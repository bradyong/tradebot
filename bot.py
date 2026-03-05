import os
import time
import hmac
import math
import hashlib
import traceback
from urllib.parse import urlencode
from decimal import Decimal, ROUND_HALF_UP, getcontext
from collections import OrderedDict

import requests
from dotenv import load_dotenv
from flask import Flask, request, jsonify

# Decimal precision
getcontext().prec = 28

# =========================
# ENV
# =========================
load_dotenv()

APP_HOST = os.getenv("APP_HOST", "0.0.0.0")
APP_PORT = int(os.getenv("APP_PORT", "5000"))
WEBHOOK_PASSPHRASE = os.getenv("WEBHOOK_PASSPHRASE", "1234")

BINANCE_API_KEY = os.getenv("BINANCE_API_KEY", "")
BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET", "")

BASE_URL = os.getenv("BINANCE_FAPI_BASE_URL", "https://fapi1.binance.com")

DEFAULT_SYMBOL = os.getenv("DEFAULT_SYMBOL", "BTCUSDT")
DEFAULT_LEVERAGE = int(os.getenv("DEFAULT_LEVERAGE", "10"))

TP_PCT = Decimal(os.getenv("TP_PCT", "1.5"))
SL_PCT = Decimal(os.getenv("SL_PCT", "1.0"))

RECV_WINDOW = int(os.getenv("RECV_WINDOW", "5000"))
TIME_SYNC_REFRESH_SEC = int(os.getenv("TIME_SYNC_REFRESH_SEC", "30"))
EXCHANGEINFO_REFRESH_SEC = int(os.getenv("EXCHANGEINFO_REFRESH_SEC", "3600"))

FALLBACK_MIN_NOTIONAL = Decimal(os.getenv("FALLBACK_MIN_NOTIONAL", "100"))
MIN_NOTIONAL_BUFFER = Decimal(os.getenv("MIN_NOTIONAL_BUFFER", "1.02"))

ALLOW_REVERSE = os.getenv("ALLOW_REVERSE", "true").lower() == "true"
CANCEL_ORDERS_BEFORE_NEW_ENTRY = os.getenv("CANCEL_ORDERS_BEFORE_NEW_ENTRY", "true").lower() == "true"
AUTO_CANCEL_ORDERS_ON_CLOSE = os.getenv("AUTO_CANCEL_ORDERS_ON_CLOSE", "true").lower() == "true"

# ---- 안정화 옵션 ----
# 같은 action/symbol이 COOLDOWN_SEC 이내에 연속으로 오면 무시
COOLDOWN_SEC = int(os.getenv("COOLDOWN_SEC", "75"))

# TradingView에서 signal_id를 같이 보내면 완전 idempotent (같은 id는 1회만 처리)
ENABLE_SIGNAL_ID = os.getenv("ENABLE_SIGNAL_ID", "true").lower() == "true"
MAX_SIGNAL_IDS = int(os.getenv("MAX_SIGNAL_IDS", "500"))
SIGNAL_ID_TTL_SEC = int(os.getenv("SIGNAL_ID_TTL_SEC", "3600"))

# TP/SL 둘 중 하나라도 실패하면:
# 1) 방금 생성된 algo 주문 전부 취소
# 2) (선택) 포지션도 즉시 청산해서 '알몸 포지션' 방지
STRICT_BRACKET = os.getenv("STRICT_BRACKET", "true").lower() == "true"
CLOSE_ON_BRACKET_FAIL = os.getenv("CLOSE_ON_BRACKET_FAIL", "true").lower() == "true"

# =========================
# Utils (Decimal Precision FIX)
# =========================
def now_ms() -> int:
    return int(time.time() * 1000)

def now_s() -> int:
    return int(time.time())

def step_decimals(step: Decimal) -> int:
    exp = step.as_tuple().exponent
    return 0 if exp >= 0 else -exp

def quantize_to_step(value: Decimal, step: Decimal) -> Decimal:
    if step == 0:
        return value
    units = (value / step).to_integral_value(rounding=ROUND_HALF_UP)
    return (units * step)

def floor_to_step(value: Decimal, step: Decimal) -> Decimal:
    if step == 0:
        return value
    units = (value / step).to_integral_value(rounding="ROUND_FLOOR")
    return (units * step)

def to_step_str(value: Decimal, step: Decimal) -> str:
    q = quantize_to_step(value, step)
    d = step_decimals(step)
    return f"{q:.{d}f}"

def to_floor_str(value: Decimal, step: Decimal) -> str:
    q = floor_to_step(value, step)
    d = step_decimals(step)
    return f"{q:.{d}f}"

# =========================
# In-memory anti-dup (cooldown + signal_id)
# =========================
_last_action_ts = {}  # key: (symbol, action) -> unix sec
_seen_signal_ids = OrderedDict()  # signal_id -> seen_at (unix sec)

def cleanup_seen_ids():
    if not _seen_signal_ids:
        return
    cutoff = now_s() - SIGNAL_ID_TTL_SEC
    # 오래된 것부터 제거
    while _seen_signal_ids:
        first_key = next(iter(_seen_signal_ids))
        if _seen_signal_ids[first_key] >= cutoff:
            break
        _seen_signal_ids.popitem(last=False)
    # 개수 제한
    while len(_seen_signal_ids) > MAX_SIGNAL_IDS:
        _seen_signal_ids.popitem(last=False)

def is_duplicate(symbol: str, action: str, signal_id: str | None):
    # 1) signal_id 기반 완전 중복 방지
    if ENABLE_SIGNAL_ID and signal_id:
        cleanup_seen_ids()
        if signal_id in _seen_signal_ids:
            return True, {"reason": "duplicate_signal_id", "signal_id": signal_id}
        _seen_signal_ids[signal_id] = now_s()

    # 2) 쿨다운 기반 중복 방지
    key = (symbol, action)
    last = _last_action_ts.get(key, 0)
    if last and (now_s() - last) < COOLDOWN_SEC:
        return True, {"reason": "cooldown", "cooldown_sec": COOLDOWN_SEC, "last_ts": last}
    _last_action_ts[key] = now_s()
    return False, None

# =========================
# Binance REST Client
# =========================
class BinanceFuturesClient:
    def __init__(self, base_url: str, api_key: str, api_secret: str, recv_window: int = 5000):
        self.base_url = base_url.rstrip("/")
        self.api_key = api_key
        self.api_secret = api_secret.encode("utf-8")
        self.recv_window = recv_window

        self._time_offset_ms = 0
        self._last_time_sync = 0

        self._exchangeinfo = None
        self._symbol_filters = {}
        self._last_exchangeinfo_fetch = 0

        self.session = requests.Session()
        self.session.headers.update({"X-MBX-APIKEY": self.api_key})

    # ---- -1021 FIX (time sync) ----
    def sync_time(self, force: bool = False):
        if not force and (now_ms() - self._last_time_sync) < (TIME_SYNC_REFRESH_SEC * 1000):
            return
        r = requests.get(self.base_url + "/fapi/v1/time", timeout=10)
        r.raise_for_status()
        server_time = r.json()["serverTime"]
        local = now_ms()
        self._time_offset_ms = server_time - local
        self._last_time_sync = now_ms()

    def _signed_request(self, method: str, path: str, params: dict | None = None):
        self.sync_time()
        if params is None:
            params = {}

        params["recvWindow"] = self.recv_window
        params["timestamp"] = now_ms() + self._time_offset_ms

        qs = urlencode(params, doseq=True)
        sig = hmac.new(self.api_secret, qs.encode("utf-8"), hashlib.sha256).hexdigest()
        url = f"{self.base_url}{path}?{qs}&signature={sig}"
        return self.session.request(method, url, timeout=20)

    def _public_request(self, method: str, path: str, params: dict | None = None):
        url = self.base_url + path
        return requests.request(method, url, params=params, timeout=15)

    # ---- filters ----
    def load_exchangeinfo(self, force: bool = False):
        if (not force and self._exchangeinfo is not None
                and (now_ms() - self._last_exchangeinfo_fetch) < (EXCHANGEINFO_REFRESH_SEC * 1000)):
            return
        r = self._public_request("GET", "/fapi/v1/exchangeInfo")
        r.raise_for_status()
        data = r.json()
        self._exchangeinfo = data
        self._symbol_filters = {}
        for s in data.get("symbols", []):
            sym = s.get("symbol")
            if not sym:
                continue
            self._symbol_filters[sym] = {f["filterType"]: f for f in s.get("filters", [])}
        self._last_exchangeinfo_fetch = now_ms()

    def get_filters(self, symbol: str):
        self.load_exchangeinfo()
        if symbol not in self._symbol_filters:
            raise ValueError(f"Symbol not found: {symbol}")

        f = self._symbol_filters[symbol]
        lot = f.get("LOT_SIZE", {})
        price_f = f.get("PRICE_FILTER", {})

        step_size = Decimal(lot.get("stepSize", "0"))
        min_qty = Decimal(lot.get("minQty", "0"))
        tick_size = Decimal(price_f.get("tickSize", "0"))

        min_notional = Decimal("0")
        mn = f.get("MIN_NOTIONAL")
        if mn:
            for k in ("notional", "minNotional"):
                if k in mn:
                    try:
                        min_notional = Decimal(str(mn[k]))
                    except Exception:
                        min_notional = Decimal("0")

        return {
            "stepSize": step_size,
            "minQty": min_qty,
            "tickSize": tick_size,
            "minNotional": min_notional
        }

    # ---- market price ----
    def get_mark_price(self, symbol: str) -> Decimal:
        r = self._public_request("GET", "/fapi/v1/premiumIndex", {"symbol": symbol})
        r.raise_for_status()
        return Decimal(str(r.json()["markPrice"]))

    # ---- position ----
    def get_position(self, symbol: str):
        r = self._signed_request("GET", "/fapi/v2/positionRisk", {})
        data = r.json()
        if r.status_code != 200:
            return None, data
        for p in data:
            if p.get("symbol") == symbol:
                return {
                    "positionAmt": Decimal(str(p.get("positionAmt", "0"))),
                    "entryPrice": Decimal(str(p.get("entryPrice", "0")))
                }, None
        return {"positionAmt": Decimal("0"), "entryPrice": Decimal("0")}, None

    # ---- cancels ----
    def cancel_open_orders(self, symbol: str):
        r = self._signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol})
        return r.status_code == 200, r.json()

    def cancel_open_algo_orders(self, symbol: str):
        r = self._signed_request("DELETE", "/fapi/v1/algoOpenOrders", {"symbol": symbol})
        return r.status_code == 200, r.json()

    # ---- leverage ----
    def set_leverage(self, symbol: str, leverage: int):
        r = self._signed_request("POST", "/fapi/v1/leverage", {"symbol": symbol, "leverage": leverage})
        return r.status_code == 200, r.json()

    # ---- normal market order ----
    def place_market(self, symbol: str, side: str, quantity: Decimal, step_size: Decimal, reduce_only: bool = False):
        qty_str = to_step_str(quantity, step_size)
        params = {
            "symbol": symbol,
            "side": side,
            "type": "MARKET",
            "quantity": qty_str,
            "reduceOnly": "true" if reduce_only else "false"
        }
        r = self._signed_request("POST", "/fapi/v1/order", params)
        return r.status_code == 200, r.json(), {"quantity_sent": qty_str}

    # ---- algo conditional (TP/SL) ----
    def place_algo_conditional(self, symbol: str, side: str, order_type: str,
                               trigger_price: Decimal, quantity: Decimal,
                               tick_size: Decimal, step_size: Decimal):
        trigger_str = to_step_str(trigger_price, tick_size)
        qty_str = to_step_str(quantity, step_size)

        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,
            "triggerPrice": trigger_str,
            "quantity": qty_str,
            "reduceOnly": "true",
            "workingType": "MARK_PRICE",
            "priceProtect": "TRUE"
        }
        r = self._signed_request("POST", "/fapi/v1/algoOrder", params)
        return r.status_code == 200, r.json(), {"triggerPrice_sent": trigger_str, "quantity_sent": qty_str}

# =========================
# Trading logic
# =========================
client = BinanceFuturesClient(BASE_URL, BINANCE_API_KEY, BINANCE_API_SECRET, RECV_WINDOW)

def cancel_everything(symbol: str):
    ok1, res1 = client.cancel_open_orders(symbol)
    ok2, res2 = client.cancel_open_algo_orders(symbol)
    return {"open": {"ok": ok1, "response": res1}, "algo": {"ok": ok2, "response": res2}}

def compute_qty_from_usdt(symbol: str, order_usdt: Decimal):
    filters = client.get_filters(symbol)
    step = filters["stepSize"]
    min_qty = filters["minQty"]
    min_notional = filters["minNotional"] if filters["minNotional"] > 0 else FALLBACK_MIN_NOTIONAL

    mark = client.get_mark_price(symbol)
    target_notional = max(order_usdt, min_notional * MIN_NOTIONAL_BUFFER)

    raw_qty = target_notional / mark
    qty = floor_to_step(raw_qty, step)
    if qty < min_qty:
        qty = min_qty
    qty = floor_to_step(qty, step)

    meta = {
        "markPrice": str(mark),
        "requestedUSDT": str(order_usdt),
        "targetNotional": str(target_notional),
        "rawQty": str(raw_qty),
        "finalQty": str(qty),
        "filters": {
            "stepSize": str(filters["stepSize"]),
            "minQty": str(filters["minQty"]),
            "tickSize": str(filters["tickSize"]),
            "minNotional": str(filters["minNotional"]),
        }
    }
    return qty, filters, meta

def get_entry_price_after_fill(symbol: str, wait_sec: float = 3.0):
    end = time.time() + wait_sec
    last = None
    while time.time() < end:
        pos, err = client.get_position(symbol)
        if err is None:
            last = pos
            if abs(pos["positionAmt"]) > 0 and pos["entryPrice"] > 0:
                return pos["entryPrice"], pos
        time.sleep(0.2)
    return (last["entryPrice"] if last else Decimal("0")), (last if last else {"positionAmt": Decimal("0"), "entryPrice": Decimal("0")})

def handle_close(symbol: str):
    pos, err = client.get_position(symbol)
    if err is not None:
        return False, {"error": "get_position failed", "details": err}

    cancels = cancel_everything(symbol) if AUTO_CANCEL_ORDERS_ON_CLOSE else {"skipped": True}

    amt = pos["positionAmt"]
    if amt == 0:
        return True, {"message": "no position", "cancels": cancels}

    f = client.get_filters(symbol)
    step = f["stepSize"]
    qty = abs(amt)
    side = "SELL" if amt > 0 else "BUY"

    ok, res, sent = client.place_market(symbol, side, qty, step, reduce_only=True)
    return ok, {"cancels": cancels, "close": {"ok": ok, "sent": sent, "response": res}}

def place_bracket(symbol: str, direction: str, entry_price: Decimal, qty: Decimal, tick: Decimal, step: Decimal):
    if direction == "LONG":
        tp = entry_price * (Decimal("1") + TP_PCT / Decimal("100"))
        sl = entry_price * (Decimal("1") - SL_PCT / Decimal("100"))
        exit_side = "SELL"
    else:
        tp = entry_price * (Decimal("1") - TP_PCT / Decimal("100"))
        sl = entry_price * (Decimal("1") + SL_PCT / Decimal("100"))
        exit_side = "BUY"

    ok_tp, res_tp, sent_tp = client.place_algo_conditional(symbol, exit_side, "TAKE_PROFIT_MARKET", tp, qty, tick, step)
    ok_sl, res_sl, sent_sl = client.place_algo_conditional(symbol, exit_side, "STOP_MARKET", sl, qty, tick, step)

    both_ok = ok_tp and ok_sl

    result = {
        "tp": {"ok": ok_tp, "sent": sent_tp, "response": res_tp},
        "sl": {"ok": ok_sl, "sent": sent_sl, "response": res_sl},
        "both_ok": both_ok
    }
    return both_ok, result

def handle_entry(symbol: str, direction: str, order_usdt: Decimal, leverage: int):
    client.sync_time(force=True)

    ok_lev, res_lev = client.set_leverage(symbol, leverage)
    if not ok_lev:
        return False, {"error": "set_leverage failed", "binance": res_lev}

    pos, err = client.get_position(symbol)
    if err is not None:
        return False, {"error": "get_position failed", "binance": err}

    amt = pos["positionAmt"]
    want_long = (direction == "LONG")

    # 같은 방향 포지션이면 무시(중복 포지션 방지)
    if amt != 0:
        already_long = amt > 0
        if (already_long and want_long) or ((not already_long) and (not want_long)):
            return True, {"message": "already in same direction; ignored",
                          "position": {"positionAmt": str(amt), "entryPrice": str(pos["entryPrice"])}}

        # 반대 포지션이면 (허용 시) 먼저 닫고 진행
        if not ALLOW_REVERSE:
            return False, {"error": "opposite position exists; reverse disabled",
                           "position": {"positionAmt": str(amt), "entryPrice": str(pos["entryPrice"])}}

        ok_close, res_close = handle_close(symbol)
        if not ok_close:
            return False, {"error": "reverse close failed", "details": res_close}

    # 새 진입 전 주문 정리(남은 TP/SL 등)
    cancels_before = cancel_everything(symbol) if CANCEL_ORDERS_BEFORE_NEW_ENTRY else {"skipped": True}

    qty, filters, meta = compute_qty_from_usdt(symbol, order_usdt)
    step = filters["stepSize"]
    tick = filters["tickSize"]

    side = "BUY" if want_long else "SELL"
    ok_entry, res_entry, sent_entry = client.place_market(symbol, side, qty, step, reduce_only=False)
    if not ok_entry:
        return False, {"error": "entry failed", "qtyMeta": meta, "sent": sent_entry, "binance": res_entry}

    entry_price, pos2 = get_entry_price_after_fill(symbol)

    both_ok, bracket = place_bracket(symbol, direction, entry_price, qty, tick, step)

    # ✅ 비정상 복구: TP/SL 한쪽만 생기면 전부 취소 + (선택) 포지션 청산
    recovery = None
    if STRICT_BRACKET and not both_ok:
        recovery = {"note": "bracket_failed_recovery_started"}
        recovery["cancels"] = cancel_everything(symbol)

        if CLOSE_ON_BRACKET_FAIL:
            ok_close, close_res = handle_close(symbol)
            recovery["close_on_fail"] = {"ok": ok_close, "result": close_res}

        return False, {
            "error": "bracket_failed",
            "message": "TP/SL 중 하나라도 실패해서 안전을 위해 복구(주문취소/포지션청산) 수행",
            "recovery": recovery,
            "cancelsBefore": cancels_before,
            "leverage": {"ok": ok_lev, "response": res_lev},
            "qtyMeta": meta,
            "entry": {"ok": ok_entry, "sent": sent_entry, "response": res_entry},
            "positionAfter": {"positionAmt": str(pos2["positionAmt"]), "entryPrice": str(pos2["entryPrice"])},
            "entryPriceUsed": str(entry_price),
            "bracket": bracket
        }

    return True, {
        "cancelsBefore": cancels_before,
        "leverage": {"ok": ok_lev, "response": res_lev},
        "qtyMeta": meta,
        "entry": {"ok": ok_entry, "sent": sent_entry, "response": res_entry},
        "positionAfter": {"positionAmt": str(pos2["positionAmt"]), "entryPrice": str(pos2["entryPrice"])},
        "entryPriceUsed": str(entry_price),
        "bracket": bracket
    }

# =========================
# Flask
# =========================
app = Flask(__name__)

@app.get("/")
def health():
    return jsonify({
        "ok": True,
        "time": now_ms(),
        "cooldown_sec": COOLDOWN_SEC,
        "strict_bracket": STRICT_BRACKET,
        "close_on_bracket_fail": CLOSE_ON_BRACKET_FAIL,
        "seen_signal_ids": len(_seen_signal_ids)
    })

@app.post("/webhook")
def webhook():
    try:
        data = request.get_json(force=True, silent=False)
        if not isinstance(data, dict):
            return jsonify({"ok": False, "error": "invalid payload"}), 400

        if data.get("passphrase") != WEBHOOK_PASSPHRASE:
            return jsonify({"ok": False, "error": "bad passphrase"}), 403

        action = str(data.get("action", "")).upper().strip()
        symbol = str(data.get("symbol", DEFAULT_SYMBOL)).upper().strip()
        leverage = int(data.get("leverage", DEFAULT_LEVERAGE))
        signal_id = str(data.get("signal_id", "")).strip() or None

        if symbol != "BTCUSDT":
            return jsonify({"ok": False, "error": "only BTCUSDT allowed"}), 400

        if not BINANCE_API_KEY or not BINANCE_API_SECRET:
            return jsonify({"ok": False, "error": "BINANCE_API_KEY/SECRET missing (.env not loaded)"}), 400

        if action not in ("LONG", "SHORT", "CLOSE"):
            return jsonify({"ok": False, "error": "unsupported action"}), 400

        dup, dup_info = is_duplicate(symbol, action, signal_id)
        if dup:
            return jsonify({"ok": True, "result": {"message": "ignored duplicate", "dup": dup_info}}), 200

        if action in ("LONG", "SHORT"):
            order_usdt = Decimal(str(data.get("order_usdt", 0)))
            if order_usdt <= 0:
                return jsonify({"ok": False, "error": "order_usdt must be > 0"}), 400

            ok, result = handle_entry(symbol, action, order_usdt, leverage)
            return jsonify({"ok": ok, "result": result}), (200 if ok else 400)

        # CLOSE
        ok, result = handle_close(symbol)
        return jsonify({"ok": ok, "result": result}), (200 if ok else 400)

    except Exception as e:
        tb = traceback.format_exc()
        print(tb)
        return jsonify({"ok": False, "error": str(e), "traceback": tb}), 500


if __name__ == "__main__":
    if not BINANCE_API_KEY or not BINANCE_API_SECRET:
        print("WARNING: BINANCE_API_KEY / BINANCE_API_SECRET not set.")
    print(f"Running on http://{APP_HOST}:{APP_PORT}")

    app.run(host=APP_HOST, port=APP_PORT)
