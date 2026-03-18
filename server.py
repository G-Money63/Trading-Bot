"""
XRP Semi-Auto Grid Bot — Cloud Server
======================================
Grid Bot watches price levels every 15s and queues PENDING signals.
The dashboard shows each signal with CONFIRM / SKIP buttons.
Only confirmed signals execute — paper or live via Coinbase Advanced.

Endpoints:
  GET  /                       → dashboard
  GET  /api/latest             → market snapshot
  GET  /api/history            → price history
  GET  /api/bot/state          → full bot + grid state
  POST /api/bot/config         → save grid config
  POST /api/bot/start          → start watching
  POST /api/bot/stop           → stop watching
  POST /api/bot/confirm        → confirm a pending signal → execute
  POST /api/bot/skip           → skip a pending signal
  GET  /health
"""

import asyncio, json, os, statistics, threading, time, logging, urllib.request, uuid, hmac, hashlib, base64, struct
from collections import deque
from datetime import datetime, timezone
from http.server import HTTPServer, BaseHTTPRequestHandler
import websockets

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger(__name__)

# ─── Config ───────────────────────────────────────────────────────────────────
PORT            = int(os.environ.get("PORT", 8080))
BUILD_ID        = os.environ.get("BUILD_ID", str(int(time.time())))
VAPID_PUBLIC_KEY = os.environ.get("VAPID_PUBLIC", "")  # unique per deploy
POLL_INTERVAL   = 15
HISTORY_MAXLEN  = 200
OBI_THRESHOLD   = 0.15
OBI_SMOOTH_N    = 4
DEPTH_LEVELS    = 20
# Coinbase Advanced public order book — works from US cloud servers, no auth needed
COINBASE_BOOK   = "https://api.coinbase.com/api/v3/brokerage/market/product_book?product_id=XRP-USD&limit=20"
# Kraken as backup — also works from US servers
KRAKEN_REST     = "https://api.kraken.com/0/public/Depth?pair=XRPUSD&count=20"
CB_API_KEY      = os.environ.get("CB_API_KEY", "")
# Handle \n stored as literal text in env vars
_raw_secret     = os.environ.get("CB_API_SECRET", "")
CB_API_SECRET   = _raw_secret.replace("\\n", "\n") if "\\n" in _raw_secret else _raw_secret
CB_BASE_URL     = "https://api.coinbase.com"
PRODUCT_ID      = "XRP-USD"
VAPID_PRIVATE   = os.environ.get("VAPID_PRIVATE", "")
VAPID_PUBLIC    = os.environ.get("VAPID_PUBLIC", "")
VAPID_EMAIL     = os.environ.get("VAPID_EMAIL", "mailto:admin@example.com")
push_subscriptions = []  # Store push subscriptions in memory

# ─── Market State ─────────────────────────────────────────────────────────────
history         = deque(maxlen=HISTORY_MAXLEN)
price_history     = deque(maxlen=20)   # For token momentum calculation
sentiment_history = deque(maxlen=20)   # For sentiment smoothing (5 min rolling avg)
bid_vol_history   = deque(maxlen=20)   # For volume trend calculation
latest_snapshot = {}
state_lock      = threading.Lock()

# ─── Scaler ───────────────────────────────────────────────────────────────────
class MinMaxScaler:
    def __init__(self, w=40):
        self.buf = deque(maxlen=w)
    def fit_transform(self, v):
        self.buf.append(v)
        lo, hi = min(self.buf), max(self.buf)
        return 0.5 if hi == lo else (v - lo) / (hi - lo)

obi_scaler    = MinMaxScaler()
spread_scaler = MinMaxScaler()
depth_scaler  = MinMaxScaler()

# ─── Grid Bot State ───────────────────────────────────────────────────────────
grid = {
    "running":       False,
    "mode":          "paper",       # "paper" | "live"
    "config": {
        "upper":         float(os.environ.get("GRID_UPPER", 1.60)),
        "lower":         float(os.environ.get("GRID_LOWER", 1.20)),
        "levels":        int(os.environ.get("GRID_LEVELS", 10)),
        "amount_usd":    float(os.environ.get("GRID_AMOUNT", 50)),
        "order_type":    os.environ.get("GRID_ORDER_TYPE", "usd"),  # "usd" or "xrp"
        "signal_direction": "both",  # "both", "buy", "sell"
        "amount_xrp":    float(os.environ.get("GRID_AMOUNT_XRP", 35)),
        "stop_loss_pct": 5.0,
        "take_profit_pct": 15.0,
    },
    # Derived grid lines — recomputed when config changes
    "grid_lines":    [],            # list of price levels
    # Which levels have open buy/sell orders (level_index: order_dict)
    "buy_orders":    {},
    "sell_orders":   {},
    # Pending signals waiting for user confirm/skip
    "pending":       [],            # list of signal dicts
    # Confirmed executed trades
    "trade_log":     deque(maxlen=200),
    # Portfolio
    "portfolio": {
        "cash_usd":        float(os.environ.get("PORTFOLIO_CASH", 1000.0)),
        "xrp_held":        float(os.environ.get("PORTFOLIO_XRP", 0.0)),
        "avg_entry":       float(os.environ.get("PORTFOLIO_AVG", 0.0)),
        "realized_pnl":    0.0,
        "open_orders":     [],
        "last_sell_price": float(os.environ.get("PORTFOLIO_LAST_SELL", 0.0)),
        "last_buy_price":  float(os.environ.get("PORTFOLIO_LAST_BUY", 0.0)),
    },
    "last_checked_band": -1,
}
grid_lock = threading.Lock()

# ─── Grid Math ────────────────────────────────────────────────────────────────
def build_grid_lines(upper, lower, levels):
    """Return evenly spaced price levels including upper and lower bounds."""
    if upper <= lower or levels < 2:
        return []
    step = (upper - lower) / levels
    return [round(lower + i * step, 6) for i in range(levels + 1)]

def recompute_grid():
    # NOTE: caller must hold grid_lock before calling this
    cfg = grid["config"]
    lines = build_grid_lines(cfg["upper"], cfg["lower"], cfg["levels"])
    grid["grid_lines"] = lines
    grid["buy_orders"]  = {}
    grid["sell_orders"] = {}
    grid["last_checked_band"] = -1
    log.info(f"Grid recomputed: {len(lines)} lines  ${cfg['lower']}–${cfg['upper']}")

# ─── Signal Builder ───────────────────────────────────────────────────────────
def make_signal(side, price, level_idx, level_low, level_high, snap):
    order_type = grid["config"].get("order_type", "usd")
    if order_type == "xrp":
        xrp_qty = grid["config"].get("amount_xrp", 35)
        amount  = round(xrp_qty * price, 2)
    else:
        amount  = grid["config"]["amount_usd"]
        xrp_qty = round(amount / price, 4)
    obi   = snap.get("obi", 0)
    bull  = snap.get("bull_score", 0.5)
    # Signal confidence based on OBI direction matching trade side
    if side == "BUY":
        confidence = "HIGH" if obi > 0.1 and bull > 0.55 else "MEDIUM" if obi > -0.05 else "LOW"
        conf_color = "#00ff88" if confidence == "HIGH" else "#ffcc00" if confidence == "MEDIUM" else "#ff8800"
    else:
        confidence = "HIGH" if obi < -0.1 and bull < 0.45 else "MEDIUM" if obi < 0.05 else "LOW"
        conf_color = "#00ff88" if confidence == "HIGH" else "#ffcc00" if confidence == "MEDIUM" else "#ff8800"

    stop_price   = round(price * (1 - grid["config"]["stop_loss_pct"] / 100), 6)
    target_price = round(price * (1 + grid["config"]["take_profit_pct"] / 100), 6)

    # Position context
    pf = grid["portfolio"]
    avg_entry  = pf.get("avg_entry", 0)
    last_sell  = pf.get("last_sell_price", 0)
    last_buy   = pf.get("last_buy_price", 0)
    open_orders = pf.get("open_orders", [])
    open_xrp   = round(sum(o["xrp_qty"] for o in open_orders), 4)

    if side == "SELL" and avg_entry > 0:
        profit_per_xrp = round(price - avg_entry, 5)
        profit_pct     = round((price - avg_entry) / avg_entry * 100, 2)
        est_profit     = round(profit_per_xrp * xrp_qty, 2)
        is_profitable  = price > avg_entry
        profit_status  = "PROFITABLE" if is_profitable else "BELOW AVG COST"
        profit_color   = "#00875a" if is_profitable else "#dc2626"
    elif side == "BUY" and last_sell > 0:
        discount       = round(last_sell - price, 5)
        discount_pct   = round(discount / last_sell * 100, 2)
        est_profit     = round(discount * xrp_qty, 2)
        is_profitable  = price < last_sell
        profit_status  = "BELOW LAST SELL" if is_profitable else "ABOVE LAST SELL"
        profit_color   = "#00875a" if is_profitable else "#dc2626"
        profit_per_xrp = discount
        profit_pct     = discount_pct
    else:
        profit_per_xrp = 0; profit_pct = 0; est_profit = 0
        is_profitable  = True; profit_status = "FIRST TRADE"; profit_color = "#0033AD"

    return {
        "id":              str(uuid.uuid4())[:8],
        "side":            side,
        "price":           round(price, 6),
        "xrp_qty":         xrp_qty,
        "usd_amount":      round(amount, 2),
        "level_idx":       level_idx,
        "level_low":       round(level_low, 6),
        "level_high":      round(level_high, 6),
        "level_label":     f"Level {level_idx + 1} of {grid['config']['levels']}",
        "stop_price":      stop_price,
        "target_price":    target_price,
        "confidence":      confidence,
        "conf_color":      conf_color,
        "obi":             round(obi, 4),
        "bull_score":      round(bull, 3),
        "signal":          snap.get("signal", "—"),
        "signal_color":    snap.get("signal_color", "#ffcc00"),
        "ts":              datetime.now(timezone.utc).isoformat(),
        "status":          "pending",
        "mode":            grid["mode"],
        "avg_entry":       round(avg_entry, 5),
        "last_sell_price": round(last_sell, 5),
        "last_buy_price":  round(last_buy, 5),
        "profit_per_xrp":  round(profit_per_xrp, 5),
        "profit_pct":      profit_pct,
        "est_profit":      est_profit,
        "is_profitable":   is_profitable,
        "profit_status":   profit_status,
        "profit_color":    profit_color,
        "open_orders":     open_orders,
        "open_xrp":        open_xrp,
        "open_order_count": len(open_orders),
    }

# ─── Grid Engine ──────────────────────────────────────────────────────────────
def run_grid_tick(snap):
    if not grid["running"]:
        return
    price = snap.get("mid_price", 0)
    if not price:
        return

    with grid_lock:
        lines = grid["grid_lines"]
        if len(lines) < 2:
            return
        cfg   = grid["config"]
        lo    = cfg["lower"]
        hi    = cfg["upper"]

        # Check stop loss
        pf = grid["portfolio"]
        if pf["xrp_held"] > 0 and pf["avg_entry"] > 0:
            drop = (pf["avg_entry"] - price) / pf["avg_entry"] * 100
            if drop >= cfg["stop_loss_pct"]:
                sig = make_signal("SELL", price, -1, price, price, snap)
                sig["level_label"] = f"🛑 STOP LOSS ({drop:.1f}% drop)"
                sig["confidence"]  = "STOP LOSS"
                sig["conf_color"]  = "#ff3355"
                if not any(p["id"] == sig["id"] for p in grid["pending"]):
                    grid["pending"].append(sig)
                    log.info(f"STOP LOSS signal queued at ${price:.5f}")
                return

        # Out of range — no grid action
        if price < lo or price > hi:
            return

        # Find which band (gap between two grid lines) the price is in
        band = -1
        for i in range(len(lines) - 1):
            if lines[i] <= price < lines[i + 1]:
                band = i
                break
        if band < 0:
            return

        # Only generate a new signal if we've moved to a different band
        if band == grid["last_checked_band"]:
            return

        prev_band = grid["last_checked_band"]
        grid["last_checked_band"] = band

        # Skip on first tick
        if prev_band < 0:
            return

        # Determine direction of price movement
        moved_down = band < prev_band
        moved_up   = band > prev_band

        # Keep pending signals alive — only remove truly stale ones (> 5 min old)
        import time as _t
        now_ts = _t.time()
        grid["pending"] = [p for p in grid["pending"] 
                          if p["status"] != "pending" or 
                          (now_ts - _t.mktime(_t.strptime(p["ts"][:19], "%Y-%m-%dT%H:%M:%S"))) < 300]
        already_pending_sides = {p["side"] for p in grid["pending"] if p["status"] == "pending"}
        direction = cfg.get("signal_direction","both")
        already_bought  = band in grid["buy_orders"]
        already_sold    = band in grid["sell_orders"]

        # Price dropped into this band → BUY opportunity at the lower line
        if moved_down and not already_bought and "BUY" not in already_pending_sides and direction in ("both","buy"):
            buy_price = lines[band]         # bottom of this band
            sig = make_signal("BUY", buy_price, band, lines[band], lines[band+1], snap)
            grid["pending"].append(sig)
            try:
                send_push_notification(
                    f"🟢 BUY Signal @ ${sig['price']:.4f}",
                    f"{sig.get('level_label','Grid')} · {sig.get('conviction','—')} conviction · {grid['mode'].upper()} MODE",
                    {"signal_id": sig["id"], "side": sig["side"]}
                )
            except: pass
            log.info(f"BUY signal queued: level {band+1}  @${buy_price:.5f}  conf={sig['confidence']}")

        # Price rose into this band → SELL opportunity at the upper line
        if moved_up and pf["xrp_held"] > 0 and not already_sold and "SELL" not in already_pending_sides and direction in ("both","sell"):
            sell_price = lines[band + 1]    # top of this band
            sig = make_signal("SELL", sell_price, band, lines[band], lines[band+1], snap)
            grid["pending"].append(sig)
            try:
                send_push_notification(
                    f"🔴 SELL Signal @ ${sig['price']:.4f}",
                    f"{sig.get('level_label','Grid')} · {sig.get('conviction','—')} conviction · {grid['mode'].upper()} MODE",
                    {"signal_id": sig["id"], "side": sig["side"]}
                )
            except: pass
            log.info(f"SELL signal queued: level {band+1}  @${sell_price:.5f}  conf={sig['confidence']}")

# ─── Trade Execution ──────────────────────────────────────────────────────────
def execute_paper(sig):
    with grid_lock:
        pf    = grid["portfolio"]
        side  = sig["side"]
        price = sig["price"]
        if "open_orders" not in pf: pf["open_orders"] = []
        if side == "BUY":
            order_type = grid["config"].get("order_type", "usd")
            if order_type == "xrp":
                qty = sig["xrp_qty"]
                usd = min(qty * price, pf["cash_usd"])
                if usd < 1:
                    return False, "Insufficient cash"
                qty = usd / price  # Adjust if cash limited
            else:
                usd = min(sig["usd_amount"], pf["cash_usd"])
                if usd < 1:
                    return False, "Insufficient cash"
                qty = usd / price
            total_xrp = pf["xrp_held"] + qty
            pf["avg_entry"] = (pf["avg_entry"] * pf["xrp_held"] + price * qty) / total_xrp if total_xrp else price
            pf["xrp_held"] += qty
            pf["cash_usd"] -= usd
            pf["last_buy_price"] = price
            sig["xrp_qty"] = round(qty, 4)
            sig["usd_amount"] = round(usd, 2)
            grid["buy_orders"][sig["level_idx"]] = sig
            # Track open order
            pf["open_orders"].append({
                "level_idx":   sig["level_idx"],
                "level_label": sig.get("level_label", f"Level {sig['level_idx']+1}"),
                "price":       price,
                "xrp_qty":     round(qty, 4),
                "usd_amount":  round(usd, 2),
                "ts":          datetime.now(timezone.utc).isoformat(),
                "side":        "BUY"
            })
        else:
            qty = min(sig["xrp_qty"], pf["xrp_held"])
            if qty < 0.001:
                return False, "Insufficient XRP"
            usd = qty * price
            cost = qty * pf["avg_entry"]
            pnl  = usd - cost
            pf["xrp_held"]     -= qty
            pf["cash_usd"]     += usd
            pf["realized_pnl"] += pnl
            pf["last_sell_price"] = price
            # Remove matched buy orders FIFO
            remaining = qty
            new_orders = []
            for o in sorted(pf["open_orders"], key=lambda x: x["ts"]):
                if remaining <= 0: new_orders.append(o)
                elif o["xrp_qty"] <= remaining: remaining -= o["xrp_qty"]
                else: o["xrp_qty"] = round(o["xrp_qty"]-remaining,4); remaining=0; new_orders.append(o)
            pf["open_orders"] = new_orders
            if pf["xrp_held"] < 0.001:
                pf["avg_entry"] = 0; pf["open_orders"] = []
            sig["usd_amount"] = round(usd, 2)
            sig["pnl"]        = round(pnl, 4)
            grid["sell_orders"][sig["level_idx"]] = sig
        sig["status"]    = "executed"
        sig["exec_ts"]   = datetime.now(timezone.utc).isoformat()
        grid["trade_log"].appendleft(dict(sig))
        log.info(f"[PAPER {side}] ${price:.5f} × {sig['xrp_qty']:.4f} XRP  [{sig['level_label']}]")
        return True, "ok"

def send_push_notification(title, body_text, data=None):
    """Send Web Push notification to all subscribers."""
    if not push_subscriptions or not VAPID_PRIVATE:
        return
    try:
        from pywebpush import webpush, WebPushException
        for sub in push_subscriptions[:]:
            try:
                webpush(
                    subscription_info=sub,
                    data=json.dumps({"title": title, "body": body_text, "data": data or {}}),
                    vapid_private_key=VAPID_PRIVATE,
                    vapid_claims={"sub": VAPID_EMAIL}
                )
                log.info(f"Push sent: {title}")
            except WebPushException as e:
                if "410" in str(e) or "404" in str(e):
                    push_subscriptions.remove(sub)  # Remove expired subscription
                log.warning(f"Push failed: {e}")
    except ImportError:
        log.warning("pywebpush not installed - push notifications disabled")
    except Exception as e:
        log.error(f"Push error: {e}")

def _clean_pem(secret):
    """Fix PEM key stored with literal \n instead of real newlines."""
    # Cloud Run env vars store newlines as literal \n (backslash + n)
    # We need to convert them back to real newlines
    if secret.count('\n') > 3:
        # Already has real newlines
        return secret
    # Has literal \n - replace with real newlines
    cleaned = secret.replace('\\n', '\n')
    if cleaned.count('\n') > 3:
        return cleaned
    # Try replacing literal backslash-n
    cleaned = ''
    i = 0
    while i < len(secret):
        if secret[i] == '\\' and i+1 < len(secret) and secret[i+1] == 'n':
            cleaned += '\n'
            i += 2
        else:
            cleaned += secret[i]
            i += 1
    log.info(f"[JWT] PEM cleaned: {len(cleaned)} chars, newlines: {cleaned.count(chr(10))}")
    return cleaned

def _make_jwt(method, path):
    """Build a JWT for Coinbase CDP API keys (organizations/... format)."""
    import time as _time
    key_name   = CB_API_KEY
    key_secret = _clean_pem(CB_API_SECRET)
    log.info(f"[JWT] key_name={key_name[:30]}... secret_lines={key_secret.count(chr(10))}")
    
    # Parse PEM to get raw private key bytes
    pem = key_secret.strip()
    pem_lines = [l for l in pem.split("\n") if l and not l.startswith("-----")]
    der = base64.b64decode("".join(pem_lines))

    # Build JWT header + payload
    now = int(_time.time())
    header  = {"alg": "ES256", "kid": key_name, "nonce": str(uuid.uuid4())[:16]}
    payload = {
        "sub": key_name,
        "iss": "cdp",
        "nbf": now,
        "exp": now + 120,
        "uri": f"{method} api.coinbase.com{path}"
    }
    def b64url(data):
        if isinstance(data, dict): data = json.dumps(data, separators=(",",":")).encode()
        return base64.urlsafe_b64encode(data).rstrip(b"=").decode()

    signing_input = f"{b64url(header)}.{b64url(payload)}".encode()

    # Sign with EC private key using built-in hmac+hashlib fallback
    # Try cryptography library first, fall back to openssl subprocess
    try:
        from cryptography.hazmat.primitives.serialization import load_pem_private_key
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.backends import default_backend
        private_key = load_pem_private_key(key_secret.encode(), password=None, backend=default_backend())
        der_sig = private_key.sign(signing_input, ec.ECDSA(hashes.SHA256()))
        # Convert DER to raw r+s (64 bytes)
        from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
        r, s = decode_dss_signature(der_sig)
        signature = r.to_bytes(32, "big") + s.to_bytes(32, "big")
    except Exception as e:
        log.error(f"JWT signing failed: {e}")
        raise

    jwt_token = f"{b64url(header)}.{b64url(payload)}.{b64url(signature)}"
    log.info(f"[JWT] Token built successfully, length={len(jwt_token)}")
    return jwt_token

def execute_live(sig):
    if not CB_API_KEY or not CB_API_SECRET:
        return False, "No API keys"
    path = "/api/v3/brokerage/orders"
    order_type = grid["config"].get("order_type", "usd")
    if sig["side"] == "BUY":
        if order_type == "xrp":
            order_cfg = {"market_market_ioc": {"base_size": str(round(sig["xrp_qty"], 6))}}
        else:
            order_cfg = {"market_market_ioc": {"quote_size": str(round(sig["usd_amount"], 2))}}
    else:
        order_cfg = {"market_market_ioc": {"base_size": str(round(sig["xrp_qty"], 6))}}
    body_dict = {
        "client_order_id":     str(uuid.uuid4()),
        "product_id":          PRODUCT_ID,
        "side":                sig["side"],
        "order_configuration": order_cfg,
    }
    body_str = json.dumps(body_dict)
    try:
        log.info(f"[LIVE] Building JWT for {path}")
        jwt_token = _make_jwt("POST", path)
        log.info(f"[LIVE] JWT built, sending order to Coinbase...")
        req = urllib.request.Request(
            CB_BASE_URL + path,
            data=body_str.encode(),
            headers={
                "Authorization":  f"Bearer {jwt_token}",
                "Content-Type":   "application/json",
                "User-Agent":     "XRP-GridBot/1.0",
            },
            method="POST"
        )
        with urllib.request.urlopen(req, timeout=15) as r:
            res = json.loads(r.read())
        log.info(f"[LIVE] Coinbase raw response: {json.dumps(res)[:200]}")
        log.info(f"Coinbase response: {res}")
        if res.get("success"):
            sig["status"]      = "executed"
            sig["exec_ts"]     = datetime.now(timezone.utc).isoformat()
            sig["cb_order_id"] = res.get("order_id","")
            with grid_lock:
                pf = grid["portfolio"]
                price = sig["price"]
                qty   = sig["xrp_qty"]
                if sig["side"] == "BUY":
                    total_xrp = pf["xrp_held"] + qty
                    pf["avg_entry"]     = (pf["avg_entry"]*pf["xrp_held"] + price*qty)/total_xrp if total_xrp else price
                    pf["xrp_held"]      = round(total_xrp, 4)
                    pf["last_buy_price"] = price
                    if "open_orders" not in pf: pf["open_orders"] = []
                    pf["open_orders"].append({"level_idx":sig["level_idx"],"level_label":sig.get("level_label",""),"price":price,"xrp_qty":qty,"usd_amount":sig["usd_amount"],"ts":datetime.now(timezone.utc).isoformat(),"side":"BUY"})
                else:
                    pf["realized_pnl"] += round((price - pf["avg_entry"]) * qty, 4)
                    pf["xrp_held"]      = round(pf["xrp_held"] - qty, 4)
                    pf["last_sell_price"] = price
                    if pf["xrp_held"] < 0.001: pf["avg_entry"]=0; pf["open_orders"]=[]
                grid["trade_log"].appendleft(dict(sig))
            log.info(f"[LIVE {sig['side']}] Coinbase order {sig['cb_order_id']} ✅")
            return True, sig["cb_order_id"]
        err = res.get("error_response", res)
        log.error(f"Coinbase order FAILED: {err}")
        return False, str(err)
    except Exception as e:
        log.error(f"Coinbase order exception: {e}")
        return False, str(e)

def confirm_signal(signal_id):
    with grid_lock:
        for sig in grid["pending"]:
            if sig["id"] == signal_id and sig["status"] == "pending":
                mode = grid["mode"]
                if mode == "paper":
                    ok, msg = execute_paper(sig)
                else:
                    ok, msg = execute_live(sig)
                sig["status"] = "executed" if ok else "failed"
                sig["exec_msg"] = msg
                return ok, msg
    return False, "Signal not found"

def skip_signal(signal_id):
    with grid_lock:
        for sig in grid["pending"]:
            if sig["id"] == signal_id and sig["status"] == "pending":
                sig["status"] = "skipped"
                log.info(f"Signal {signal_id} skipped")
                return True
    return False

def pending_signals():
    with grid_lock:
        return [s for s in grid["pending"] if s["status"] == "pending"]

# ─── XRPL + Binance ───────────────────────────────────────────────────────────
def fetch_coinbase_book():
    """Fetch XRP-USD order book from Coinbase Advanced — works from US cloud."""
    try:
        req = urllib.request.Request(
            COINBASE_BOOK,
            headers={"User-Agent": "XRP-Bot/1.0", "Accept": "application/json"}
        )
        with urllib.request.urlopen(req, timeout=10) as r:
            d = json.loads(r.read())
        book = d.get("pricebook", {})
        bids = [{"price": float(b["price"]), "qty": float(b["size"])}
                for b in book.get("bids", []) if b.get("price") and b.get("size")]
        asks = [{"price": float(a["price"]), "qty": float(a["size"])}
                for a in book.get("asks", []) if a.get("price") and a.get("size")]
        if not bids or not asks:
            raise ValueError("Empty order book from Coinbase")
        return {"source": "Coinbase", "bids": bids[:DEPTH_LEVELS], "asks": asks[:DEPTH_LEVELS]}
    except Exception as e:
        log.warning(f"Coinbase book: {e}"); return None

def fetch_kraken_book():
    """Fetch XRP/USD order book from Kraken — US-friendly backup source."""
    try:
        req = urllib.request.Request(
            KRAKEN_REST,
            headers={"User-Agent": "XRP-Bot/1.0"}
        )
        with urllib.request.urlopen(req, timeout=10) as r:
            d = json.loads(r.read())
        if d.get("error"):
            raise ValueError(f"Kraken error: {d['error']}")
        result = d.get("result", {})
        pair_data = result.get("XXRPZUSD") or result.get("XRPUSD") or next(iter(result.values()), {})
        bids = [{"price": float(b[0]), "qty": float(b[1])} for b in pair_data.get("bids", [])]
        asks = [{"price": float(a[0]), "qty": float(a[1])} for a in pair_data.get("asks", [])]
        if not bids or not asks:
            raise ValueError("Empty order book from Kraken")
        return {"source": "Kraken", "bids": bids[:DEPTH_LEVELS], "asks": asks[:DEPTH_LEVELS]}
    except Exception as e:
        log.warning(f"Kraken: {e}"); return None

def compute_snapshot(books):
    bids,asks,sources=[],[],[]
    for b in books:
        if b: bids.extend(b["bids"]); asks.extend(b["asks"]); sources.append(b["source"])
    if not bids or not asks: return {}
    bids.sort(key=lambda x:x["price"],reverse=True)
    asks.sort(key=lambda x:x["price"])
    best_bid=bids[0]["price"]; best_ask=asks[0]["price"]
    mid=(best_bid+best_ask)/2; spread=best_ask-best_bid; sprd_pct=spread/mid*100
    bid_vol=sum(b["qty"] for b in bids); ask_vol=sum(a["qty"] for a in asks)
    total=bid_vol+ask_vol; obi=(bid_vol-ask_vol)/total if total else 0
    depth_tiers={}
    for pct in [0.5,1.0,2.0]:
        lo=mid*(1-pct/100); hi=mid*(1+pct/100)
        depth_tiers[f"{pct}pct"]={"bid":round(sum(b["qty"] for b in bids if b["price"]>=lo),2),
                                   "ask":round(sum(a["qty"] for a in asks if a["price"]<=hi),2)}
    def vwap(orders):
        tq=sum(o["qty"] for o in orders)
        return sum(o["price"]*o["qty"] for o in orders)/tq if tq else 0
    obi_s=obi_scaler.fit_transform(obi); sprd_s=spread_scaler.fit_transform(sprd_pct)
    d_ratio=depth_tiers["1.0pct"]["bid"]/max(depth_tiers["1.0pct"]["ask"],1)
    dep_s=depth_scaler.fit_transform(d_ratio)
    bull=obi_s*0.5+dep_s*0.3+(1-sprd_s)*0.2
    # Signal based on raw OBI
    if   obi> OBI_THRESHOLD:   raw_sig="BUY"
    elif obi<-OBI_THRESHOLD:   raw_sig="SELL"
    else:                      raw_sig="HOLD"
    # Conviction requires BOTH signal and bull score to agree
    if   raw_sig=="BUY"  and bull>0.6:  sig,col="STRONG BUY","#00875a";conviction="HIGH"
    elif raw_sig=="BUY"  and bull>0.5:  sig,col="BUY","#00875a";conviction="MEDIUM"
    elif raw_sig=="BUY"  and bull<=0.5: sig,col="BUY","#00875a";conviction="LOW"
    elif raw_sig=="SELL" and bull<0.4:  sig,col="STRONG SELL","#dc2626";conviction="HIGH"
    elif raw_sig=="SELL" and bull<0.5:  sig,col="SELL","#dc2626";conviction="MEDIUM"
    elif raw_sig=="SELL" and bull>=0.5: sig,col="SELL","#dc2626";conviction="LOW"
    else:                               sig,col="HOLD","#eab308";conviction="NEUTRAL"
    with state_lock:
        past=[h["obi"] for h in list(history)[-OBI_SMOOTH_N:]]
    smooth=statistics.mean(past+[obi])
    # ── Token-specific sentiment score (0-100) ──────────────────────────────
    # Component 1: OBI score (35%) — scaled 0-100 from -1 to +1
    obi_sentiment = round((obi + 1) / 2 * 100, 1)

    # Component 2: Bull score (30%) — already 0-1, scale to 0-100
    bull_sentiment = round(bull * 100, 1)

    # Component 3: Price momentum (20%) — compare current to 5min rolling avg
    price_history.append(mid)
    if len(price_history) >= 5:
        avg_price = statistics.mean(list(price_history)[:-1])
        momentum = (mid - avg_price) / avg_price * 100
        # Scale: -2% = 0, 0% = 50, +2% = 100
        momentum_sentiment = round(max(0, min(100, (momentum + 2) / 4 * 100)), 1)
    else:
        momentum_sentiment = 50.0

    # Component 4: Volume trend (15%) — current bid vol vs rolling avg
    bid_vol_history.append(bid_vol)
    if len(bid_vol_history) >= 5:
        avg_bid_vol = statistics.mean(list(bid_vol_history)[:-1])
        vol_ratio = bid_vol / avg_bid_vol if avg_bid_vol > 0 else 1.0
        # Scale: 0.5x = 0, 1x = 50, 2x = 100
        vol_sentiment = round(max(0, min(100, (vol_ratio - 0.5) / 1.5 * 100)), 1)
    else:
        vol_sentiment = 50.0

    # Weighted composite (raw single-snapshot score)
    raw_sentiment = round(
        obi_sentiment * 0.35 +
        bull_sentiment * 0.30 +
        momentum_sentiment * 0.20 +
        vol_sentiment * 0.15, 1
    )

    # Smooth over last 20 polls (~5 minutes) to reduce noise
    sentiment_history.append(raw_sentiment)
    token_sentiment = round(statistics.mean(sentiment_history), 1)
    if   token_sentiment >= 75: ts_label = "Strongly Bullish"
    elif token_sentiment >= 55: ts_label = "Bullish"
    elif token_sentiment >= 45: ts_label = "Neutral"
    elif token_sentiment >= 25: ts_label = "Bearish"
    else:                       ts_label = "Strongly Bearish"
    ts_color = ("#00875a" if token_sentiment >= 75 else "#22c55e" if token_sentiment >= 55
                else "#eab308" if token_sentiment >= 45 else "#f97316" if token_sentiment >= 25
                else "#dc2626")
    # ── BTC Fear & Greed (reference only) ──────────────────────────────────
    fng_val = fng_cache.get("value")
    fng_cls = fng_cache.get("classification", "—")
    change_24h = price_24h_cache.get("open_24h")
    return {"ts":datetime.now(timezone.utc).isoformat(),"unix":time.time(),"sources":sources,
            "fear_greed_value": fng_val, "fear_greed_classification": fng_cls,
            "change_24h": change_24h,
            "token_sentiment": token_sentiment, "token_sentiment_label": ts_label,
            "token_sentiment_color": ts_color,
            "sentiment_components": {
                "obi": round(obi_sentiment, 1),
                "bull": round(bull_sentiment, 1),
                "momentum": round(momentum_sentiment, 1),
                "volume": round(vol_sentiment, 1),
                "raw": round(raw_sentiment, 1),
            },
            "mid_price":round(mid,5),"best_bid":round(best_bid,5),"best_ask":round(best_ask,5),
            "spread":round(spread,5),"spread_pct":round(sprd_pct,4),"obi":round(obi,4),
            "smooth_obi":round(smooth,4),"bid_vol":round(bid_vol,2),"ask_vol":round(ask_vol,2),
            "bid_vwap":round(vwap(bids[:10]),5),"ask_vwap":round(vwap(asks[:10]),5),
            "depth_tiers":depth_tiers,"obi_scaled":round(obi_s,3),"spread_scaled":round(sprd_s,3),
            "depth_scaled":round(dep_s,3),"bull_score":round(bull,3),"signal":sig,"signal_color":col,
            "top_bids":bids[:8],"top_asks":asks[:8],"conviction":conviction,"raw_signal":raw_sig}

FNG_URL = "https://api.alternative.me/fng/?limit=1"
fng_cache = {"value": None, "classification": None, "ts": 0}

# 24h price change cache
price_24h_cache = {"open_24h": None, "ts": 0}

def fetch_24h_stats():
    """Fetch 24h stats from Coinbase — updates every 5 minutes."""
    import time as _t
    now = _t.time()
    if price_24h_cache["open_24h"] is not None and (now - price_24h_cache["ts"]) < 300:
        return price_24h_cache
    try:
        url = "https://api.coinbase.com/api/v3/brokerage/market/products/XRP-USD"
        req = urllib.request.Request(url, headers={"User-Agent": "XRP-Bot/1.0", "Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=8) as r:
            d = json.loads(r.read())
        open_24h = float(d.get("price_percentage_change_24h", 0))
        price_24h_cache["open_24h"] = open_24h
        price_24h_cache["ts"] = now
        log.info(f"24h change: {open_24h:.2f}%")
        return price_24h_cache
    except Exception as e:
        log.warning(f"24h stats fetch failed: {e}")
        return price_24h_cache

def fetch_fear_greed():
    """Fetch Fear & Greed Index — updates daily, cache for 1 hour."""
    import time
    now = time.time()
    if fng_cache["value"] is not None and (now - fng_cache["ts"]) < 3600:
        return fng_cache  # Return cached value
    try:
        req = urllib.request.Request(FNG_URL, headers={"User-Agent": "XRP-Bot/1.0"})
        with urllib.request.urlopen(req, timeout=8) as r:
            d = json.loads(r.read())
        data = d.get("data", [{}])[0]
        fng_cache["value"] = int(data.get("value", 50))
        fng_cache["classification"] = data.get("value_classification", "Neutral")
        fng_cache["ts"] = now
        log.info(f"Fear & Greed: {fng_cache['value']} ({fng_cache['classification']})")
        return fng_cache
    except Exception as e:
        log.warning(f"Fear & Greed: {e}")
        return fng_cache  # Return last cached value on error

_poll_running = False
async def poll_loop():
    global _poll_running
    if _poll_running:
        log.warning("poll_loop already running — skipping duplicate start")
        return
    _poll_running = True
    log.info(f"Polling every {POLL_INTERVAL}s …")
    poll_count = 0
    while True:
        t0 = time.time()
        poll_count += 1
        try:
            log.info(f"Poll #{poll_count} starting...")
            cb  = await asyncio.get_event_loop().run_in_executor(None, fetch_coinbase_book)
            log.info(f"Poll #{poll_count} Coinbase: {'OK' if cb else 'FAILED'}")
            krk = await asyncio.get_event_loop().run_in_executor(None, fetch_kraken_book)
            log.info(f"Poll #{poll_count} Kraken: {'OK' if krk else 'FAILED'}")
            # Fetch Fear & Greed (cached hourly, non-blocking)
            await asyncio.get_event_loop().run_in_executor(None, fetch_fear_greed)
            # Fetch 24h stats (cached 5 min)
            await asyncio.get_event_loop().run_in_executor(None, fetch_24h_stats)
            snap = compute_snapshot([b for b in [cb, krk] if b])
            if snap:
                with state_lock:
                    history.append(snap)
                    global latest_snapshot; latest_snapshot=snap
                run_grid_tick(snap)
                log.info(f"[{snap['signal']:^11}] ${snap['mid_price']}  OBI={snap['obi']:+.3f}  bull={snap['bull_score']:.2f}  sources={snap['sources']}")
            else:
                log.warning(f"Poll #{poll_count}: No data from either source")
        except Exception as e:
            import traceback
            log.error(f"Poll #{poll_count} CRASHED: {e}")
            log.error(traceback.format_exc())
        elapsed = time.time() - t0
        log.info(f"Poll #{poll_count} done in {elapsed:.1f}s, sleeping {max(0,POLL_INTERVAL-elapsed):.1f}s")
        await asyncio.sleep(max(0, POLL_INTERVAL - elapsed))

# ─── State Serializer ─────────────────────────────────────────────────────────
def full_state():
    with grid_lock:
        snap  = latest_snapshot
        price = snap.get("mid_price", 0)
        pf    = grid["portfolio"]
        xrp_v = pf["xrp_held"] * price
        unreal= (price - pf["avg_entry"]) * pf["xrp_held"] if pf["avg_entry"] else 0
        cfg   = grid["config"]
        lines = grid["grid_lines"]
        # Build enriched grid lines for visualisation
        grid_vis = []
        for i, lp in enumerate(lines):
            has_buy  = i in grid["buy_orders"]
            has_sell = i in grid["sell_orders"]
            grid_vis.append({
                "index": i,
                "price": lp,
                "has_buy":  has_buy,
                "has_sell": has_sell,
            })
        return {
            "running":   grid["running"],
            "mode":      grid["mode"],
            "config":    cfg,
            "grid_lines": grid_vis,
            "pending":   [s for s in grid["pending"] if s["status"] == "pending"],
            "trade_log": list(grid["trade_log"])[:40],
            "portfolio": {
                **pf,
                "xrp_value_usd":  round(xrp_v, 2),
                "total_value":    round(pf["cash_usd"] + xrp_v, 2),
                "unrealized_pnl": round(unreal, 4),
                "current_price":  price,
            },
            "cb_connected": bool(CB_API_KEY and CB_API_SECRET),
            "market": snap,
        }

# ─── Dashboard ────────────────────────────────────────────────────────────────
DASHBOARD_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1"/>
<meta name="apple-mobile-web-app-capable" content="yes"/>
<meta name="mobile-web-app-capable" content="yes"/>
<meta name="apple-mobile-web-app-status-bar-style" content="default"/>
<meta name="apple-mobile-web-app-title" content="XRP Grid"/>
<meta name="theme-color" content="#ffffff"/>
<title>XRP Grid Bot</title>
<link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800&family=Orbitron:wght@700;900&display=swap" rel="stylesheet"/>
<style>
/* ══ LIGHT MODE (default) ══ */
:root{
  --bg:#f0f4f8; --panel:#ffffff; --panel2:#f7fafc;
  --border:#e2e8f0; --border2:#cbd5e0;
  --text:#1a2332; --muted:#64748b;
  --xrp:#0033AD; --xrp-light:#e8eeff; --xrp-dark:#002080;
  --green:#00875a; --green-bg:#e8f5ee; --green-light:#00b87a;
  --red:#dc2626; --red-bg:#fee2e2; --red-light:#ef4444;
  --yellow:#eab308; --yellow-bg:#fefce8;
  --cyan:#0077aa; --blue:#1d4ed8;
  --fm:'Plus Jakarta Sans',sans-serif; --fh:'Plus Jakarta Sans',sans-serif;
  --shadow:0 1px 3px rgba(0,0,0,.08),0 1px 2px rgba(0,0,0,.04);
  --shadow-md:0 4px 6px rgba(0,0,0,.07),0 2px 4px rgba(0,0,0,.04);
  --radius:10px; --radius-sm:6px;
}
/* ══ DARK MODE ══ */
html.dark{
  --bg:#04080f; --panel:#0a1020; --panel2:#0d1428;
  --border:#1e2d45; --border2:#2a3f5f; --gauge-track:#1e2d45;
  --text:#e2eaf5; --muted:#6b82a0;
  --xrp:#4d8eff; --xrp-light:#0d1f3c; --xrp-dark:#6ba3ff;
  --green:#00e87a; --green-bg:#0a2a1a; --green-light:#00cc6a;
  --red:#ff4466; --red-bg:#2a0a0a; --red-light:#ff6680;
  --yellow:#facc15; --yellow-bg:#1a1a00;
  --cyan:#00d4ff; --blue:#60a5fa;
  --shadow:none; --shadow-md:none;
}
*,*::before,*::after{box-sizing:border-box;margin:0;padding:0}
html,body{min-height:100%;background:var(--bg);color:var(--text);font-family:var(--fm);font-size:16px;-webkit-tap-highlight-color:transparent}
html{transition:background .25s,color .25s}

/* ══ LAYOUT ══ */
.root{display:flex;flex-direction:column;min-height:100vh;padding:0 0 24px;max-width:680px;margin:0 auto}

/* ══ HEADER ══ */
.header{background:var(--panel);border-bottom:1px solid var(--border);padding:12px 16px;text-align:center;box-shadow:var(--shadow)}
.logo-wrap{display:flex;flex-direction:column;align-items:center;gap:8px}
.logo-svg{width:56px;height:56px}
.logo-title{font-family:'Orbitron',sans-serif;font-size:20px;font-weight:900;letter-spacing:3px;color:var(--xrp)}
html.dark .logo-title{color:var(--xrp)}
.logo-sub{font-size:12px;color:var(--muted);letter-spacing:1px;font-weight:500;text-transform:uppercase}
.header-controls{display:flex;align-items:center;justify-content:space-between;padding:0 4px;margin-bottom:12px}
.theme-btn{background:var(--panel2);border:1.5px solid var(--border2);border-radius:16px;padding:6px 12px;font-size:13px;font-weight:600;color:var(--muted);cursor:pointer;font-family:var(--fm);height:32px;display:flex;align-items:center}
.live-pill{display:flex;align-items:center;gap:5px;padding:6px 12px;background:var(--panel2);border:1.5px solid var(--border2);border-radius:16px;height:32px}
.live-dot{width:8px;height:8px;border-radius:50%;background:var(--muted);flex-shrink:0}
.live-dot.on{background:var(--green);animation:pulse 2s ease-in-out infinite}
@keyframes pulse{0%,100%{opacity:1;box-shadow:0 0 0 0 var(--green)}50%{opacity:.7;box-shadow:0 0 0 4px transparent}}
.live-txt{font-size:12px;color:var(--muted);font-weight:600;letter-spacing:.5px}

/* ══ TABS ══ */
.tabs{display:flex;background:var(--panel);border-bottom:1px solid var(--border);padding:0 4px}
.tab{flex:1;font-family:var(--fh);font-size:11px;font-weight:700;letter-spacing:1px;padding:13px 4px;color:var(--muted);cursor:pointer;border-bottom:2px solid transparent;text-align:center;text-transform:uppercase;transition:color .2s,border-color .2s;vertical-align:middle;line-height:1}
.tab.active{color:var(--xrp);border-bottom-color:var(--xrp)}
.badge{display:inline-flex;align-items:center;justify-content:center;width:16px;height:16px;border-radius:50%;background:var(--red);color:#fff;font-size:9px;margin-left:3px;font-weight:700}
.pane{display:none;flex-direction:column;gap:10px;padding:12px 14px}.pane.active{display:flex}

/* ══ PANELS ══ */
.panel{background:var(--panel);border:1px solid var(--border);border-radius:var(--radius);padding:14px;box-shadow:var(--shadow)}
html.dark .panel{box-shadow:none}
.ptitle{font-family:var(--fh);font-size:11px;font-weight:700;letter-spacing:.5px;text-transform:uppercase;color:var(--muted);margin-bottom:10px}
.rbtn{font-family:var(--fh);font-size:9px;font-weight:700;padding:4px 10px;border-radius:6px;border:1.5px solid var(--border2);background:none;color:var(--muted);cursor:pointer;letter-spacing:.5px}
.rbtn.active{background:var(--xrp);color:#fff;border-color:var(--xrp)}

/* ══ METRIC TILES ══ */
.tiles{display:grid;grid-template-columns:repeat(2,1fr);gap:8px}
.tile{background:var(--panel);border:1.5px solid var(--border);border-radius:var(--radius);padding:14px;cursor:pointer;transition:border-color .2s,box-shadow .2s;position:relative;overflow:hidden;box-shadow:var(--shadow);display:flex;flex-direction:column;min-height:110px}
.tile.tile-tall{min-height:165px}
.tile:active{transform:scale(.98)}
html.dark .tile{box-shadow:none}
.tile-label{font-family:var(--fh);font-size:11px;font-weight:600;letter-spacing:.5px;color:var(--muted);text-transform:uppercase;margin-bottom:8px;text-align:left;width:100%;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.tile-expand{font-size:10px;opacity:.5}
.tile-val{font-family:var(--fh);font-size:28px;font-weight:800;line-height:1;color:var(--xrp);text-align:center;width:100%;display:block}
.tile-sub{font-size:13px;color:var(--muted);margin-top:4px;font-weight:500;text-align:center;width:100%;display:block}
.tile-signal{font-family:var(--fh);font-size:20px;font-weight:900;letter-spacing:1px;text-align:center;width:100%;display:block}
/* Tile accent bar */
.tile::before{content:'';position:absolute;top:0;left:0;right:0;height:3px;background:var(--xrp);opacity:.15;border-radius:var(--radius) var(--radius) 0 0}
.tile.tile-buy::before{background:var(--green);opacity:.3}
.tile.tile-sell::before{background:var(--red);opacity:.4}
.tile.tile-hold::before{background:var(--yellow);opacity:.4}

/* ══ TIME STRIP ══ */
.time-strip{background:var(--panel);border:1px solid var(--border);border-radius:var(--radius-sm);padding:8px 14px;display:flex;align-items:center;justify-content:space-between}
.time-val{font-family:'Orbitron',sans-serif;font-size:15px;color:var(--xrp);font-weight:700;letter-spacing:1px}
.cbar{height:3px;background:var(--border2);border-radius:2px;overflow:hidden;width:80px}
.cfill{height:100%;background:linear-gradient(90deg,var(--xrp),var(--cyan));transition:width 1s linear!important;border-radius:2px}
.time-label{font-size:10px;color:var(--muted);font-weight:500}

/* ══ EXPAND MODAL ══ */
.modal-overlay{position:fixed;inset:0;background:rgba(0,0,0,.5);z-index:1000;display:none;align-items:flex-end;justify-content:center}
.modal-overlay.open{display:flex;animation:fadeIn .2s ease}
@keyframes fadeIn{from{opacity:0}to{opacity:1}}
.modal{background:var(--panel);border-radius:20px 20px 0 0;width:100%;max-width:680px;padding:20px;max-height:85vh;overflow-y:auto;animation:slideUp .25s ease}
@keyframes slideUp{from{transform:translateY(100%)}to{transform:translateY(0)}}
.modal-handle{width:36px;height:4px;background:var(--border2);border-radius:2px;margin:0 auto 16px}
.modal-title{font-family:var(--fh);font-size:14px;font-weight:900;letter-spacing:1px;color:var(--xrp);margin-bottom:14px;text-transform:uppercase}
.modal-price{font-family:var(--fh);font-size:32px;font-weight:800;color:var(--xrp);margin-bottom:4px}
.modal-change{font-size:14px;font-weight:600;margin-bottom:16px}
.modal-chart{height:220px;margin-bottom:12px}
.modal-close{position:absolute;top:20px;right:20px;width:28px;height:28px;border-radius:50%;background:var(--bg);border:1px solid var(--border);display:flex;align-items:center;justify-content:center;cursor:pointer;font-size:14px;color:var(--muted)}
.stat-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:12px}
.stat-item{background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);padding:10px}
.stat-label{font-size:12px;color:var(--muted);font-weight:600;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px}
.stat-val{font-size:17px;font-weight:700;font-family:var(--fh)}

/* ══ SIGNAL CARDS ══ */
.signal-queue{display:flex;flex-direction:column;gap:10px}
.sig-card{background:var(--panel);border-radius:var(--radius);padding:16px;box-shadow:var(--shadow)}
html.dark .sig-card{box-shadow:none}
.sig-card.buy{border:2px solid var(--green)}
.sig-card.sell{border:2px solid var(--red)}
.sig-hdr{display:flex;align-items:center;justify-content:space-between;margin-bottom:10px}
.sig-badge{font-family:var(--fh);font-size:13px;font-weight:900;letter-spacing:1px;padding:5px 12px;border-radius:var(--radius-sm)}
.sig-badge.buy{background:var(--green-bg);color:var(--green);border:1.5px solid var(--green)}
.sig-badge.sell{background:var(--red-bg);color:var(--red);border:1.5px solid var(--red)}
.sig-price{font-family:var(--fh);font-size:32px;font-weight:900;margin:8px 0}
.sig-price.buy{color:var(--green)}.sig-price.sell{color:var(--red)}
.sig-details{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:10px 0}
.sig-detail{background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);padding:8px}
.sig-detail-label{font-size:11px;color:var(--muted);font-weight:600;text-transform:uppercase;margin-bottom:3px;letter-spacing:.5px}
.sig-detail-val{font-size:16px;color:var(--text);font-weight:600}
.sig-meta{display:flex;align-items:center;gap:8px;margin:8px 0;padding:8px 10px;background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);flex-wrap:wrap}
.sig-conf{font-family:var(--fh);font-size:8px;font-weight:700;letter-spacing:1px;padding:3px 8px;border-radius:4px;margin-left:auto}
.sig-actions{display:flex;gap:8px;margin-top:12px}
.btn-confirm{flex:1;color:#fff;border:none;padding:16px;border-radius:var(--radius-sm);font-family:var(--fh);font-size:13px;font-weight:900;letter-spacing:1px;cursor:pointer}
.btn-confirm.buy-confirm{background:var(--green)}
.btn-confirm.sell-confirm{background:var(--red)}
.btn-skip{flex:1;background:var(--bg);border:1.5px solid var(--border2);color:var(--muted);padding:16px;border-radius:var(--radius-sm);font-family:var(--fh);font-size:13px;font-weight:700;cursor:pointer}
.no-signals{text-align:center;padding:36px 20px;color:var(--muted)}
.spinner{width:40px;height:40px;border:3px solid var(--border2);border-top-color:var(--xrp);border-radius:50%;animation:spin .8s linear infinite;margin:0 auto 14px}
@keyframes spin{to{transform:rotate(360deg)}}
.no-sig-txt{font-size:15px;font-weight:500}

/* ══ CHARTS ══ */
.chart-wrap{position:relative;height:200px}
canvas{display:block;width:100%!important;height:100%!important}
.chart-row{display:grid;grid-template-columns:1fr 1fr;gap:10px}
@media(max-width:500px){.chart-row{grid-template-columns:1fr}}

/* ══ ORDER BOOKS ══ */
.books{display:grid;grid-template-columns:1fr 1fr;gap:10px}
@media(max-width:480px){.books{grid-template-columns:1fr}}
.ob-table{width:100%;border-collapse:collapse;font-size:14px}
.ob-table th{font-family:var(--fh);font-size:9px;letter-spacing:1px;color:var(--muted);text-align:right;padding:3px 5px 7px;text-transform:uppercase;font-weight:700}
.ob-table th:first-child{text-align:left}
.ob-table td{padding:5px;text-align:right;border-bottom:1px solid var(--border);position:relative;font-weight:500}
.ob-table td:first-child{text-align:left}
.ob-bid td{color:var(--green)}.ob-ask td{color:var(--red)}
.dbar{position:absolute;top:0;right:0;height:100%;opacity:.07;pointer-events:none}

/* ══ OBI GAUGE ══ */
.gauge-wrap{margin:10px 0}
.gauge-track{width:100%;height:12px;border-radius:6px;position:relative;border:1px solid var(--border);background:linear-gradient(90deg,var(--red-bg),var(--panel2),var(--green-bg))}
html.dark .gauge-track{background:linear-gradient(90deg,rgba(255,68,102,.2),var(--panel2),rgba(0,232,122,.2))}
.gauge-thumb{position:absolute;top:50%;transform:translate(-50%,-50%);width:16px;height:22px;background:var(--text);border-radius:4px;transition:left .5s cubic-bezier(.4,0,.2,1)!important;box-shadow:0 2px 6px rgba(0,0,0,.15)}
.gauge-labels{display:flex;justify-content:space-between;font-size:13px;font-weight:600;margin-top:6px}

/* ══ PORTFOLIO ══ */
.pnl-grid{display:grid;grid-template-columns:repeat(2,1fr);gap:8px;margin-bottom:8px}
@media(max-width:420px){}
.pnl-c{background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);padding:10px;text-align:center;justify-content:center;min-height:60px}
.pnl-label{font-family:var(--fh);font-size:11px;letter-spacing:.5px;color:var(--muted);margin-bottom:4px;font-weight:600;text-transform:uppercase;display:block}
.pnl-val{font-size:20px;font-weight:700;font-family:var(--fh);color:var(--text);display:block;margin-top:4px}

/* ══ TRADE LOG ══ */
.tlog{max-height:240px;overflow-y:auto}
.trow{display:flex;align-items:center;gap:7px;padding:7px 0;border-bottom:1px solid var(--border);flex-wrap:wrap}
.tbadge{padding:3px 8px;border-radius:4px;font-family:var(--fh);font-size:9px;letter-spacing:1px;flex-shrink:0;font-weight:700}
.tbuy{background:var(--green-bg);color:var(--green);border:1px solid var(--green)}
.tsell{background:var(--red-bg);color:var(--red);border:1px solid var(--red)}
.tmeta{color:var(--muted);font-size:13px;font-weight:500}

/* ══ GRID CONFIG ══ */
.cfg-grid{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.inp-group{display:flex;flex-direction:column;gap:4px}
.inp-label{font-family:var(--fh);font-size:11px;letter-spacing:1px;color:var(--muted);text-transform:uppercase;font-weight:700}
.inp{background:var(--bg);border:1.5px solid var(--border);border-radius:var(--radius-sm);color:var(--text);font-family:var(--fm);font-size:16px;font-weight:500;padding:9px 12px;width:100%;outline:none}
.inp::placeholder{color:var(--muted);font-weight:400;opacity:.6}
.inp:focus{border-color:var(--xrp)}
.btn-row{display:flex;gap:8px;flex-wrap:wrap;margin-top:12px}
.btn{font-family:var(--fh);font-size:11px;font-weight:700;letter-spacing:1px;padding:10px 18px;border-radius:var(--radius-sm);border:none;cursor:pointer;text-transform:uppercase}
.btn-xrp{background:var(--xrp);color:#fff}
.btn-outline{background:none;border:1.5px solid var(--border2);color:var(--muted)}

/* ══ BOT CONTROLS ══ */
.tog-row{display:flex;align-items:center;gap:12px;flex-wrap:wrap}
.tog{position:relative;width:52px;height:28px;flex-shrink:0}.tog input{opacity:0;width:0;height:0}
.tog-sl{position:absolute;inset:0;background:var(--border2);border-radius:14px;cursor:pointer}
.tog-sl::before{content:'';position:absolute;width:22px;height:22px;left:3px;top:3px;background:#fff;border-radius:50%;transition:transform .3s!important;box-shadow:0 1px 3px rgba(0,0,0,.2)}
.tog input:checked+.tog-sl{background:var(--green)}
.tog input:checked+.tog-sl::before{transform:translateX(24px)}
.tog-label{font-size:16px;color:var(--text);font-weight:600}
.mode-row{display:flex;gap:6px}
.mbtn{font-family:var(--fh);font-size:11px;font-weight:700;letter-spacing:1px;padding:7px 12px;border:1.5px solid var(--border2);border-radius:var(--radius-sm);background:none;color:var(--muted);cursor:pointer;text-transform:uppercase}
.mbtn.paper.active{background:var(--yellow);color:#fff;border-color:var(--yellow)}
.mbtn.live.active{background:var(--red);color:#fff;border-color:var(--red)}

/* ══ GRID VIZ ══ */
.grid-viz{position:relative;height:260px;background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);overflow:hidden;margin-top:8px}
.grid-line{position:absolute;left:0;right:0;height:1px;background:var(--border2)}
.grid-line-label{position:absolute;right:10px;font-size:13px;color:var(--muted);transform:translateY(-50%);font-weight:500}
.grid-line-label.has-buy{color:var(--green);font-weight:700}
.grid-line-label.has-sell{color:var(--red);font-weight:700}
.price-cursor{position:absolute;left:0;right:0;height:3px;background:var(--xrp);z-index:10;transition:top .4s cubic-bezier(.4,0,.2,1)!important}
.price-tag{position:absolute;right:10px;background:var(--xrp);color:#fff;font-family:var(--fh);font-size:10px;font-weight:700;padding:3px 8px;border-radius:3px;transform:translateY(-50%);white-space:nowrap}

/* ══ MISC ══ */
.src-badge{display:inline-flex;align-items:center;gap:4px;padding:3px 8px;border-radius:4px;border:1px solid var(--border2);font-size:13px;color:var(--muted);font-weight:500}
.src-row{display:flex;gap:5px;flex-wrap:wrap}
.demo-banner{background:var(--xrp-light);border:1.5px solid rgba(0,51,173,.2);border-radius:var(--radius-sm);padding:10px 14px;font-size:14px;color:var(--xrp);font-weight:600;display:flex;align-items:center;gap:8px}
html.dark .demo-banner{background:var(--xrp-light);border-color:rgba(77,142,255,.2);color:var(--xrp)}
/* Version */
.version-bar{text-align:center;padding:16px;font-size:10px;color:var(--muted);font-weight:500;letter-spacing:1px;border-top:1px solid var(--border);margin-top:8px}
::-webkit-scrollbar{width:3px}::-webkit-scrollbar-track{background:var(--bg)}::-webkit-scrollbar-thumb{background:var(--border2);border-radius:2px}
</style>
</head>
<body>
<div class="root">

<!-- ══ HEADER ══ -->
<div class="header">
  <div class="header-controls">
    <div class="live-pill">
      <div class="live-dot" id="liveDot"></div>
      <span class="live-txt" id="liveTxt">CONNECTING</span>
    </div>
    <button class="theme-btn" id="themeBtn" onclick="toggleTheme()">🌙 Dark</button>
  </div>
  <div class="logo-wrap">
    <!-- XRP Grid Bot Logo -->
    <svg class="logo-svg" viewBox="0 0 100 100" xmlns="http://www.w3.org/2000/svg">
      <polygon fill="var(--xrp)" points="50,8 88,29 88,71 50,92 12,71 12,29"/>
      <polygon fill="var(--xrp-dark)" points="50,20 78,36 78,64 50,80 22,64 22,36"/>
      <rect fill="#ffffff" x="28" y="47" width="44" height="10" rx="5" transform="rotate(45 50 52)"/>
      <rect fill="#ffffff" x="28" y="47" width="44" height="10" rx="5" transform="rotate(-45 50 52)"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="12" y1="42" x2="22" y2="42"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="12" y1="52" x2="22" y2="52"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="12" y1="62" x2="22" y2="62"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="78" y1="42" x2="88" y2="42"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="78" y1="52" x2="88" y2="52"/>
      <line stroke="rgba(255,255,255,0.4)" stroke-width="1.5" x1="78" y1="62" x2="88" y2="62"/>
      <circle fill="#00cc66" cx="50" cy="8" r="4"/>
      <circle fill="#ff4466" cx="50" cy="92" r="4"/>
    </svg>
    <div class="logo-title">XRP GRID BOT</div>
    <div class="logo-sub">Semi-Auto · Order Book Intelligence</div>
  </div>
</div>

<!-- ══ TABS ══ -->
<div class="tabs">
  <div class="tab active" onclick="switchTab('signals')">Signals <span id="pendingBadge" style="display:none" class="badge">0</span></div>
  <div class="tab" onclick="switchTab('market')">Market</div>
  <div class="tab" onclick="switchTab('grid')">Grid</div>
  <div class="tab" onclick="switchTab('portfolio')">Portfolio</div>
</div>

<!-- ══ SIGNALS TAB ══ -->
<div id="pane-signals" class="pane active">
  <div class="demo-banner" id="demoBanner">✦ DEMO MODE — Connecting to live data...</div>

  <!-- Time strip -->
  <div class="time-strip">
    <div><div class="time-label">LOCAL TIME</div><div class="time-val" id="clock">--:--:--</div></div>
    <div style="text-align:right"><div class="time-label">NEXT POLL</div><div class="cbar"><div class="cfill" id="cfill" style="width:100%"></div></div></div>
  </div>

  <!-- Metric tiles — all 4 expandable -->
  <div class="tiles">
    <div class="tile tile-tall" id="tile-price" onclick="expandTile('price')">
      <div class="tile-label">XRP PRICE <span class="tile-expand">↗</span></div>
      <div style="flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center">
        <div class="tile-val" id="tilePrice" style="font-size:26px">—</div>
        <div class="tile-sub" id="tilePriceSub" style="text-align:center;margin-top:6px">—</div>
      </div>
    </div>
    <div class="tile tile-tall" id="tile-signal" onclick="expandTile('signal')">
      <div class="tile-label">SIGNAL <span class="tile-expand">↗</span></div>
      <div id="gaugeLabel" style="font-family:var(--fh);font-size:18px;font-weight:900;text-align:center;color:#64748b;line-height:1.1;margin-bottom:1px">—</div>
      <div id="gaugeConv" style="font-size:10px;color:var(--muted);text-align:center;margin-bottom:4px"></div>
      <div style="flex:1;display:flex;flex-direction:column;align-items:center;justify-content:flex-end">
        <div style="display:flex;align-items:center;justify-content:center;width:100%;gap:2px">
          <div style="font-size:10px;color:#dc2626;font-weight:700;width:24px;text-align:right;flex-shrink:0;padding-bottom:8px">SELL</div>
          <svg id="gaugesvg" viewBox="0 0 120 65" width="100%" style="flex:1;overflow:visible;max-width:110px">
            <defs>
              <linearGradient id="gaugeGrad" x1="0%" y1="0%" x2="100%" y2="0%">
                <stop offset="0%" stop-color="#dc2626"/>
                <stop offset="25%" stop-color="#f97316"/>
                <stop offset="50%" stop-color="#eab308"/>
                <stop offset="75%" stop-color="#22c55e"/>
                <stop offset="100%" stop-color="#00875a"/>
              </linearGradient>
            </defs>
            <path d="M10,52 A50,50 0 0,1 110,52" fill="none" stroke="var(--border)" stroke-width="8" stroke-linecap="round"/>
            <path d="M10,52 A50,50 0 0,1 110,52" fill="none" stroke="url(#gaugeGrad)" stroke-width="8" stroke-linecap="round"/>
            <line id="gaugeNeedle" x1="60" y1="52" x2="60" y2="6" stroke="#64748b" stroke-width="2.5" stroke-linecap="round"/>
            <circle cx="60" cy="52" r="4" id="gaugeDot" fill="#64748b"/>
            <circle cx="60" cy="52" r="1.8" fill="white"/>
          </svg>
          <div style="font-size:10px;color:#00875a;font-weight:700;width:24px;text-align:left;flex-shrink:0;padding-bottom:8px">BUY</div>
        </div>
        <div class="tile-sub" id="tileSignalSub" style="text-align:center">—</div>
      </div>
    </div>
    <div class="tile" id="tile-bull" onclick="expandTile('bull')">
      <div class="tile-label">BULL SCORE <span class="tile-expand">↗</span> <span onclick="event.stopPropagation();showBullPopup()" style="cursor:pointer;font-size:10px;font-weight:700;color:var(--xrp);border:1.5px solid var(--xrp);border-radius:50%;width:16px;height:16px;display:inline-flex;align-items:center;justify-content:center;margin-left:6px;opacity:.7">?</span></div>
      <div class="tile-val" id="tileBull">—</div>
      <div class="tile-sub">Composite [0–1]</div>
    </div>
    <div class="tile" id="tile-obi" onclick="expandTile('obi')">
      <div class="tile-label">OBI <span class="tile-expand">↗</span></div>
      <div class="tile-val" id="tileObi">—</div>
      <div class="tile-sub">Smooth: <span id="tileObiSmooth">—</span></div>
    </div>
  </div>

  <!-- Token Sentiment -->
  <div class="panel" id="fngPanel" style="display:none">
    <div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:10px">
      <div>
        <div class="ptitle" style="margin-bottom:3px" id="sentimentTitle">XRP MARKET SENTIMENT</div>
        <div style="font-size:11px;color:var(--muted)">Token-specific · Live order book · Updates every 15s</div>
      </div>
      <div style="text-align:right">
        <div id="fngValue" style="font-family:var(--fh);font-size:32px;font-weight:800;color:var(--muted)">—</div>
        <div id="fngLabel" style="font-size:13px;font-weight:700;color:var(--muted);margin-top:2px">—</div>
      </div>
    </div>
    <!-- Gradient bar -->
    <div style="margin-bottom:10px">
      <div style="height:10px;border-radius:5px;background:linear-gradient(90deg,#dc2626,#f97316,#eab308,#22c55e,#00875a);position:relative;overflow:visible">
        <div id="fngThumb" style="position:absolute;top:50%;transform:translate(-50%,-50%);width:14px;height:20px;background:var(--text);border-radius:3px;transition:left .5s ease;left:50%"></div>
      </div>
      <div style="display:flex;justify-content:space-between;font-size:9px;color:var(--muted);font-weight:600;margin-top:4px">
        <span style="color:#dc2626">Strongly Bearish</span>
        <span>Bearish</span>
        <span>Neutral</span>
        <span>Bullish</span>
        <span style="color:#00875a">Strongly Bullish</span>
      </div>
    </div>
    <!-- Component breakdown -->
    <div style="padding:10px;background:var(--bg);border:1px solid var(--border);border-radius:8px;margin-bottom:8px">
      <div class="ptitle" style="margin-bottom:8px">SCORE BREAKDOWN</div>
      <div style="display:flex;flex-direction:column;gap:6px">
        <div style="display:flex;align-items:center;gap:8px">
          <div style="font-size:11px;color:var(--muted);width:110px;flex-shrink:0">Order Book (35%)</div>
          <div style="flex:1;height:5px;background:var(--border);border-radius:3px;overflow:hidden"><div id="sc_obi" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div></div>
          <div id="sv_obi" style="font-size:11px;font-weight:700;color:var(--muted);width:28px;text-align:right">—</div>
        </div>
        <div style="display:flex;align-items:center;gap:8px">
          <div style="font-size:11px;color:var(--muted);width:110px;flex-shrink:0">Bull Score (30%)</div>
          <div style="flex:1;height:5px;background:var(--border);border-radius:3px;overflow:hidden"><div id="sc_bull" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div></div>
          <div id="sv_bull" style="font-size:11px;font-weight:700;color:var(--muted);width:28px;text-align:right">—</div>
        </div>
        <div style="display:flex;align-items:center;gap:8px">
          <div style="font-size:11px;color:var(--muted);width:110px;flex-shrink:0">Momentum (20%)</div>
          <div style="flex:1;height:5px;background:var(--border);border-radius:3px;overflow:hidden"><div id="sc_mom" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div></div>
          <div id="sv_mom" style="font-size:11px;font-weight:700;color:var(--muted);width:28px;text-align:right">—</div>
        </div>
        <div style="display:flex;align-items:center;gap:8px">
          <div style="font-size:11px;color:var(--muted);width:110px;flex-shrink:0">Volume (15%)</div>
          <div style="flex:1;height:5px;background:var(--border);border-radius:3px;overflow:hidden"><div id="sc_vol" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div></div>
          <div id="sv_vol" style="font-size:11px;font-weight:700;color:var(--muted);width:28px;text-align:right">—</div>
        </div>
      </div>
    </div>
    <!-- BTC reference -->
    <div style="display:flex;justify-content:space-between;align-items:center;padding:8px 10px;background:var(--bg);border:1px solid var(--border);border-radius:8px">
      <div style="font-size:11px;color:var(--muted)">BTC Sentiment (alternative.me)</div>
      <div style="display:flex;align-items:center;gap:6px">
        <div id="fngBtcValue" style="font-size:13px;font-weight:700;color:var(--muted)">—</div>
        <div id="fngBtcLabel" style="font-size:11px;font-weight:600;color:var(--muted)">—</div>
      </div>
    </div>
    <div id="sentimentDivergence" style="display:none;font-size:10px;color:var(--yellow);text-align:center;margin-top:6px;font-style:italic"></div>
  </div>

  <!-- Signal queue -->
  <div class="panel">
    <div class="ptitle">PENDING SIGNALS — CONFIRM TO EXECUTE</div>
    <div class="signal-queue" id="signalQueue">
      <div class="no-signals"><div class="spinner"></div><div class="no-sig-txt">Watching grid levels...</div></div>
    </div>
  </div>
</div>

<!-- ══ MARKET TAB ══ -->
<div id="pane-market" class="pane">
  <div class="panel" style="padding-bottom:8px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">
      <div class="ptitle" style="margin-bottom:0">PRICE · VWAP</div>
      <div style="display:flex;gap:4px" id="rangeButtons">
        <button onclick="setRange(20)" id="r20" class="rbtn active">15m</button>
        <button onclick="setRange(40)" id="r40" class="rbtn">30m</button>
        <button onclick="setRange(80)" id="r80" class="rbtn">All</button>
      </div>
    </div>
    <div class="chart-wrap"><canvas id="priceChart"></canvas></div>
  </div>
  <div class="panel"><div class="ptitle">OBI · BULL SCORE</div><div class="chart-wrap"><canvas id="obiChart"></canvas></div></div>
  <div class="books">
    <div class="panel" style="overflow:auto;max-height:220px">
      <div class="ptitle">BIDS</div>
      <table class="ob-table"><thead><tr><th>Price</th><th>Qty</th><th>%</th></tr></thead><tbody id="bidsBody"></tbody></table>
    </div>
    <div class="panel" style="overflow:auto;max-height:220px">
      <div class="ptitle">ASKS</div>
      <table class="ob-table"><thead><tr><th>Price</th><th>Qty</th><th>%</th></tr></thead><tbody id="asksBody"></tbody></table>
    </div>
  </div>
  <div class="panel">
    <div class="ptitle">ORDER BOOK IMBALANCE</div>
    <div class="gauge-wrap">
      <div class="gauge-track"><div class="gauge-thumb" id="gaugeThumb" style="left:50%"></div></div>
      <div class="gauge-labels"><span style="color:var(--red)">SELL</span><span style="color:var(--muted)">NEUTRAL</span><span style="color:var(--green)">BUY</span></div>
    </div>
    <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-top:6px">
      <span style="font-size:12px;font-weight:500">Bid: <span id="bidVol" style="color:var(--green);font-weight:700">—</span> &nbsp;|&nbsp; Ask: <span id="askVol" style="color:var(--red);font-weight:700">—</span></span>
      <div class="src-row" id="srcRow"></div>
    </div>
  </div>
</div>

<!-- ══ GRID TAB ══ -->
<div id="pane-grid" class="pane">
  <div class="panel">

    <!-- Progress bar + Notifications button -->
    <div style="display:flex;align-items:center;gap:8px;margin-bottom:16px">
      <div style="display:flex;gap:5px;flex:1" id="gridProgress">
      <div style="flex:1;height:4px;border-radius:2px;background:var(--border2)" id="prog1"></div>
      <div style="flex:1;height:4px;border-radius:2px;background:var(--border2)" id="prog2"></div>
      <div style="flex:1;height:4px;border-radius:2px;background:var(--border2)" id="prog3"></div>
      <div style="flex:1;height:4px;border-radius:2px;background:var(--border2)" id="prog4"></div>
      </div>
      <button id="notifBtn" onclick="enableNotifications()" style="font-family:var(--fh);font-size:10px;font-weight:700;padding:6px 12px;border-radius:20px;border:1.5px solid var(--border2);background:var(--panel);color:var(--muted);cursor:pointer;white-space:nowrap;flex-shrink:0">🔔 ALERTS</button>
    </div>

    <!-- Section 1: Price Range -->
    <div class="ptitle">PRICE RANGE</div>
    <div class="cfg-grid" style="margin-bottom:16px">
      <div class="inp-group"><div class="inp-label">Lower Price (USD)</div><input class="inp" id="cfgLower" type="number" step="0.01" placeholder="e.g. 1.35" value="1.35" oninput="updateActivateBtn()"/></div>
      <div class="inp-group"><div class="inp-label">Upper Price (USD)</div><input class="inp" id="cfgUpper" type="number" step="0.01" placeholder="e.g. 1.55" value="1.50" oninput="updateActivateBtn()"/></div>
      <div class="inp-group"><div class="inp-label">Grid Levels</div><input class="inp" id="cfgLevels" type="number" step="1" min="2" max="50" placeholder="e.g. 10" value="10" oninput="updateActivateBtn()"/></div>
    </div>

    <!-- Section 2: Order Size -->
    <div class="ptitle">ORDER SIZE</div>
    <div style="display:flex;gap:8px;align-items:center;margin-bottom:16px">
      <div style="flex:1;position:relative">
        <input class="inp" id="cfgAmount" type="number" step="1" min="1" placeholder="e.g. 10" value="10" oninput="updateActivateBtn()"/>
        <span id="cfgAmountUnit" style="position:absolute;right:12px;top:50%;transform:translateY(-50%);font-size:13px;color:var(--muted);font-weight:600;pointer-events:none">XRP</span>
      </div>
      <div style="display:flex;border:1.5px solid var(--border2);border-radius:8px;overflow:hidden;flex-shrink:0">
        <button id="toggleXRP" onclick="setOrderType('xrp')" style="padding:8px 14px;background:var(--xrp);color:#fff;border:none;cursor:pointer;font-family:var(--fh);font-size:10px;font-weight:700">XRP</button>
        <button id="toggleUSD" onclick="setOrderType('usd')" style="padding:8px 14px;background:none;color:var(--muted);border:none;cursor:pointer;font-family:var(--fh);font-size:10px;font-weight:700">USD</button>
      </div>
    </div>

    <!-- Section 3: Stop/TP -->
    <div class="ptitle">RISK SETTINGS</div>
    <div class="cfg-grid" style="margin-bottom:16px">
      <div class="inp-group"><div class="inp-label">Stop Loss (%)</div><input class="inp" id="cfgStop" type="number" step="0.5" placeholder="e.g. 5%" value="5"/></div>
      <div class="inp-group"><div class="inp-label">Take Profit (%)</div><input class="inp" id="cfgTP" type="number" step="0.5" placeholder="e.g. 15%" value="15"/></div>
    </div>

    <!-- Section 3b: Direction -->
    <div class="ptitle">SIGNAL DIRECTION</div>
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:8px;margin-bottom:16px">
      <button id="dirBoth" onclick="setDirection('both')" style="padding:10px;border-radius:8px;border:2px solid var(--xrp);background:rgba(0,51,173,.08);font-family:var(--fh);font-size:10px;font-weight:700;color:var(--xrp);cursor:pointer">⚡ BOTH</button>
      <button id="dirBuy" onclick="setDirection('buy')" style="padding:10px;border-radius:8px;border:2px solid var(--border2);background:var(--panel);font-family:var(--fh);font-size:10px;font-weight:700;color:var(--muted);cursor:pointer">🟢 BUY ONLY</button>
      <button id="dirSell" onclick="setDirection('sell')" style="padding:10px;border-radius:8px;border:2px solid var(--border2);background:var(--panel);font-family:var(--fh);font-size:10px;font-weight:700;color:var(--muted);cursor:pointer">🔴 SELL ONLY</button>
    </div>

    <!-- Section 4: Mode -->
    <div class="ptitle">MODE</div>
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:16px">
      <button id="modePaper" onclick="setMode('paper')" style="padding:12px;border-radius:8px;border:2px solid var(--border2);background:var(--panel);font-family:var(--fh);font-size:11px;font-weight:700;color:var(--muted);cursor:pointer">📝 PAPER</button>
      <button id="modeLive" onclick="setMode('live')" style="padding:12px;border-radius:8px;border:2px solid var(--border2);background:var(--panel);font-family:var(--fh);font-size:11px;font-weight:700;color:var(--muted);cursor:pointer">🔴 LIVE</button>
    </div>

    <!-- CB Status -->
    <div style="font-size:12px;color:var(--muted);font-weight:500;margin-bottom:16px;text-align:center">
      Coinbase: <span id="cbStat" style="color:var(--red);font-weight:700">NOT SET</span>
    </div>

    <!-- Activate button -->
    <button id="activateBtn" onclick="activateBot()" style="width:100%;padding:16px;border-radius:10px;border:none;background:var(--border2);color:var(--muted);font-family:var(--fh);font-size:13px;font-weight:800;cursor:not-allowed;transition:all .2s;letter-spacing:.5px">
      ▶ ACTIVATE BOT
    </button>
    <div id="activateSummary" style="font-size:11px;color:var(--muted);text-align:center;margin-top:8px">Fill in all fields to activate</div>
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:8px">
      <button onclick="updateGridConfig()" style="padding:10px;border-radius:8px;border:1.5px solid var(--xrp);background:none;color:var(--xrp);font-family:var(--fh);font-size:11px;font-weight:700;cursor:pointer">💾 UPDATE CONFIG</button>
      <button onclick="resetGridFields()" style="padding:10px;border-radius:8px;border:1.5px solid var(--border2);background:none;color:var(--muted);font-family:var(--fh);font-size:11px;font-weight:600;cursor:pointer">🔄 RESET FIELDS</button>
    </div>

    <!-- Bot status (shown when running) -->
    <div id="botStatusRow" style="display:none;margin-top:12px">
      <div style="padding:14px;background:rgba(0,135,90,.08);border:2px solid var(--green);border-radius:10px;text-align:center">
        <div style="display:flex;align-items:center;justify-content:center;gap:8px;margin-bottom:6px">
          <span style="width:10px;height:10px;border-radius:50%;background:var(--green);display:inline-block;animation:pulse 1.5s infinite"></span>
          <span style="font-size:15px;font-weight:800;color:var(--green);font-family:var(--fh)">BOT ACTIVE</span>
        </div>
        <div id="botStatusDetail" style="font-size:12px;color:var(--muted);margin-bottom:10px">Watching for signals...</div>
        <div style="font-size:11px;color:var(--muted);margin-bottom:12px">Signals will appear on the SIGNALS tab</div>
        <button onclick="deactivateBot()" style="width:100%;padding:12px;border-radius:8px;border:2px solid var(--red);background:rgba(220,38,38,.08);color:var(--red);font-family:var(--fh);font-size:12px;font-weight:700;cursor:pointer">⏹ STOP BOT</button>
      </div>
    </div>
  </div>

  <!-- Grid visualization -->
  <div class="panel">
    <div class="ptitle">GRID LEVELS</div>
    <div id="gridViz" style="position:relative;height:200px;overflow:hidden;border-radius:8px;background:var(--bg);border:1px solid var(--border)"><div style="display:flex;align-items:center;justify-content:center;height:100%;color:var(--muted);font-size:13px">Configure grid above</div></div>
  </div>
</div>

<!-- ══ PORTFOLIO TAB ══ -->
<div id="pane-portfolio" class="pane">
  <div class="panel">
    <div class="ptitle">PORTFOLIO OVERVIEW</div>
    <div class="pnl-grid">
      <div class="pnl-c"><div class="pnl-label">CASH</div><div class="pnl-val" id="pfCash" style="color:var(--xrp)">—</div></div>
      <div class="pnl-c"><div class="pnl-label">XRP HELD</div><div class="pnl-val" id="pfXrp" style="color:var(--xrp)">—</div></div>
      <div class="pnl-c"><div class="pnl-label">XRP VALUE</div><div class="pnl-val" id="pfXrpVal" style="color:var(--xrp)">—</div></div>
      <div class="pnl-c"><div class="pnl-label">TOTAL</div><div class="pnl-val" id="pfTotal" style="color:var(--xrp)">—</div></div>
      <div class="pnl-c"><div class="pnl-label">UNREALIZED</div><div class="pnl-val" id="pfUnreal">—</div></div>
      <div class="pnl-c"><div class="pnl-label">REALIZED</div><div class="pnl-val" id="pfReal">—</div></div>
    </div>
    <div style="margin-top:10px;font-size:12px;color:var(--muted);font-weight:500;display:flex;flex-wrap:wrap;gap:12px">
      <span>Avg Entry: <span id="pfAvg" style="color:var(--text);font-weight:600">—</span></span>
      <span>Current: <span id="pfCur" style="color:var(--xrp);font-weight:600">—</span></span>
      <span>Last Sell: <span id="pfLastSell" style="color:var(--red);font-weight:600">—</span></span>
      <span>Last Buy: <span id="pfLastBuy" style="color:var(--green);font-weight:600">—</span></span>
    </div>
  </div>
  <div class="panel" id="pfOpenOrdersPanel" style="display:none">
    <div class="ptitle">OPEN BUY ORDERS <span id="pfOpenCount" style="float:right;color:var(--muted)"></span></div>
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:4px;font-size:11px;font-weight:600;color:var(--muted);padding:4px 0;border-bottom:1px solid var(--border);margin-bottom:4px">
      <div>Level</div><div>Buy Price</div><div>XRP</div><div>Unrealized</div>
    </div>
    <div id="pfOpenOrders"></div>
    <div style="margin-top:8px;font-size:13px;color:var(--muted)">Total: <strong id="pfOpenTotal" style="color:var(--xrp)">—</strong></div>
  </div>
  <div class="panel">
    <div class="ptitle">TRADE HISTORY <span id="tradeCount" style="float:right;color:var(--muted)"></span></div>
    <div class="tlog" id="tradeLog"><div style="text-align:center;padding:24px;color:var(--muted);font-size:13px">No trades yet</div></div>
  </div>
</div>

<!-- ══ VERSION BAR ══ -->
<div class="version-bar">XRP GRID BOT · v3.7 · PAPER MODE · COINBASE ADVANCED + KRAKEN</div>

<!-- ══ BULL SCORE POPUP ══ -->
<div id="bullPopup" style="display:none;position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,.6);z-index:1000;padding:20px;overflow-y:auto" onclick="hideBullPopup()">
  <div style="background:var(--panel);border-radius:16px;padding:20px;max-width:480px;margin:40px auto" onclick="event.stopPropagation()">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:16px">
      <div style="font-family:var(--fh);font-size:14px;font-weight:700;color:var(--xrp);letter-spacing:1px">BULL SCORE EXPLAINED</div>
      <button onclick="hideBullPopup()" style="background:none;border:none;font-size:20px;cursor:pointer;color:var(--muted)">✕</button>
    </div>

    <!-- Live score display -->
    <div style="text-align:center;padding:16px;background:var(--bg);border:1px solid var(--border);border-radius:10px;margin-bottom:16px">
      <div style="font-size:11px;color:var(--muted);letter-spacing:1px;margin-bottom:6px">CURRENT BULL SCORE</div>
      <div id="bullPopupScore" style="font-size:48px;font-weight:800;font-family:var(--fh);color:var(--xrp)">—</div>
      <div id="bullPopupLabel" style="font-size:13px;color:var(--muted);margin-top:4px">out of 1.0</div>
    </div>

    <!-- Component breakdown -->
    <div style="font-size:11px;font-weight:700;color:var(--muted);letter-spacing:1px;margin-bottom:10px">SCORE COMPONENTS</div>
    <div style="display:flex;flex-direction:column;gap:10px;margin-bottom:16px">
      <div>
        <div style="display:flex;justify-content:space-between;margin-bottom:4px">
          <span style="font-size:12px;color:var(--text);font-weight:600">Order Book (OBI) <span style="color:var(--muted);font-weight:400">50%</span></span>
          <span id="bullObiVal" style="font-size:12px;font-weight:700;color:var(--xrp)">—</span>
        </div>
        <div style="height:6px;background:var(--border);border-radius:3px;overflow:hidden">
          <div id="bullObiBar" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div>
        </div>
        <div style="font-size:11px;color:var(--muted);margin-top:3px">Ratio of buy vs sell orders in the live order book</div>
      </div>
      <div>
        <div style="display:flex;justify-content:space-between;margin-bottom:4px">
          <span style="font-size:12px;color:var(--text);font-weight:600">Depth Ratio <span style="color:var(--muted);font-weight:400">30%</span></span>
          <span id="bullDepthVal" style="font-size:12px;font-weight:700;color:var(--xrp)">—</span>
        </div>
        <div style="height:6px;background:var(--border);border-radius:3px;overflow:hidden">
          <div id="bullDepthBar" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div>
        </div>
        <div style="font-size:11px;color:var(--muted);margin-top:3px">Bid depth vs ask depth within 1% of current price</div>
      </div>
      <div>
        <div style="display:flex;justify-content:space-between;margin-bottom:4px">
          <span style="font-size:12px;color:var(--text);font-weight:600">Spread Score <span style="color:var(--muted);font-weight:400">20%</span></span>
          <span id="bullSpreadVal" style="font-size:12px;font-weight:700;color:var(--xrp)">—</span>
        </div>
        <div style="height:6px;background:var(--border);border-radius:3px;overflow:hidden">
          <div id="bullSpreadBar" style="height:100%;width:50%;background:var(--xrp);border-radius:3px;transition:width .5s"></div>
        </div>
        <div style="font-size:11px;color:var(--muted);margin-top:3px">Tight spread = healthy market. Inverse scaled so tight = high score</div>
      </div>
    </div>

    <!-- Formula -->
    <div style="background:var(--bg);border:1px solid var(--border);border-radius:8px;padding:12px;margin-bottom:14px">
      <div style="font-size:10px;font-weight:700;color:var(--muted);letter-spacing:1px;margin-bottom:6px">FORMULA</div>
      <div style="font-family:'Courier New',monospace;font-size:12px;color:var(--text);line-height:1.8">
        Bull Score =<br>
        &nbsp;&nbsp;(OBI_scaled × 50%) +<br>
        &nbsp;&nbsp;(Depth_scaled × 30%) +<br>
        &nbsp;&nbsp;(1 − Spread_scaled × 20%)
      </div>
    </div>

    <!-- Interpretation -->
    <div style="font-size:11px;font-weight:700;color:var(--muted);letter-spacing:1px;margin-bottom:8px">HOW TO READ IT</div>
    <div style="display:flex;flex-direction:column;gap:6px">
      <div style="display:flex;align-items:center;gap:10px"><div style="width:40px;text-align:center;font-size:12px;font-weight:700;color:#00875a">0.7+</div><div style="font-size:12px;color:var(--muted)">Strong buying pressure — HIGH conviction signals</div></div>
      <div style="display:flex;align-items:center;gap:10px"><div style="width:40px;text-align:center;font-size:12px;font-weight:700;color:#22c55e">0.5+</div><div style="font-size:12px;color:var(--muted)">Moderate bullish — MEDIUM conviction signals</div></div>
      <div style="display:flex;align-items:center;gap:10px"><div style="width:40px;text-align:center;font-size:12px;font-weight:700;color:#eab308">0.4+</div><div style="font-size:12px;color:var(--muted)">Neutral market — LOW conviction signals</div></div>
      <div style="display:flex;align-items:center;gap:10px"><div style="width:40px;text-align:center;font-size:12px;font-weight:700;color:#dc2626">&lt;0.4</div><div style="font-size:12px;color:var(--muted)">Bearish pressure — signals may be risky</div></div>
    </div>
  </div>
</div>

<!-- ══ EXPAND MODALS ══ -->
<!-- Price Modal -->
<div class="modal-overlay" id="modal-price" onclick="closeModal('price')">
  <div class="modal" onclick="event.stopPropagation()">
    <div class="modal-handle"></div>
    <button class="modal-close" onclick="closeModal('price')">✕</button>
    <div class="modal-title">XRP PRICE</div>
    <div class="modal-price" id="modalPrice">—</div>
    <div class="modal-change" id="modalPriceChange">—</div>
    <div class="modal-chart"><canvas id="modalPriceChart"></canvas></div>
    <div class="stat-grid">
      <div class="stat-item"><div class="stat-label">Best Bid</div><div class="stat-val" id="modalBid">—</div></div>
      <div class="stat-item"><div class="stat-label">Best Ask</div><div class="stat-val" id="modalAsk">—</div></div>
      <div class="stat-item"><div class="stat-label">Spread</div><div class="stat-val" id="modalSpread">—</div></div>
      <div class="stat-item"><div class="stat-label">Spread %</div><div class="stat-val" id="modalSpreadPct">—</div></div>
      <div class="stat-item"><div class="stat-label">Bid VWAP</div><div class="stat-val" id="modalBidVwap">—</div></div>
      <div class="stat-item"><div class="stat-label">Ask VWAP</div><div class="stat-val" id="modalAskVwap">—</div></div>
    </div>
  </div>
</div>

<!-- Signal Modal -->
<div class="modal-overlay" id="modal-signal" onclick="closeModal('signal')">
  <div class="modal" onclick="event.stopPropagation()">
    <div class="modal-handle"></div>
    <button class="modal-close" onclick="closeModal('signal')">✕</button>
    <div class="modal-title">MARKET SIGNAL DETAIL</div>
    <div style="font-family:var(--fh);font-size:32px;font-weight:800;margin-bottom:8px" id="modalSignalText">—</div>
    <div class="stat-grid">
      <div class="stat-item"><div class="stat-label">Bull Score</div><div class="stat-val" id="modalBullScore">—</div></div>
      <div class="stat-item"><div class="stat-label">OBI</div><div class="stat-val" id="modalObi">—</div></div>
      <div class="stat-item"><div class="stat-label">Smooth OBI</div><div class="stat-val" id="modalSmoothObi">—</div></div>
      <div class="stat-item"><div class="stat-label">OBI Scaled</div><div class="stat-val" id="modalObiScaled">—</div></div>
      <div class="stat-item"><div class="stat-label">Depth Scaled</div><div class="stat-val" id="modalDepthScaled">—</div></div>
      <div class="stat-item"><div class="stat-label">Spread Scaled</div><div class="stat-val" id="modalSpreadScaled">—</div></div>
    </div>
    <div style="margin-top:12px">
      <div class="ptitle">DEPTH TIERS</div>
      <table style="width:100%;font-size:12px;border-collapse:collapse" id="modalDepthTable"></table>
    </div>
  </div>
</div>

<!-- Bull Score Modal -->
<div class="modal-overlay" id="modal-bull" onclick="closeModal('bull')">
  <div class="modal" onclick="event.stopPropagation()">
    <div class="modal-handle"></div>
    <button class="modal-close" onclick="closeModal('bull')">✕</button>
    <div class="modal-title">BULL SCORE HISTORY</div>
    <div style="font-family:var(--fh);font-size:32px;font-weight:800;color:var(--xrp);margin-bottom:4px" id="modalBullVal">—</div>
    <div style="font-size:12px;color:var(--muted);margin-bottom:16px">Composite signal strength [0 = bearish · 1 = bullish]</div>
    <div class="modal-chart"><canvas id="modalBullChart"></canvas></div>
    <div class="stat-grid" style="margin-top:12px">
      <div class="stat-item"><div class="stat-label">OBI Weight</div><div class="stat-val">50%</div></div>
      <div class="stat-item"><div class="stat-label">Depth Weight</div><div class="stat-val">30%</div></div>
      <div class="stat-item"><div class="stat-label">Spread Weight</div><div class="stat-val">20%</div></div>
      <div class="stat-item"><div class="stat-label">Signal</div><div class="stat-val" id="modalBullSignal">—</div></div>
    </div>
    <div style="margin-top:14px;background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm);padding:14px">
      <div class="ptitle" style="margin-bottom:8px">HOW BULL SCORE IS CALCULATED</div>
      <div style="font-size:12px;color:var(--muted);line-height:1.7;font-weight:500">
        <div style="margin-bottom:8px">The Bull Score combines three real-time order book signals into a single number between <strong style="color:var(--text)">0</strong> (fully bearish) and <strong style="color:var(--text)">1</strong> (fully bullish):</div>
        <div style="margin-bottom:6px">📊 <strong style="color:var(--text)">Order Book Imbalance (50%)</strong> — Compares total bid vs ask volume. More buyers than sellers = higher score.</div>
        <div style="margin-bottom:6px">📉 <strong style="color:var(--text)">Depth Ratio (30%)</strong> — Measures cumulative buy vs sell orders within ±1% of current price. Stronger bid-side depth = higher score.</div>
        <div style="margin-bottom:10px">↔️ <strong style="color:var(--text)">Inverse Spread (20%)</strong> — A tighter bid/ask spread means a more liquid, active market. Tighter spread = higher score.</div>
        <div style="margin-bottom:8px">Each input is scaled against the last 40 readings so the score reflects <em>current conditions relative to recent history</em> — not an absolute value.</div>
        <div style="background:var(--panel);border:1px solid var(--border);border-radius:6px;padding:10px;font-family:var(--fh);font-size:10px;letter-spacing:.5px">
          <div style="color:var(--green);margin-bottom:3px">0.65+ → BUY / STRONG BUY</div>
          <div style="color:var(--muted);margin-bottom:3px">0.40 – 0.65 → HOLD</div>
          <div style="color:var(--red)">Below 0.40 → SELL / STRONG SELL</div>
        </div>
      </div>
    </div>
  </div>
</div>

<!-- OBI Modal -->
<div class="modal-overlay" id="modal-obi" onclick="closeModal('obi')">
  <div class="modal" onclick="event.stopPropagation()">
    <div class="modal-handle"></div>
    <button class="modal-close" onclick="closeModal('obi')">✕</button>
    <div class="modal-title">ORDER BOOK DEPTH</div>
    <div style="font-family:var(--fh);font-size:32px;font-weight:800;margin-bottom:4px" id="modalObiVal">—</div>
    <div style="font-size:12px;color:var(--muted);margin-bottom:16px">[-1 = max sell pressure · +1 = max buy pressure]</div>
    <div class="gauge-wrap" style="margin-bottom:16px">
      <div class="gauge-track"><div class="gauge-thumb" id="modalGaugeThumb" style="left:50%"></div></div>
      <div class="gauge-labels"><span style="color:var(--red)">SELL</span><span style="color:var(--muted)">NEUTRAL</span><span style="color:var(--green)">BUY</span></div>
    </div>
    <div class="stat-grid">
      <div class="stat-item"><div class="stat-label">Bid Volume</div><div class="stat-val" id="modalBidVol">—</div></div>
      <div class="stat-item"><div class="stat-label">Ask Volume</div><div class="stat-val" id="modalAskVol">—</div></div>
      <div class="stat-item"><div class="stat-label">Smooth OBI</div><div class="stat-val" id="modalSmoothObiVal">—</div></div>
      <div class="stat-item"><div class="stat-label">Sources</div><div class="stat-val" id="modalSources">—</div></div>
    </div>
    <div style="margin-top:12px;padding:12px;background:var(--bg);border:1px solid var(--border);border-radius:var(--radius-sm)">
      <div style="font-size:12px;font-weight:700;color:var(--xrp);margin-bottom:8px;font-family:var(--fh);letter-spacing:1px">WHAT IS OBI?</div>
      <div style="font-size:13px;color:var(--muted);line-height:1.7">
        OBI measures the balance between buy and sell orders sitting in the live order book.<br/><br/>
        <strong style="color:var(--text)">Formula:</strong> (Bid Volume &minus; Ask Volume) &divide; (Bid Volume + Ask Volume)<br/><br/>
        <span style="color:var(--green);font-weight:600">Positive (+)</span> &nbsp;More buyers than sellers &mdash; buying pressure<br/>
        <span style="color:var(--red);font-weight:600">Negative (&minus;)</span> &nbsp;More sellers than buyers &mdash; selling pressure<br/><br/>
        <strong style="color:var(--text)">Smooth OBI</strong> averages the last 4 readings to filter out sudden spikes and show the underlying trend.<br/><br/>
        <span style="color:var(--yellow);font-weight:600">&#9888; Note:</span> OBI shows <em>intent</em> not <em>completed trades</em>. Large traders can place fake orders (spoofing) to manipulate readings. Always use alongside Bull Score and Signal.
      </div>
    </div>
    <div style="margin-top:12px">
      <div class="ptitle">DEPTH AT PRICE LEVELS</div>
      <table style="width:100%;font-size:12px;border-collapse:collapse" id="modalObiDepthTable"></table>
    </div>
  </div>
</div>

</div><!-- .root -->

<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.3/dist/chart.umd.min.js"></script>
<script>
const API='',POLL=15000,MXPT=80;
let pChart,oChart,mPriceChart,mBullChart;
let prevPrice=null,cdTimer,cdVal=POLL/1000;
let priceH=[],labelH=[],bullH=[],obiH=[];
let lastSnap=null;
let demoMode=true;

// ── Demo data ──
const DEMO_SIGNALS=[
  {id:'d1',side:'BUY',price:1.3920,xrp_qty:35.91,usd_amount:50,level_idx:2,level_label:'Level 3 of 10',
   level_low:1.380,level_high:1.392,stop_price:1.3224,target_price:1.6008,
   confidence:'HIGH',conf_color:'#00875a',obi:0.22,bull_score:0.71,
   signal:'BUY',signal_color:'#00875a',ts:new Date(Date.now()-45000).toISOString(),status:'pending',mode:'paper'},
  {id:'d2',side:'SELL',price:1.4100,xrp_qty:35.46,usd_amount:50,level_idx:5,level_label:'Level 6 of 10',
   level_low:1.404,level_high:1.416,stop_price:1.3395,target_price:1.6215,
   confidence:'MEDIUM',conf_color:'#d97706',obi:-0.08,bull_score:0.44,
   signal:'HOLD',signal_color:'#eab308',ts:new Date(Date.now()-12000).toISOString(),status:'pending',mode:'paper'}
];
const DEMO_MKT={mid_price:1.3920,best_bid:1.3919,best_ask:1.3921,spread:0.0002,spread_pct:0.014,
  obi:0.18,smooth_obi:0.14,bid_vol:48200,ask_vol:38100,bull_score:0.67,bid_vwap:1.3915,ask_vwap:1.3925,
  signal:'BUY',signal_color:'#00875a',sources:['DEMO'],ts:new Date().toISOString(),
  top_bids:[{price:1.3919,qty:4200},{price:1.3918,qty:6800},{price:1.3917,qty:3100},{price:1.3916,qty:5500},{price:1.3915,qty:8200},{price:1.3914,qty:2900},{price:1.3913,qty:4100},{price:1.3912,qty:3600}],
  top_asks:[{price:1.3921,qty:3800},{price:1.3922,qty:5200},{price:1.3923,qty:4600},{price:1.3924,qty:6100},{price:1.3925,qty:3300},{price:1.3926,qty:4900},{price:1.3927,qty:7200},{price:1.3928,qty:2800}]};

// ── Theme ──
function isDark(){return document.documentElement.classList.contains('dark')}
function applyTheme(dark){
  document.documentElement.classList.toggle('dark',dark);
  document.getElementById('themeBtn').textContent=dark?'☀️ Light':'🌙 Dark';
  localStorage.setItem('xrp-theme',dark?'dark':'light');
  updateChartTheme();
}
function toggleTheme(){applyTheme(!isDark())}
(function(){if(localStorage.getItem('xrp-theme')==='dark')applyTheme(true);})();

// ── Tabs ──
function switchTab(t){
  document.querySelectorAll('.tab').forEach((el,i)=>el.classList.toggle('active',['signals','market','grid','portfolio'][i]===t));
  document.querySelectorAll('.pane').forEach(p=>p.classList.remove('active'));
  document.getElementById('pane-'+t).classList.add('active');
}

// ── Clock ──
function tick(){document.getElementById('clock').textContent=new Date().toLocaleTimeString([],{hour:'2-digit',minute:'2-digit',second:'2-digit'});}
setInterval(tick,1000);tick();

// ── Countdown ──
function startCd(){
  cdVal=POLL/1000;clearInterval(cdTimer);
  cdTimer=setInterval(()=>{cdVal=Math.max(0,cdVal-1);document.getElementById('cfill').style.width=(cdVal/(POLL/1000)*100)+'%';},1000);
}

// ── Charts ──
Chart.defaults.font.family="'Plus Jakarta Sans',sans-serif";Chart.defaults.font.size=11;

function chartColors(){
  const dk=isDark();
  return{
    grid:dk?'#1a2535':'#eef2f7',
    text:dk?'#6b82a0':'#64748b',
    tipBg:dk?'#0a1020':'#1e293b',
    tipBrd:dk?'#2a3f5f':'#0f172a',
    tipTxt:dk?'#e2eaf5':'#f8fafc',
    price:dk?'#4d8eff':'#0033AD',
    priceAlpha:dk?'rgba(77,142,255,.15)':'rgba(0,51,173,.1)',
    bull:dk?'#fbbf24':'#d97706',
    buyBar:dk?'rgba(0,232,122,.7)':'rgba(0,135,90,.6)',
    sellBar:dk?'rgba(255,68,102,.7)':'rgba(220,38,38,.6)',
    holdBar:dk?'rgba(251,191,36,.55)':'rgba(217,119,6,.5)',
  };
}

function makeLineDataset(label,color,alpha){
  const C=chartColors();
  const ctx=document.createElement('canvas').getContext('2d');
  const g=ctx.createLinearGradient(0,0,0,180);
  g.addColorStop(0,alpha||C.priceAlpha);g.addColorStop(1,'rgba(0,0,0,0)');
  return{label,data:[],borderColor:color||C.price,backgroundColor:g,borderWidth:2,pointRadius:1.5,tension:.3,fill:true};
}

function initCharts(){
  const C=chartColors();
  const pc=document.getElementById('priceChart').getContext('2d');
  pChart=new Chart(pc,{type:'line',data:{labels:[],datasets:[
    makeLineDataset('Price'),
    {label:'Bid VWAP',data:[],borderColor:isDark()?'rgba(0,232,122,.4)':'rgba(0,135,90,.4)',borderWidth:1.5,borderDash:[4,3],pointRadius:0,tension:.3,fill:false},
    {label:'Ask VWAP',data:[],borderColor:isDark()?'rgba(255,68,102,.4)':'rgba(220,38,38,.4)',borderWidth:1.5,borderDash:[4,3],pointRadius:0,tension:.3,fill:false},
    {label:'Buy ▲',data:[],type:'scatter',backgroundColor:isDark()?'rgba(0,232,122,.9)':'rgba(0,135,90,.9)',pointRadius:7,pointStyle:'triangle',showLine:false},
    {label:'Sell ▼',data:[],type:'scatter',backgroundColor:isDark()?'rgba(255,68,102,.9)':'rgba(220,38,38,.9)',pointRadius:7,pointStyle:'triangle',rotation:180,showLine:false},
  ]},options:{responsive:true,maintainAspectRatio:false,animation:{duration:400},interaction:{mode:'index',intersect:false},
    plugins:{legend:{display:true,position:'top',labels:{color:C.text,boxWidth:8,padding:8,font:{size:9}}},
      tooltip:{backgroundColor:C.tipBg,borderColor:C.tipBrd,borderWidth:1,titleColor:C.tipTxt,bodyColor:C.tipTxt,callbacks:{label:c=>` ${c.dataset.label}: $${c.parsed.y?.toFixed(5)??'—'}`}}},
    scales:{x:{grid:{color:C.grid},ticks:{maxTicksLimit:5,color:C.text}},y:{grid:{color:C.grid},ticks:{color:C.text,callback:v=>'$'+v.toFixed(4)}}}}});

  const oc=document.getElementById('obiChart').getContext('2d');
  oChart=new Chart(oc,{type:'bar',data:{labels:[],datasets:[
    {label:'OBI',data:[],backgroundColor:[],borderRadius:3,borderWidth:0},
    {label:'Bull',data:[],type:'line',borderColor:C.bull,borderWidth:2,pointRadius:0,tension:.4,fill:false,yAxisID:'y2'},
  ]},options:{responsive:true,maintainAspectRatio:false,animation:{duration:300},
    plugins:{legend:{display:true,position:'top',labels:{color:C.text,boxWidth:8,padding:8,font:{size:9}}},
      tooltip:{backgroundColor:C.tipBg,borderColor:C.tipBrd,borderWidth:1,titleColor:C.tipTxt,bodyColor:C.tipTxt}},
    scales:{x:{display:false},y:{grid:{color:C.grid},ticks:{color:C.text,count:5},min:-1,max:1},
      y2:{position:'right',grid:{display:false},ticks:{color:C.bull,count:5},min:0,max:1}}}});
}

function updateChartTheme(){
  if(!pChart||!oChart)return;
  const C=chartColors();
  pChart.data.datasets[0].borderColor=C.price;
  const g=pChart.ctx.createLinearGradient(0,0,0,180);g.addColorStop(0,C.priceAlpha);g.addColorStop(1,'rgba(0,0,0,0)');
  pChart.data.datasets[0].backgroundColor=g;
  pChart.data.datasets[1].borderColor=isDark()?'rgba(0,232,122,.4)':'rgba(0,135,90,.4)';
  pChart.data.datasets[2].borderColor=isDark()?'rgba(255,68,102,.4)':'rgba(220,38,38,.4)';
  pChart.data.datasets[3].backgroundColor=isDark()?'rgba(0,232,122,.9)':'rgba(0,135,90,.9)';
  pChart.data.datasets[4].backgroundColor=isDark()?'rgba(255,68,102,.9)':'rgba(220,38,38,.9)';
  [pChart,oChart].forEach(ch=>{
    ch.options.scales.x&&(ch.options.scales.x.grid.color=C.grid,ch.options.scales.x.ticks.color=C.text);
    ch.options.scales.y&&(ch.options.scales.y.grid.color=C.grid,ch.options.scales.y.ticks.color=C.text);
    ch.options.plugins.legend.labels.color=C.text;
    ch.options.plugins.tooltip.backgroundColor=C.tipBg;ch.options.plugins.tooltip.borderColor=C.tipBrd;ch.options.plugins.tooltip.titleColor=C.tipTxt;ch.options.plugins.tooltip.bodyColor=C.tipTxt;
  });
  oChart.data.datasets[1].borderColor=C.bull;
  oChart.options.scales.y2.ticks.color=C.bull;
  pChart.update('none');oChart.update('none');
}

function barColor(obi){const C=chartColors();return obi>.15?C.buyBar:obi<-.15?C.sellBar:C.holdBar;}

// ── Helpers ──
const fmt=(n,d=5)=>n!=null?Number(n).toFixed(d):'—';
const fmtU=n=>n!=null?'$'+Number(n).toFixed(2):'—';
const fmtK=n=>n>=1e6?(n/1e6).toFixed(2)+'M':n>=1e3?(n/1e3).toFixed(1)+'K':n?.toFixed(0)??'—';
const pColor=v=>v>0?'var(--green)':v<0?'var(--red)':'var(--muted)';

// ── Render market ──
function renderMarket(d){
  lastSnap=d;
  // Tiles
  // Drive speedometer gauge
  const gaugeMap={'STRONG BUY':{pct:0.92,color:'#00875a'},'BUY':{pct:0.72,color:'#059669'},
    'HOLD':{pct:0.50,color:'#eab308'},'SELL':{pct:0.28,color:'#ef4444'},'STRONG SELL':{pct:0.08,color:'#dc2626'}};
  const gm=gaugeMap[d.signal]||gaugeMap['HOLD'];
  // Conviction adjusts needle slightly within each zone
  const convAdj={'HIGH':0,'MEDIUM':-0.08,'LOW':-0.15,'NEUTRAL':0};
  const adj=d.signal.includes('BUY')?(convAdj[d.conviction]||0):d.signal.includes('SELL')?-(convAdj[d.conviction]||0):0;
  const pct=Math.max(0.05,Math.min(0.95,gm.pct+adj));
  const angle=(pct*180)-180; // -180 (full left) to 0 (full right)
  const rad=angle*Math.PI/180;
  const nx=60+46*Math.cos(rad);
  const ny=52+46*Math.sin(rad);
  const gNeedle=document.getElementById('gaugeNeedle');
  const gDot=document.getElementById('gaugeDot');
  const gLabel=document.getElementById('gaugeLabel');
  const gConv=document.getElementById('gaugeConv');
  if(gNeedle){gNeedle.setAttribute('x2',nx.toFixed(1));gNeedle.setAttribute('y2',ny.toFixed(1));gNeedle.setAttribute('stroke',gm.color);}
  if(gDot)gDot.setAttribute('fill',gm.color);
  if(gLabel){gLabel.textContent=d.signal;gLabel.style.color=gm.color;}
  if(gConv)gConv.textContent=d.conviction&&d.conviction!=='NEUTRAL'?d.conviction+' CONVICTION':'';
  // Update tile accent
  const tile=document.getElementById('tile-signal');
  tile.className='tile tile-'+(d.signal.includes('BUY')?'buy':d.signal.includes('SELL')?'sell':'hold');
  document.getElementById('tileSignalSub').textContent='OBI: '+(d.obi>=0?'+':'')+fmt(d.obi,4);
  // Conviction shown in gauge label
  const mp=document.getElementById('tilePrice');mp.textContent='$'+fmt(d.mid_price,4);
  // Show 24h change if available, otherwise show tick change
  const el=document.getElementById('tilePriceSub');
  if(d.change_24h!=null){
    const pct=d.change_24h;
    const absChange=Math.abs(d.mid_price*(pct/100)).toFixed(4);
    el.textContent=(pct>=0?'▲ +':'▼ ')+Math.abs(pct).toFixed(2)+'% ($'+(pct>=0?'+':'')+d.mid_price*(pct/100)).toFixed(4)+')';
    el.style.color=mp.style.color=pct>=0?'var(--green)':'var(--red)';
  } else if(prevPrice!=null){
    const df=d.mid_price-prevPrice;
    el.textContent=(df>=0?'▲ +':'▼ ')+fmt(df,5);
    el.style.color=mp.style.color=df>=0?'var(--green)':'var(--red)';
  }
  prevPrice=d.mid_price;
  const bs=d.bull_score,bsEl=document.getElementById('tileBull');
  bsEl.textContent=fmt(bs,3);bsEl.style.color=bs>.6?'var(--green)':bs<.4?'var(--red)':'var(--yellow)';
  const ov=document.getElementById('tileObi');ov.textContent=(d.obi>=0?'+':'')+fmt(d.obi,4);
  ov.style.color=d.obi>0?'var(--green)':d.obi<0?'var(--red)':'var(--text)';
  document.getElementById('tileObiSmooth').textContent=(d.smooth_obi>=0?'+':'')+fmt(d.smooth_obi,4);
  // Token Sentiment
  if(d.token_sentiment!=null){
    const ts=d.token_sentiment;
    const fngPanel=document.getElementById('fngPanel');
    if(fngPanel)fngPanel.style.display='block';
    const fngEl=document.getElementById('fngValue');
    const fngLbl=document.getElementById('fngLabel');
    const fngThumb=document.getElementById('fngThumb');
    const tsColor=d.token_sentiment_color||'#eab308';
    if(fngEl){fngEl.textContent=Math.round(ts);fngEl.style.color=tsColor;}
    if(fngLbl){fngLbl.textContent=d.token_sentiment_label||'—';fngLbl.style.color=tsColor;}
    if(fngThumb)fngThumb.style.left=ts+'%';
    // Update title with token name
    const titleEl=document.getElementById('sentimentTitle');
    if(titleEl)titleEl.textContent=(window.PRODUCT_ID||'XRP').replace('-USD','')+' MARKET SENTIMENT';
    // Component bars
    const sc=d.sentiment_components||{};
    const compColor=(v)=>v>=60?'#00875a':v>=45?'#eab308':'#dc2626';
    ['obi','bull','mom','vol'].forEach((k,i)=>{
      const key=['obi','bull','momentum','volume'][i];
      const val=sc[key]||50;
      const bar=document.getElementById('sc_'+k);
      const txt=document.getElementById('sv_'+k);
      if(bar){bar.style.width=val+'%';bar.style.background=compColor(val);}
      if(txt){txt.textContent=Math.round(val);txt.style.color=compColor(val);}
    });
    // BTC reference
    const btcVal=document.getElementById('fngBtcValue');
    const btcLbl=document.getElementById('fngBtcLabel');
    if(btcVal&&d.fear_greed_value!=null){
      const btcColor=d.fear_greed_value<=25?'#dc2626':d.fear_greed_value<=45?'#f97316':d.fear_greed_value<=55?'#eab308':d.fear_greed_value<=75?'#22c55e':'#00875a';
      btcVal.textContent=d.fear_greed_value;btcVal.style.color=btcColor;
      if(btcLbl){btcLbl.textContent=d.fear_greed_classification||'—';btcLbl.style.color=btcColor;}
    }
    // Divergence signal
    const divEl=document.getElementById('sentimentDivergence');
    if(divEl&&d.fear_greed_value!=null){
      const diff=ts-d.fear_greed_value;
      if(Math.abs(diff)>20){
        divEl.style.display='block';
        divEl.textContent=diff>0?
          `⚡ Token sentiment ${Math.round(diff)} pts above BTC — token-specific opportunity`:
          `⚠️ Token sentiment ${Math.round(Math.abs(diff))} pts below BTC — token underperforming`;
      } else {
        divEl.style.display='none';
      }
    }
  }
  // Market tab
  document.getElementById('gaugeThumb').style.left=((d.obi+1)/2*100).toFixed(1)+'%';
  document.getElementById('bidVol').textContent=fmtK(d.bid_vol);
  document.getElementById('askVol').textContent=fmtK(d.ask_vol);
  document.getElementById('srcRow').innerHTML=(d.sources||[]).map(s=>`<div class="src-badge"><span style="width:6px;height:6px;border-radius:50%;background:var(--green);display:inline-block;flex-shrink:0"></span>${s}</div>`).join('');
  renderBook(d.top_bids||[],d.top_asks||[]);
}

function renderBook(bids,asks){
  const mx=Math.max(...bids.map(b=>b.qty),...asks.map(a=>a.qty),1);
  const rows=(ords,cls,col)=>ords.map(o=>{const bw=(o.qty/mx*100).toFixed(1);
    return `<tr class="ob-${cls}"><td>$${Number(o.price).toFixed(5)}</td><td>${fmtK(o.qty)}</td><td style="position:relative;min-width:40px"><div class="dbar" style="width:${bw}%;background:${col}"></div>${bw}%</td></tr>`;
  }).join('');
  document.getElementById('bidsBody').innerHTML=rows(bids,'bid','var(--green)');
  document.getElementById('asksBody').innerHTML=rows(asks,'ask','var(--red)');
}

function addToCharts(d,isBuy,isSell){
  const ts=new Date(d.ts).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit',second:'2-digit'});
  if(priceH.length>=MXPT){
    priceH.shift();labelH.shift();bullH.shift();obiH.shift();
    pChart.data.labels.shift();pChart.data.datasets.forEach(ds=>ds.data.shift());
    oChart.data.labels.shift();oChart.data.datasets[0].data.shift();oChart.data.datasets[0].backgroundColor.shift();oChart.data.datasets[1].data.shift();
  }
  priceH.push(d.mid_price);labelH.push(ts);bullH.push(d.bull_score);obiH.push(d.obi);
  pChart.data.labels.push(ts);
  pChart.data.datasets[0].data.push(d.mid_price);
  pChart.data.datasets[1].data.push(d.bid_vwap);
  pChart.data.datasets[2].data.push(d.ask_vwap);
  pChart.data.datasets[3].data.push(isBuy?{x:ts,y:d.mid_price}:null);
  pChart.data.datasets[4].data.push(isSell?{x:ts,y:d.mid_price}:null);
  pChart.update('active');
  oChart.data.labels.push(ts);oChart.data.datasets[0].data.push(d.obi);
  oChart.data.datasets[0].backgroundColor.push(barColor(d.obi));
  oChart.data.datasets[1].data.push(d.bull_score);
  oChart.update('active');
}

// ── Expand modals ──
function expandTile(type){
  const d=lastSnap||DEMO_MKT;
  if(type==='price'){
    document.getElementById('modalPrice').textContent='$'+fmt(d.mid_price);
    document.getElementById('modalPrice').style.color='var(--xrp)';
    if(prevPrice!=null){
      const df=d.mid_price-prevPrice;
      const el=document.getElementById('modalPriceChange');
      el.textContent=(df>=0?'▲ +':'▼ ')+fmt(df,5)+' USD';
      el.style.color=df>=0?'var(--green)':'var(--red)';
    }
    document.getElementById('modalBid').textContent='$'+fmt(d.best_bid);
    document.getElementById('modalAsk').textContent='$'+fmt(d.best_ask);
    document.getElementById('modalSpread').textContent='$'+fmt(d.spread,5);
    document.getElementById('modalSpreadPct').textContent=fmt(d.spread_pct,4)+'%';
    document.getElementById('modalBidVwap').textContent='$'+fmt(d.bid_vwap);
    document.getElementById('modalAskVwap').textContent='$'+fmt(d.ask_vwap);
    // Mini price chart in modal
    setTimeout(()=>{
      if(mPriceChart)mPriceChart.destroy();
      const C=chartColors();
      const ctx=document.getElementById('modalPriceChart').getContext('2d');
      const g=ctx.createLinearGradient(0,0,0,200);g.addColorStop(0,C.priceAlpha);g.addColorStop(1,'rgba(0,0,0,0)');
      mPriceChart=new Chart(ctx,{type:'line',data:{labels:labelH.slice(-40),datasets:[{label:'Price',data:priceH.slice(-40),borderColor:C.price,backgroundColor:g,borderWidth:2,pointRadius:0,tension:.3,fill:true}]},
        options:{responsive:true,maintainAspectRatio:false,animation:{duration:300},plugins:{legend:{display:false}},
          scales:{x:{grid:{color:C.grid},ticks:{maxTicksLimit:5,color:C.text}},y:{grid:{color:C.grid},ticks:{color:C.text,callback:v=>'$'+v.toFixed(4)}}}}});
    },100);
  } else if(type==='signal'){
    const sigEl=document.getElementById('modalSignalText');
    sigEl.textContent=d.signal;sigEl.style.color=d.signal_color;
    document.getElementById('modalBullScore').textContent=fmt(d.bull_score,3);
    document.getElementById('modalObi').textContent=(d.obi>=0?'+':'')+fmt(d.obi,4);
    document.getElementById('modalSmoothObi').textContent=(d.smooth_obi>=0?'+':'')+fmt(d.smooth_obi,4);
    document.getElementById('modalObiScaled').textContent=fmt(d.obi_scaled,3);
    document.getElementById('modalDepthScaled').textContent=fmt(d.depth_scaled,3);
    document.getElementById('modalSpreadScaled').textContent=fmt(d.spread_scaled,3);
    const dt=d.depth_tiers||{};
    document.getElementById('modalDepthTable').innerHTML=
      `<tr style="color:var(--muted)"><th style="text-align:left;padding:4px 6px;font-size:10px">Range</th><th style="text-align:right;padding:4px 6px;font-size:10px;color:var(--green)">Bid XRP</th><th style="text-align:right;padding:4px 6px;font-size:10px;color:var(--red)">Ask XRP</th></tr>`+
      ['0.5','1.0','2.0'].map(k=>{const t=dt[k+'pct']||{};
        return `<tr><td style="padding:5px 6px;border-bottom:1px solid var(--border);font-size:12px;font-weight:500">±${k}%</td><td style="text-align:right;padding:5px 6px;border-bottom:1px solid var(--border);color:var(--green);font-weight:600">${fmtK(t.bid)}</td><td style="text-align:right;padding:5px 6px;border-bottom:1px solid var(--border);color:var(--red);font-weight:600">${fmtK(t.ask)}</td></tr>`;
      }).join('');
  } else if(type==='bull'){
    document.getElementById('modalBullVal').textContent=fmt(d.bull_score,3);
    document.getElementById('modalBullSignal').textContent=d.signal;
    setTimeout(()=>{
      if(mBullChart)mBullChart.destroy();
      const C=chartColors();
      const ctx=document.getElementById('modalBullChart').getContext('2d');
      mBullChart=new Chart(ctx,{type:'line',data:{labels:labelH.slice(-40),datasets:[
        {label:'Bull Score',data:bullH.slice(-40),borderColor:C.bull,backgroundColor:'rgba(217,119,6,.1)',borderWidth:2,pointRadius:0,tension:.4,fill:true},
        {label:'OBI',data:obiH.slice(-40),borderColor:C.price,borderWidth:1.5,pointRadius:0,tension:.4,fill:false,yAxisID:'y2'},
      ]},options:{responsive:true,maintainAspectRatio:false,animation:{duration:300},interaction:{mode:'index',intersect:false},
        plugins:{legend:{display:true,position:'top',labels:{color:C.text,boxWidth:8,padding:8,font:{size:9}}}},
        scales:{x:{grid:{color:C.grid},ticks:{maxTicksLimit:5,color:C.text}},
          y:{grid:{color:C.grid},ticks:{color:C.bull},min:0,max:1},
          y2:{position:'right',grid:{display:false},ticks:{color:C.price},min:-1,max:1}}}});
    },100);
  } else if(type==='obi'){
    const ov=document.getElementById('modalObiVal');
    ov.textContent=(d.obi>=0?'+':'')+fmt(d.obi,4);
    ov.style.color=d.obi>0?'var(--green)':d.obi<0?'var(--red)':'var(--text)';
    document.getElementById('modalGaugeThumb').style.left=((d.obi+1)/2*100).toFixed(1)+'%';
    document.getElementById('modalBidVol').textContent=fmtK(d.bid_vol)+' XRP';
    document.getElementById('modalAskVol').textContent=fmtK(d.ask_vol)+' XRP';
    document.getElementById('modalSmoothObiVal').textContent=(d.smooth_obi>=0?'+':'')+fmt(d.smooth_obi,4);
    document.getElementById('modalSources').textContent=(d.sources||[]).join(' + ');
    const dt=d.depth_tiers||{};
    document.getElementById('modalObiDepthTable').innerHTML=
      `<tr style="color:var(--muted)"><th style="text-align:left;padding:4px 6px;font-size:10px">Range</th><th style="text-align:right;padding:4px 6px;font-size:10px;color:var(--green)">Bid XRP</th><th style="text-align:right;padding:4px 6px;font-size:10px;color:var(--red)">Ask XRP</th></tr>`+
      ['0.5','1.0','2.0'].map(k=>{const t=dt[k+'pct']||{};
        return `<tr><td style="padding:5px 6px;border-bottom:1px solid var(--border);font-size:12px;font-weight:500">±${k}%</td><td style="text-align:right;padding:5px 6px;border-bottom:1px solid var(--border);color:var(--green);font-weight:600">${fmtK(t.bid)}</td><td style="text-align:right;padding:5px 6px;border-bottom:1px solid var(--border);color:var(--red);font-weight:600">${fmtK(t.ask)}</td></tr>`;
      }).join('');
  }
  document.getElementById('modal-'+type).classList.add('open');
}

function closeModal(type){document.getElementById('modal-'+type).classList.remove('open');}

// ── Signals ──
function renderSignals(signals){
  const el=document.getElementById('signalQueue');
  const badge=document.getElementById('pendingBadge');
  if(!signals||!signals.length){
    badge.style.display='none';
    // Check bot running state from last fetched state
    const botRunning = window._botRunning || false;
    el.innerHTML=`<div class="no-signals"><div class="spinner"></div><div class="no-sig-txt">${botRunning ? 'Watching grid levels… signals appear when price crosses a level.' : 'Bot is stopped. Go to the ⚙️ Grid tab and turn the bot on to start watching.'}</div></div>`;
    return;
  }
  badge.textContent=signals.length;badge.style.display='inline-flex';
  el.innerHTML=signals.map(s=>{
    const isBuy=s.side==='BUY';
    const age=Math.floor((Date.now()-new Date(s.ts).getTime())/1000);
    const ageStr=age<60?age+'s ago':Math.floor(age/60)+'m ago';
    // Position context
    let posContext='',ordersBreakdown='';
    if(s.profit_status&&s.profit_status!=='FIRST TRADE'){
      const bg=s.is_profitable?'var(--green-bg)':'var(--red-bg)';
      const bc=s.is_profitable?'var(--green)':'var(--red)';
      let rows='';
      if(s.side==='SELL'&&s.avg_entry){
        rows=`<div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Avg Buy Price</span><span style="font-size:13px;font-weight:700;color:var(--xrp)">$${fmt(s.avg_entry,5)}</span></div>
        <div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Profit per XRP</span><span style="font-size:13px;font-weight:700;color:${s.profit_color}">${s.profit_per_xrp>=0?'+':''}$${fmt(s.profit_per_xrp,5)} (${s.profit_pct>=0?'+':''}${s.profit_pct}%)</span></div>
        <div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Open position</span><span style="font-size:13px;font-weight:700;color:var(--xrp)">${fmt(s.open_xrp,4)} XRP (${s.open_order_count} orders)</span></div>
        <div style="display:flex;justify-content:space-between;padding:5px 0"><span style="font-size:12px;color:var(--muted)">Est. profit this trade</span><span style="font-size:15px;font-weight:800;color:${s.profit_color}">${s.est_profit>=0?'+':''}$${s.est_profit?.toFixed(2)}</span></div>
        ${!s.is_profitable?'<div style="margin-top:8px;font-size:12px;color:var(--red);font-weight:500">⚠️ Selling below avg buy price. Consider skipping.</div>':''}`;
      } else if(s.side==='BUY'&&s.last_sell_price){
        rows=`<div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Last Sell Price</span><span style="font-size:13px;font-weight:700;color:var(--red)">$${fmt(s.last_sell_price,5)}</span></div>
        <div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Discount vs last sell</span><span style="font-size:13px;font-weight:700;color:${s.profit_color}">${s.profit_per_xrp>=0?'+':''}$${fmt(s.profit_per_xrp,5)} (${s.profit_pct>=0?'+':''}${s.profit_pct}%)</span></div>
        ${s.avg_entry?`<div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Avg entry (all orders)</span><span style="font-size:13px;font-weight:700;color:var(--xrp)">$${fmt(s.avg_entry,5)}</span></div>`:''}
        <div style="display:flex;justify-content:space-between;padding:5px 0;border-bottom:1px solid var(--border)"><span style="font-size:12px;color:var(--muted)">Current position</span><span style="font-size:13px;font-weight:700;color:var(--xrp)">${fmt(s.open_xrp,4)} XRP (${s.open_order_count} orders)</span></div>
        <div style="display:flex;justify-content:space-between;padding:5px 0"><span style="font-size:12px;color:var(--muted)">Est. profit if sold at last sell</span><span style="font-size:15px;font-weight:800;color:${s.profit_color}">${s.est_profit>=0?'+':''}$${s.est_profit?.toFixed(2)}</span></div>`;
      }
      posContext=`<div style="background:${bg};border:1px solid ${bc}40;border-radius:8px;padding:12px;margin:10px 0"><div style="font-size:11px;font-weight:700;color:${bc};letter-spacing:1px;margin-bottom:8px">${s.is_profitable?'✅':'⚠️'} ${s.profit_status}</div>${rows}</div>`;
    }
    if(s.open_orders&&s.open_orders.length>0){
      const hdr=`<div style="display:grid;grid-template-columns:1fr 1fr 1fr ${s.side==='SELL'?'1fr':''};gap:4px;font-size:10px;font-weight:600;color:var(--muted);padding:3px 0;border-bottom:1px solid var(--border);margin-bottom:2px"><div>Level</div><div>Price</div><div>XRP</div>${s.side==='SELL'?'<div>P&L</div>':''}</div>`;
      const rows2=s.open_orders.map(o=>{const pnl=s.side==='SELL'?(s.price-o.price)*o.xrp_qty:null;
        return `<div style="display:grid;grid-template-columns:1fr 1fr 1fr ${pnl!==null?'1fr':''};gap:4px;font-size:12px;padding:5px 0;border-bottom:1px solid var(--border)"><div style="color:var(--muted)">${o.level_label||'L'+(o.level_idx+1)}</div><div style="color:var(--xrp);font-weight:600">$${fmt(o.price,4)}</div><div style="font-weight:500">${fmt(o.xrp_qty,4)}</div>${pnl!==null?`<div style="color:${pnl>=0?'var(--green)':'var(--red)'};font-weight:600">${pnl>=0?'+':''}$${pnl.toFixed(2)}</div>`:''}</div>`;
      }).join('');
      ordersBreakdown=`<div style="margin:8px 0;padding:10px;background:var(--bg);border:1px solid var(--border);border-radius:8px"><div style="font-size:10px;font-weight:700;color:var(--muted);letter-spacing:1px;margin-bottom:6px">OPEN ORDERS</div>${hdr}${rows2}<div style="font-size:12px;color:var(--muted);margin-top:6px">Total: <strong style="color:var(--xrp)">${fmt(s.open_xrp,4)} XRP</strong></div></div>`;
    }
    return `<div class="sig-card ${s.side.toLowerCase()}">
      <div class="sig-hdr">
        <div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap">
          <span class="sig-badge ${s.side.toLowerCase()}">${isBuy?'⬆ BUY':'⬇ SELL'}</span>
          <span style="font-size:12px;color:var(--muted);font-weight:500">${s.level_label}</span>
          ${s.profit_status&&s.profit_status!=='FIRST TRADE'?`<span style="font-size:10px;font-weight:700;padding:2px 8px;border-radius:4px;background:${s.is_profitable?'var(--green-bg)':'var(--red-bg)'};color:${s.profit_color};border:1px solid ${s.profit_color}40">${s.is_profitable?'✅':'⚠️'} ${s.profit_status}</span>`:''}
        </div>
        <span style="font-size:10px;color:var(--muted)">${ageStr} · ${(s.mode||'paper').toUpperCase()}</span>
      </div>
      <div class="sig-price ${s.side.toLowerCase()}">$${fmt(s.price,5)}</div>
      ${posContext}
      ${ordersBreakdown}
      <div class="sig-details">
        <div class="sig-detail"><div class="sig-detail-label">XRP Amount</div><div class="sig-detail-val">${fmt(s.xrp_qty,4)} XRP</div></div>
        <div class="sig-detail"><div class="sig-detail-label">USD Value</div><div class="sig-detail-val">${fmtU(s.usd_amount)}</div></div>
        <div class="sig-detail"><div class="sig-detail-label">Stop Loss</div><div class="sig-detail-val" style="color:var(--red)">$${fmt(s.stop_price,5)}</div></div>
        <div class="sig-detail"><div class="sig-detail-label">Take Profit</div><div class="sig-detail-val" style="color:var(--green)">$${fmt(s.target_price,5)}</div></div>
        <div class="sig-detail"><div class="sig-detail-label">Grid Zone</div><div class="sig-detail-val" style="font-size:12px">$${fmt(s.level_low,4)}–$${fmt(s.level_high,4)}</div></div>
        <div class="sig-detail"><div class="sig-detail-label">Market Signal</div><div class="sig-detail-val" style="color:${s.signal_color}">${s.signal}</div></div>
      </div>
      <div class="sig-meta">
        <span style="font-size:11px;color:var(--muted);font-weight:500">OBI: <strong style="color:${s.obi>0?'var(--green)':'var(--red)'}">${s.obi>=0?'+':''}${fmt(s.obi,4)}</strong></span>
        <span style="font-size:11px;color:var(--muted);font-weight:500">Bull: <strong style="color:${s.bull_score>.6?'var(--green)':s.bull_score<.4?'var(--red)':'var(--yellow)'}">${fmt(s.bull_score,3)}</strong></span>
        <span class="sig-conf" style="background:${s.conf_color}15;color:${s.conf_color};border:1px solid ${s.conf_color}40">CONF: ${s.confidence}</span>
      </div>
      <div class="sig-actions">
        <button class="btn-confirm ${isBuy?'buy':'sell'}-confirm" onclick="confirmSignal('${s.id}')">✅ CONFIRM ${isBuy?'BUY':'SELL'}</button>
        <button class="btn-skip" onclick="skipSignal('${s.id}')">❌ SKIP</button>
      </div>
    </div>`;
  }).join('');
}

function renderGridViz(state){
  const el=document.getElementById('gridViz');
  if(!el)return;
  el.style.position='relative';
  el.style.overflow='hidden';
  const lines=state.grid_lines||[];
  if(!lines.length){el.innerHTML='<div style="display:flex;align-items:center;justify-content:center;height:100%;color:var(--muted);font-size:13px">Configure grid above</div>';return;}
  const prices=lines.map(l=>l.price);
  const minP=Math.min(...prices),maxP=Math.max(...prices),rangeP=maxP-minP||1;
  const curP=state.market?.mid_price||0;
  const gridRange=document.getElementById('gridPriceRange');
  if(gridRange)gridRange.textContent='$'+fmt(minP,4)+' — $'+fmt(maxP,4);
  let html='';
  lines.forEach(l=>{
    const topPct=100-((l.price-minP)/rangeP*100);
    const cls=l.has_buy?'has-buy':l.has_sell?'has-sell':'';
    html+=`<div class="grid-line" style="top:${topPct}%"></div><div class="grid-line-label ${cls}" style="top:${topPct}%">${l.has_buy?'🟢':l.has_sell?'🔴':'·'} $${fmt(l.price,5)}</div>`;
  });
  if(curP>=minP&&curP<=maxP){
    const ct=100-((curP-minP)/rangeP*100);
    html+=`<div class="price-cursor" style="top:${ct}%"></div><div class="price-tag" style="top:${ct}%">$${fmt(curP,5)}</div>`;
  }
  el.innerHTML=html;
}

function renderPortfolio(pf){
  if(!pf)return;
  const pfCash=document.getElementById('pfCash');
  if(pfCash)pfCash.textContent=fmtU(pf.cash_usd);
  const pfXrp=document.getElementById('pfXrp');
  if(pfXrp)pfXrp.textContent=fmt(pf.xrp_held,4)+' XRP';
  const pfXrpVal=document.getElementById('pfXrpVal');
  if(pfXrpVal)pfXrpVal.textContent=fmtU(pf.xrp_value_usd);
  const pfTotal=document.getElementById('pfTotal');
  if(pfTotal)pfTotal.textContent=fmtU(pf.total_value);
  const ur=pf.unrealized_pnl,re=pf.realized_pnl;
  document.getElementById('pfUnreal').textContent=(ur>=0?'+':'')+fmtU(ur);document.getElementById('pfUnreal').style.color=pColor(ur);
  document.getElementById('pfReal').textContent=(re>=0?'+':'')+fmtU(re);document.getElementById('pfReal').style.color=pColor(re);
  document.getElementById('pfAvg').textContent=pf.avg_entry?'$'+fmt(pf.avg_entry,5):'—';
  document.getElementById('pfCur').textContent=pf.current_price?'$'+fmt(pf.current_price,5):'—';
  const lastSellEl=document.getElementById('pfLastSell');
  if(lastSellEl)lastSellEl.textContent=pf.last_sell_price?'$'+fmt(pf.last_sell_price,5):'—';
  const lastBuyEl=document.getElementById('pfLastBuy');
  if(lastBuyEl)lastBuyEl.textContent=pf.last_buy_price?'$'+fmt(pf.last_buy_price,5):'—';
  // Open orders breakdown
  const panel=document.getElementById('pfOpenOrdersPanel');
  const ordersEl=document.getElementById('pfOpenOrders');
  const countEl=document.getElementById('pfOpenCount');
  const totalEl=document.getElementById('pfOpenTotal');
  if(panel&&ordersEl&&pf.open_orders&&pf.open_orders.length>0){
    panel.style.display='block';
    if(countEl)countEl.textContent=pf.open_orders.length+' orders';
    const curPrice=pf.current_price||0;
    ordersEl.innerHTML=pf.open_orders.map(o=>{
      const pnl=(curPrice-o.price)*o.xrp_qty;
      return `<div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:4px;font-size:12px;padding:6px 0;border-bottom:1px solid var(--border)">
        <div style="color:var(--muted)">${o.level_label||'L'+(o.level_idx+1)}</div>
        <div style="color:var(--xrp);font-weight:600">$${fmt(o.price,4)}</div>
        <div style="font-weight:500">${fmt(o.xrp_qty,4)}</div>
        <div style="color:${pnl>=0?'var(--green)':'var(--red)'};font-weight:600">${pnl>=0?'+':''}$${pnl.toFixed(2)}</div>
      </div>`;
    }).join('');
    if(totalEl)totalEl.textContent=fmt(pf.xrp_held,4)+' XRP · Avg $'+fmt(pf.avg_entry,5);
  } else if(panel){
    panel.style.display='none';
  }
}

function renderTradeLog(trades){
  document.getElementById('tradeCount').textContent=trades.length+' trades';
  document.getElementById('tradeLog').innerHTML=trades.length?trades.map(t=>{
    const pnl=t.pnl!=null?(t.pnl>=0?`<span style="color:var(--green);font-weight:700">+$${Math.abs(t.pnl).toFixed(4)}</span>`:`<span style="color:var(--red);font-weight:700">-$${Math.abs(t.pnl).toFixed(4)}</span>`):'';
    const ts=new Date(t.ts).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
    return `<div class="trow"><span class="tbadge t${t.side.toLowerCase()}">${t.side}</span><span style="color:var(--xrp);font-weight:600">$${fmt(t.price,5)}</span><span class="tmeta">${fmt(t.xrp_qty,4)} XRP</span><span class="tmeta">${t.level_label||'—'}</span>${pnl}<span class="tmeta" style="margin-left:auto">${ts}</span></div>`;
  }).join(''):'<div style="text-align:center;padding:20px;color:var(--muted);font-size:13px">No trades yet</div>';
}

function renderBotStatus(s){
  if(!s)return;
  if(s.mode&&s.mode!==currentMode){currentMode=s.mode;setMode(s.mode);}
  // Restore direction from localStorage
  const savedDir=localStorage.getItem('gridDirection')||'both';
  if(savedDir!==currentDirection){currentDirection=savedDir;setDirection(savedDir);}
  // Restore mode from localStorage
  const savedMode=localStorage.getItem('gridMode')||'paper';
  if(s.mode)localStorage.setItem('gridMode',s.mode);
  // Activate button vs status row
  const row=document.getElementById('botStatusRow');
  const btn=document.getElementById('activateBtn');
  const summaryEl=document.getElementById('activateSummary');
  if(row)row.style.display=s.running?'block':'none';
  if(btn){
    btn.style.display=s.running?'none':'block';
    btn.disabled=false;
    btn.style.opacity='1';
  }
  if(summaryEl)summaryEl.style.display=s.running?'none':'block';
  const detail=document.getElementById('botStatusDetail');
  if(detail&&s.config)detail.textContent=`${s.config.levels} levels · $${s.config.lower}–$${s.config.upper} · ${(s.mode||'paper').toUpperCase()} mode`;
  const cb=document.getElementById('cbStat');
  if(cb){
    cb.textContent=s.cb_connected?'CONNECTED ✓':'NOT SET';
    cb.style.color=s.cb_connected?'var(--green)':'var(--red)';
    cb.style.fontWeight='700';
  }
  if(s.config){
    // Only update fields if user is NOT currently editing them
    const activeEl = document.activeElement;
    const editingGrid = activeEl && ['cfgUpper','cfgLower','cfgLevels','cfgStop','cfgTP','cfgAmount'].includes(activeEl.id);
    if(!editingGrid){
      const savedCfg=JSON.parse(localStorage.getItem('gridConfig')||'null');
      document.getElementById('cfgUpper').value=s.config.upper||(savedCfg?.upper)||1.50;
      document.getElementById('cfgLower').value=s.config.lower||(savedCfg?.lower)||1.35;
      document.getElementById('cfgLevels').value=s.config.levels||(savedCfg?.levels)||10;
      document.getElementById('cfgStop').value=s.config.stop_loss_pct||5;
      document.getElementById('cfgTP').value=s.config.take_profit_pct||15;
    }
    const ot=s.config.order_type||'xrp';
    currentOrderType=ot;setOrderType(ot);
    document.getElementById('cfgAmount').value=ot==='xrp'?(s.config.amount_xrp||10):(s.config.amount_usd||50);
    if(!s.running)updateActivateBtn();
  }
}

// ── Actions ──
// toggleBot replaced by activateBot/deactivateBot
function setMode(m){
  if(demoMode){alert('Deploy to cloud to switch modes.');return;}
  currentMode=m;
  const pBtn=document.getElementById('modePaper');
  const lBtn=document.getElementById('modeLive');
  if(pBtn){pBtn.style.borderColor=m==='paper'?'var(--xrp)':'var(--border2)';pBtn.style.color=m==='paper'?'var(--xrp)':'var(--muted)';pBtn.style.background=m==='paper'?'rgba(0,51,173,.08)':'var(--panel)';}
  if(lBtn){lBtn.style.borderColor=m==='live'?'var(--red)':'var(--border2)';lBtn.style.color=m==='live'?'var(--red)':'var(--muted)';lBtn.style.background=m==='live'?'rgba(220,38,38,.08)':'var(--panel)';}
  fetch(API+'/api/bot/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({mode:m})}).then(()=>fetchState());
  updateActivateBtn();
}

let currentMode='paper';
let currentDirection='both';
function setDirection(d){
  currentDirection=d;
  ['dirBoth','dirBuy','dirSell'].forEach(id=>{
    const btn=document.getElementById(id);
    if(!btn)return;
    const key=id.replace('dir','').toLowerCase();
    const isActive=key===d;
    const color=d==='buy'?'var(--green)':d==='sell'?'var(--red)':'var(--xrp)';
    btn.style.borderColor=isActive?color:'var(--border2)';
    btn.style.color=isActive?color:'var(--muted)';
    btn.style.background=isActive?`rgba(${d==='buy'?'0,135,90':d==='sell'?'220,38,38':'0,51,173'},.08)`:'var(--panel)';
  });
  fetch(API+'/api/bot/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({config:{signal_direction:d}})}).catch(()=>{});
  localStorage.setItem('gridDirection', d);
}

function updateGridConfig(){
  const price=lastSnap?.mid_price||1.50;
  const amount=parseFloat(document.getElementById('cfgAmount').value)||10;
  const cfg={
    upper:+document.getElementById('cfgUpper').value||1.55,
    lower:+document.getElementById('cfgLower').value||1.45,
    levels:+document.getElementById('cfgLevels').value||10,
    amount_usd:currentOrderType==='usd'?amount:amount*price,
    amount_xrp:currentOrderType==='xrp'?amount:Math.round(amount/price*10)/10,
    order_type:currentOrderType,
    stop_loss_pct:+document.getElementById('cfgStop').value||5,
    take_profit_pct:+document.getElementById('cfgTP').value||15
  };
  fetch(API+'/api/bot/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({config:cfg})})
  .then(r=>r.json())
  .then(s=>{
    if(s.ok){
      showToast('✅ Config updated!','var(--green)');
      // Save to localStorage for persistence across app switches
      localStorage.setItem('gridConfig', JSON.stringify(cfg));
      localStorage.setItem('gridConfigTs', Date.now());
    } else {showToast('❌ Update failed','var(--red)');}
    fetchState();
  }).catch(e=>showToast('❌ '+e.message,'var(--red)'));
}

function resetGridFields(){
  document.getElementById('cfgLower').value='';
  document.getElementById('cfgUpper').value='';
  document.getElementById('cfgLevels').value='';
  document.getElementById('cfgAmount').value='';
  document.getElementById('cfgStop').value='';
  document.getElementById('cfgTP').value='';
  currentMode='paper';
  setMode('paper');
  updateActivateBtn();
  showToast('Fields cleared','var(--muted)');
}

function showBullPopup(){
  const popup=document.getElementById('bullPopup');
  if(!popup)return;
  popup.style.display='block';
  document.body.style.overflow='hidden';
  // Populate with live data
  const bull=lastSnap?.bull_score||0;
  const obi_s=lastSnap?.obi_scaled||0.5;
  const dep_s=lastSnap?.depth_scaled||0.5;
  const spr_s=lastSnap?.spread_scaled||0.5;
  const scoreEl=document.getElementById('bullPopupScore');
  const labelEl=document.getElementById('bullPopupLabel');
  if(scoreEl){
    scoreEl.textContent=bull.toFixed(3);
    scoreEl.style.color=bull>=0.6?'var(--green)':bull>=0.4?'var(--yellow)':'var(--red)';
  }
  if(labelEl)labelEl.textContent=bull>=0.6?'Strong Bullish':bull>=0.5?'Moderate Bullish':bull>=0.4?'Neutral':'Bearish';
  // Update bars
  const setBar=(id,val)=>{
    const bar=document.getElementById(id+'Bar');
    const txt=document.getElementById(id+'Val');
    if(bar)bar.style.width=(val*100)+'%';
    if(bar)bar.style.background=val>=0.6?'var(--green)':val>=0.4?'var(--yellow)':'var(--red)';
    if(txt)txt.textContent=val.toFixed(3);
    if(txt)txt.style.color=val>=0.6?'var(--green)':val>=0.4?'var(--yellow)':'var(--red)';
  };
  setBar('bullObi',obi_s);
  setBar('bullDepth',dep_s);
  setBar('bullSpread',1-spr_s);
}
function hideBullPopup(){
  const popup=document.getElementById('bullPopup');
  if(popup)popup.style.display='none';
  document.body.style.overflow='';
}

function updateActivateBtn(){
  const lower=parseFloat(document.getElementById('cfgLower')?.value||0);
  const upper=parseFloat(document.getElementById('cfgUpper')?.value||0);
  const levels=parseInt(document.getElementById('cfgLevels')?.value||0);
  const amount=parseFloat(document.getElementById('cfgAmount')?.value||0);
  const btn=document.getElementById('activateBtn');
  const summary=document.getElementById('activateSummary');
  const price=lastSnap?.mid_price||1.41;
  const usdVal=currentOrderType==='xrp'?(amount*price).toFixed(2):amount.toFixed(2);
  // Progress bar
  const steps=[lower>0&&upper>0&&upper>lower,levels>=2,amount>0,true];
  ['prog1','prog2','prog3','prog4'].forEach((id,i)=>{const el=document.getElementById(id);if(el)el.style.background=steps[i]?'var(--xrp)':'var(--border2)';});
  if(!btn)return;
  const allValid=lower>0&&upper>lower&&levels>=2&&amount>0;
  if(allValid){
    const modeLabel=currentMode==='live'?'🔴 LIVE MODE':'📝 PAPER MODE';
    btn.style.background=currentMode==='live'?'#dc2626':'var(--xrp)';
    btn.style.color='#fff';btn.style.cursor='pointer';
    btn.textContent=`▶ ACTIVATE BOT · ${modeLabel}`;
    if(summary)summary.textContent=`${amount} ${currentOrderType.toUpperCase()} · $${lower}–$${upper} · ${levels} levels · ~$${usdVal}/order`;
  } else {
    btn.style.background='var(--border2)';btn.style.color='var(--muted)';btn.style.cursor='not-allowed';
    btn.textContent='▶ ACTIVATE BOT';
    if(summary)summary.textContent='Fill in all fields to activate';
  }
}

function activateBot(){
  const lower=parseFloat(document.getElementById('cfgLower')?.value||0);
  const upper=parseFloat(document.getElementById('cfgUpper')?.value||0);
  if(!lower||!upper||upper<=lower){alert('Please set a valid price range first.');return;}
  if(currentMode==='live'){
    fetch(API+'/api/bot/state').then(r=>r.json()).then(s=>{
      if(!s.cb_connected){alert('Coinbase API not connected. Cannot activate LIVE mode.');}
      else{_doActivate();}
    });
  } else {
    _doActivate();
  }
}

function _doActivate(){
  const amount=document.getElementById('cfgAmount').value;
  const unit=currentOrderType.toUpperCase();
  const lower=document.getElementById('cfgLower').value;
  const upper=document.getElementById('cfgUpper').value;
  if(currentMode==='live'){
    if(!confirm(`⚠️ LIVE MODE\n\nThis will place REAL orders on Coinbase Advanced.\n\nAmount: ${amount} ${unit} per order\nRange: $${lower} – $${upper}\n\nAre you sure?`))return;
  }
  const btn=document.getElementById('activateBtn');
  if(btn){btn.textContent='⏳ ACTIVATING...';btn.style.opacity='0.7';btn.disabled=true;}
  // Set a timeout to reset button if something goes wrong
  const resetBtn=()=>{
    if(btn){btn.textContent=`▶ ACTIVATE BOT · ${currentMode==='live'?'🔴 LIVE MODE':'📝 PAPER MODE'}`;btn.style.opacity='1';btn.disabled=false;}
  };
  const timeout=setTimeout(()=>{resetBtn();showToast('⚠️ Activation timed out','var(--yellow)');},8000);
  const price=lastSnap?.mid_price||1.50;
  const cfg={
    upper:+document.getElementById('cfgUpper').value||1.55,
    lower:+document.getElementById('cfgLower').value||1.45,
    levels:+document.getElementById('cfgLevels').value||10,
    amount_usd:currentOrderType==='usd'?+amount:(+amount*price),
    amount_xrp:currentOrderType==='xrp'?+amount:Math.round(+amount/price*10)/10,
    order_type:currentOrderType,
    stop_loss_pct:+document.getElementById('cfgStop').value||5,
    take_profit_pct:+document.getElementById('cfgTP').value||15
  };
  fetch(API+'/api/bot/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({mode:currentMode,config:cfg})})
  .then(r=>r.json())
  .then(cfgRes=>{
    if(!cfgRes.ok)throw new Error('Config failed');
    return fetch(API+'/api/bot/start',{method:'POST'});
  })
  .then(r=>r.json())
  .then(startRes=>{
    clearTimeout(timeout);
    resetBtn();
    if(startRes.ok){
      showToast('✅ Bot activated!','var(--green)');
      // Force UI to show BOT ACTIVE immediately without waiting for fetchState
      const row=document.getElementById('botStatusRow');
      const btn=document.getElementById('activateBtn');
      const summaryEl=document.getElementById('activateSummary');
      if(row)row.style.display='block';
      if(btn)btn.style.display='none';
      if(summaryEl)summaryEl.style.display='none';
      const detail=document.getElementById('botStatusDetail');
      if(detail)detail.textContent=`${document.getElementById('cfgLevels').value} levels · $${document.getElementById('cfgLower').value}–$${document.getElementById('cfgUpper').value} · ${currentMode.toUpperCase()} mode`;
      setTimeout(()=>fetchState(),1000);
    } else {
      throw new Error('Start failed');
    }
  })
  .catch(e=>{
    clearTimeout(timeout);
    showToast('❌ '+e.message,'var(--red)');
    resetBtn();
  });
}

function deactivateBot(){
  fetch(API+'/api/bot/stop',{method:'POST'})
  .then(r=>r.json())
  .then(s=>{
    window._botRunning=false;
    // Immediately update UI
    const row=document.getElementById('botStatusRow');
    const btn=document.getElementById('activateBtn');
    const summaryEl=document.getElementById('activateSummary');
    if(row)row.style.display='none';
    if(btn)btn.style.display='block';
    if(summaryEl)summaryEl.style.display='block';
    showToast('⏹ Bot stopped','var(--red)');
    setTimeout(()=>fetchState(),500);
  }).catch(e=>showToast('❌ '+e.message,'var(--red)'));
}

let currentOrderType='xrp';
function setOrderType(type){
  currentOrderType=type;
  const usdBtn=document.getElementById('toggleUSD');
  const xrpBtn=document.getElementById('toggleXRP');
  const unit=document.getElementById('cfgAmountUnit');
  const inp=document.getElementById('cfgAmount');
  if(type==='usd'){
    if(usdBtn){usdBtn.style.background='var(--xrp)';usdBtn.style.color='#fff';}
    if(xrpBtn){xrpBtn.style.background='none';xrpBtn.style.color='var(--muted)';}
    if(unit)unit.textContent='USD';
    if(inp){inp.step='5';inp.value=50;}
  } else {
    if(xrpBtn){xrpBtn.style.background='var(--xrp)';xrpBtn.style.color='#fff';}
    if(usdBtn){usdBtn.style.background='none';usdBtn.style.color='var(--muted)';}
    if(unit)unit.textContent='XRP';
    if(inp){inp.step='1';inp.value=35;}
  }
}
function saveConfig(){
  const amt=+document.getElementById('cfgAmount').value;
  const cfg={upper:+document.getElementById('cfgUpper').value,lower:+document.getElementById('cfgLower').value,
    levels:+document.getElementById('cfgLevels').value,
    amount_usd: currentOrderType==='usd'?amt:amt*1.41,
    amount_xrp: currentOrderType==='xrp'?amt:Math.round(amt/1.41*10)/10,
    order_type: currentOrderType,
    stop_loss_pct:+document.getElementById('cfgStop').value,take_profit_pct:+document.getElementById('cfgTP').value};
  if(cfg.upper<=cfg.lower){showToast('⚠️ Upper price must be greater than lower price','var(--red)');return;}
  if(demoMode){showToast('⚠️ Demo mode — deploy to cloud to save config','var(--yellow)');return;}
  const btn=document.getElementById('saveBtn');
  btn.textContent='⏳ SAVING...';btn.disabled=true;
  fetch(API+'/api/bot/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({config:cfg})})
    .then(r=>r.json())
    .then(r=>{
      btn.textContent='✅ SAVED!';
      setTimeout(()=>{btn.textContent='💾 SAVE & APPLY';btn.disabled=false;},2000);
      fetchState();
      showToast('✅ Grid config saved and applied','var(--green)');
    })
    .catch(()=>{
      btn.textContent='❌ FAILED';
      setTimeout(()=>{btn.textContent='💾 SAVE & APPLY';btn.disabled=false;},2000);
      showToast('❌ Failed to save config','var(--red)');
    });
}
function loadConfig(){
  if(demoMode){showToast('⚠️ Demo mode — no config to reload','var(--yellow)');return;}
  const btn=document.getElementById('reloadBtn');
  btn.textContent='⏳ LOADING...';btn.disabled=true;
  fetchState().then(()=>{
    btn.textContent='✅ RELOADED!';
    setTimeout(()=>{btn.textContent='↺ RELOAD';btn.disabled=false;},2000);
    showToast('✅ Config reloaded from server','var(--green)');
  }).catch(()=>{
    btn.textContent='❌ FAILED';
    setTimeout(()=>{btn.textContent='↺ RELOAD';btn.disabled=false;},2000);
  });
}

function confirmSignal(id){
  if(demoMode){
    const card=document.querySelector(`[onclick="confirmSignal('${id}')"]`)?.closest('.sig-card');
    if(card){card.style.opacity='0';card.style.transition='opacity .3s';setTimeout(()=>{const i=DEMO_SIGNALS.findIndex(s=>s.id===id);if(i>-1)DEMO_SIGNALS.splice(i,1);renderSignals(DEMO_SIGNALS);showToast('✅ Demo trade executed','var(--green)');},300);}
    return;
  }
  fetch(API+'/api/bot/confirm',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({signal_id:id})})
    .then(r=>r.json()).then(r=>{
      if(r.ok){
        showToast('✅ Trade executed!','var(--green)');
        fetchState();
      } else {
        showToast('❌ '+(r.msg||'Failed — check logs'),'var(--red)');
        console.error('Confirm failed:',r);
        fetchState();
      }
    }).catch(e=>{showToast('❌ Network error','var(--red)');console.error(e);});
}
function skipSignal(id){
  if(demoMode){
    const card=document.querySelector(`[onclick="skipSignal('${id}')"]`)?.closest('.sig-card');
    if(card){card.style.opacity='0';card.style.transition='opacity .25s';setTimeout(()=>{const i=DEMO_SIGNALS.findIndex(s=>s.id===id);if(i>-1)DEMO_SIGNALS.splice(i,1);renderSignals(DEMO_SIGNALS);},260);}
    return;
  }
  fetch(API+'/api/bot/skip',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({signal_id:id})}).then(()=>fetchState());
}

function showToast(msg,color){
  const t=document.createElement('div');
  t.style.cssText=`position:fixed;bottom:24px;left:50%;transform:translateX(-50%);background:${color};color:#fff;padding:12px 24px;border-radius:8px;font-family:var(--fh);font-size:11px;font-weight:700;z-index:9999;box-shadow:0 4px 12px rgba(0,0,0,.2)`;
  t.textContent=msg;document.body.appendChild(t);setTimeout(()=>t.remove(),3000);
}

// ── Status ──
function setStatus(live,txt){
  document.getElementById('liveDot').className='live-dot'+(live?' on':'');
  document.getElementById('liveTxt').textContent=txt;
}

// ── Fetch ──
async function fetchMarket(){
  try{
    const d=await fetch('/api/latest',{cache:'no-store'}).then(r=>r.json());
    if(d&&d.mid_price){
      demoMode=false;
      document.getElementById('demoBanner').style.display='none';
      setStatus(true,'LIVE · COINBASE + KRAKEN');
      renderMarket(d);
      addToCharts(d,d.signal==='BUY'||d.signal==='STRONG BUY',d.signal==='SELL'||d.signal==='STRONG SELL');
      startCd();
    }
  }catch(e){setStatus(false,demoMode?'DEMO MODE':'CONNECTING…');}
}
async function fetchState(){
  fetch('/api/bot/state',{cache:'no-store'})
  .then(r=>r.json())
  .then(s=>{
    if(!s||!s.portfolio)return;
    demoMode=false;
    window._botRunning = s.running || false;
    const cbEl=document.getElementById('cbStat');
    if(cbEl){
      cbEl.textContent=s.cb_connected?'CONNECTED ✓':'NOT SET';
      cbEl.style.color=s.cb_connected?'var(--green)':'var(--red)';
      cbEl.style.fontWeight='700';
    }
    renderSignals(s.pending||[]);
    renderGridViz(s);
    renderPortfolio(s.portfolio);
    renderTradeLog(s.trade_log||[]);
    renderBotStatus(s);
    if(s.config){
      document.getElementById('cfgUpper').value=s.config.upper||1.60;
      document.getElementById('cfgLower').value=s.config.lower||1.20;
      document.getElementById('cfgLevels').value=s.config.levels||10;
      const ot=s.config.order_type||'xrp';
      currentOrderType=ot;
      setOrderType(ot);
      document.getElementById('cfgAmount').value=ot==='xrp'?(s.config.amount_xrp||10):(s.config.amount_usd||50);
      updateActivateBtn();
      document.getElementById('cfgStop').value=s.config.stop_loss_pct||5;
      document.getElementById('cfgTP').value=s.config.take_profit_pct||15;
    }
  }).catch(e=>console.error('fetchState error:',e));
}

// ── Range selector ──
let currentRange=20;
function setRange(n){
  currentRange=n;
  document.querySelectorAll('.rbtn').forEach(b=>b.classList.remove('active'));
  const map={20:'r20',40:'r40',80:'r80'};
  const btn=document.getElementById(map[n]);
  if(btn)btn.classList.add('active');
  // Slice chart data to selected range
  const slice=Math.min(n,priceH.length);
  const labels=labelH.slice(-slice);
  const prices=priceH.slice(-slice);
  pChart.data.labels=labels;
  pChart.data.datasets[0].data=prices;
  pChart.data.datasets[1].data=pChart.data.datasets[1].data.slice(-slice);
  pChart.data.datasets[2].data=pChart.data.datasets[2].data.slice(-slice);
  pChart.data.datasets[3].data=pChart.data.datasets[3].data.slice(-slice);
  pChart.data.datasets[4].data=pChart.data.datasets[4].data.slice(-slice);
  pChart.update();
}

// ── Init ──
initCharts();
// Use server-injected data if available
(function initFromServer(){
  if(window.__LIVE__&&window.__SNAP__&&window.__SNAP__.mid_price){
    demoMode=false;
    document.getElementById('demoBanner').style.display='none';
    setStatus(true,'LIVE · COINBASE + KRAKEN');
    renderMarket(window.__SNAP__);
    if(window.__HIST__&&window.__HIST__.length){
      pChart.data.labels=[];pChart.data.datasets.forEach(ds=>ds.data=[]);
      oChart.data.labels=[];oChart.data.datasets[0].data=[];
      oChart.data.datasets[0].backgroundColor=[];oChart.data.datasets[1].data=[];
      priceH=[];labelH=[];bullH=[];obiH=[];
      for(const h of window.__HIST__)addToCharts(h,false,false);
      pChart.update();oChart.update();
    }
    startCd();
  } else {
    // No live data yet — show empty state, not demo signals
    renderSignals([]);
    renderPortfolio({cash_usd:1000,xrp_held:0,avg_entry:0,realized_pnl:0,xrp_value_usd:0,total_value:1000,unrealized_pnl:0,current_price:0});
  }
})();
// ── Push Notifications ──
const VAPID_PUBLIC = '__VAPID_PUBLIC__';
async function enableNotifications(){
  const btn=document.getElementById('notifBtn');
  if(btn){btn.textContent='⏳ Enabling...';btn.disabled=true;}
  try {
    if(!('serviceWorker' in navigator)||!('PushManager' in window)){
      showToast('❌ Push not supported on this browser','var(--red)');
      if(btn){btn.textContent='🔔 ALERTS';btn.disabled=false;}
      return;
    }
    const reg = await navigator.serviceWorker.register('/sw.js');
    await navigator.serviceWorker.ready;
    const existing = await reg.pushManager.getSubscription();
    if(existing){
      // Already subscribed - just re-send to server
      await fetch('/api/bot/subscribe',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({subscription:existing.toJSON()})});
      if(btn){btn.textContent='🔔 ALERTS ON';btn.style.color='var(--green)';btn.style.borderColor='var(--green)';btn.disabled=false;}
      showToast('🔔 Alerts already active!','var(--green)');
      return;
    }
    const permission = await Notification.requestPermission();
    if(permission !== 'granted'){
      showToast('❌ Notification permission denied','var(--red)');
      if(btn){btn.textContent='🔔 ALERTS';btn.disabled=false;}
      return;
    }
    const sub = await reg.pushManager.subscribe({
      userVisibleOnly: true,
      applicationServerKey: VAPID_PUBLIC
    });
    await fetch('/api/bot/subscribe',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({subscription:sub.toJSON()})});
    if(btn){btn.textContent='🔔 ALERTS ON';btn.style.color='var(--green)';btn.style.borderColor='var(--green)';btn.disabled=false;}
    showToast('🔔 Signal notifications enabled!','var(--green)');
  } catch(e) {
    console.error('Enable notifications error:', e);
    if(btn){btn.textContent='🔔 ALERTS';btn.disabled=false;}
    showToast('❌ '+e.message,'var(--red)');
  }
}

async function initPushNotifications(manual=false){
  if(!('serviceWorker' in navigator)||!('PushManager' in window)){
    console.log('Push not supported');return;
  }
  try {
    const reg = await navigator.serviceWorker.register('/sw.js');
    console.log('SW registered');
    const permission = await Notification.requestPermission();
    if(permission !== 'granted'){console.log('Push permission denied');return;}
    const existing = await reg.pushManager.getSubscription();
    if(existing){
      await fetch('/api/bot/subscribe',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({subscription:existing.toJSON()})});
      console.log('Push re-subscribed');
      return;
    }
    const sub = await reg.pushManager.subscribe({
      userVisibleOnly: true,
      applicationServerKey: VAPID_PUBLIC
    });
    await fetch('/api/bot/subscribe',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({subscription:sub.toJSON()})});
    console.log('Push subscribed!');
    showToast('🔔 Signal notifications enabled!','var(--green)');
    const btn=document.getElementById('notifBtn');
    if(btn){btn.textContent='🔔 ALERTS ON';btn.style.color='var(--green)';btn.style.borderColor='var(--green)';}
  } catch(e){
    console.error('Push init error:',e);
    const btn=document.getElementById('notifBtn');
    if(btn){btn.textContent='🔔 ENABLE ALERTS';btn.disabled=false;}
    if(manual)showToast('❌ Notifications failed: '+e.message,'var(--red)');
  }
}
// Check push status on load
setTimeout(async()=>{
  if(!('serviceWorker' in navigator)||!('PushManager' in window))return;
  try{
    const reg = await navigator.serviceWorker.register('/sw.js');
    await navigator.serviceWorker.ready;
    const existing = await reg.pushManager.getSubscription();
    if(existing){
      await fetch('/api/bot/subscribe',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({subscription:existing.toJSON()})});
      const btn=document.getElementById('notifBtn');
      if(btn){btn.textContent='🔔 ALERTS ON';btn.style.color='var(--green)';btn.style.borderColor='var(--green)';}
    }
  }catch(e){console.log('SW check:',e);}
}, 2000);

// Background fetch + polling
fetchMarket();fetchState();
setInterval(async function(){
  await fetchMarket();
  await fetchState();
},POLL);
</script>
</body>
</html>
"""

# ─── HTTP Handler ─────────────────────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        path=self.path.split("?")[0]
        if path in ("/",""):
            # Inject build ID AND live data directly — no JS fetch needed
            html = DASHBOARD_HTML.replace(
                '<meta charset="UTF-8"/>',
                f'<meta charset="UTF-8"/><meta name="build-id" content="{BUILD_ID}"/>'
            )
            html = html.replace("'__VAPID_PUBLIC__'", f"'{VAPID_PUBLIC_KEY}'" if VAPID_PUBLIC_KEY else "''")
            # Inject live snapshot as global JS var so page renders live immediately
            with state_lock:
                snap = latest_snapshot
                hist = list(history)[-40:]
            if snap and snap.get('mid_price'):
                inject = f"""<script>
window.__LIVE__ = true;
window.__SNAP__ = {json.dumps(snap)};
window.__HIST__ = {json.dumps(hist)};
</script>"""
            else:
                inject = '<script>window.__LIVE__ = false;</script>'
            html = html.replace('</head>', inject + '</head>')
            self._send(200,"text/html; charset=utf-8",html.encode())
        elif path=="/api/latest":
            with state_lock: self._json(latest_snapshot)
        elif path=="/api/history":
            with state_lock: self._json(list(history))
        elif path=="/api/bot/state":
            self._json(full_state())
        elif path=="/sw.js":
            sw_code = """self.addEventListener('push',function(e){const d=e.data?e.data.json():{};e.waitUntil(self.registration.showNotification(d.title||'XRP Grid Bot',{body:d.body||'New signal',icon:'/favicon.ico',tag:'signal',renotify:true,data:d.data||{}}));});self.addEventListener('notificationclick',function(e){e.notification.close();e.waitUntil(clients.openWindow('/'));});"""
            self.send_response(200)
            self.send_header('Content-Type','application/javascript')
            self.send_header('Service-Worker-Allowed','/')
            self.send_header('Cache-Control','no-cache')
            self.end_headers()
            self.wfile.write(sw_code.encode())
        elif path=="/health":
            self._json({"ok":True,"running":grid["running"],"mode":grid["mode"]})
        else:
            self._send(404,"text/plain",b"Not found")

    def do_POST(self):
        path=self.path.split("?")[0]
        n=int(self.headers.get("Content-Length",0))
        body=json.loads(self.rfile.read(n)) if n else {}
        if path=="/api/bot/portfolio":
            # Manual portfolio sync
            with grid_lock:
                pf = grid["portfolio"]
                if "cash_usd" in body: pf["cash_usd"] = float(body["cash_usd"])
                if "xrp_held" in body: pf["xrp_held"] = float(body["xrp_held"])
                if "avg_entry" in body: pf["avg_entry"] = float(body["avg_entry"])
                if "last_buy_price" in body: pf["last_buy_price"] = float(body["last_buy_price"])
                if "last_sell_price" in body: pf["last_sell_price"] = float(body["last_sell_price"])
                log.info(f"Portfolio manually synced: cash=${pf['cash_usd']} xrp={pf['xrp_held']} avg=${pf['avg_entry']}")
            self._json({"ok":True,"portfolio":grid["portfolio"]})
        elif path=="/api/bot/subscribe":
            sub = body.get("subscription")
            if sub and sub not in push_subscriptions:
                push_subscriptions.append(sub)
                log.info(f"Push subscription added. Total: {len(push_subscriptions)}")
            self._json({"ok": True, "count": len(push_subscriptions)})
        elif path=="/api/bot/unsubscribe":
            sub = body.get("subscription")
            if sub in push_subscriptions:
                push_subscriptions.remove(sub)
            self._json({"ok": True})
        elif path=="/api/bot/test_signal":
            side = body.get("side","BUY").upper()
            with grid_lock:
                snap = latest_snapshot
                price = snap.get("mid_price",0) or 1.41
                lines = grid["grid_lines"]
                level_idx = max(1, len(lines)//2)
                level_low  = lines[level_idx-1] if level_idx>0 and lines else round(price*0.99,5)
                level_high = lines[level_idx]   if level_idx<len(lines) and lines else round(price*1.01,5)
                sig = make_signal(side, price, level_idx, level_low, level_high, snap)
                sig["label"] = "TEST SIGNAL"
                grid["pending"].append(sig)
                log.info(f"[TEST] Injected {side} signal @ ${price:.5f}")
                send_push_notification(
                    f"{'🟢 BUY' if side=='BUY' else '🔴 SELL'} Signal @ ${price:.4f}",
                    f"{sig.get('level_label','Grid')} · {sig.get('conviction','—')} conviction",
                    {"signal_id": sig["id"], "side": side}
                )
            self._json({"ok":True,"signal_id":sig["id"],"price":price,"side":side})
        elif path=="/api/bot/start":
            with grid_lock: grid["running"]=True
            log.info("Bot STARTED"); self._json({"ok":True})
        elif path=="/api/bot/stop":
            with grid_lock: grid["running"]=False
            log.info("Bot STOPPED"); self._json({"ok":True})
        elif path=="/api/bot/config":
            with grid_lock:
                if "config" in body: grid["config"].update(body["config"]); recompute_grid()
                if "mode" in body:
                    if body["mode"]=="live" and not CB_API_KEY:
                        self._json({"ok":False,"error":"No Coinbase API keys"}); return
                    grid["mode"]=body["mode"]
            self._json({"ok":True})
        elif path=="/api/bot/confirm":
            signal_id=body.get("signal_id","")
            ok,msg=confirm_signal(signal_id)
            if not ok:
                with grid_lock:
                    pending_ids=[s["id"] for s in grid["pending"] if s["status"]=="pending"]
                log.warning(f"Confirm FAILED id={signal_id} msg={msg} pending={pending_ids}")
            else:
                log.info(f"Confirm OK id={signal_id} mode={grid['mode']}")
            self._json({"ok":ok,"msg":msg})
        elif path=="/api/bot/skip":
            ok=skip_signal(body.get("signal_id",""))
            self._json({"ok":ok})
        else:
            self._send(404,"text/plain",b"Not found")

    def _json(self,data):
        self._send(200,"application/json",json.dumps(data).encode())

    def _send(self,code,ct,body):
        self.send_response(code)
        self.send_header("Content-Type",ct)
        self.send_header("Content-Length",len(body))
        self.send_header("Access-Control-Allow-Origin","*")
        # Aggressive no-cache for HTML so iPhone always gets latest version
        if "html" in ct:
            self.send_header("Cache-Control","no-store, no-cache, must-revalidate, max-age=0")
            self.send_header("Pragma","no-cache")
            self.send_header("Expires","0")
            self.send_header("X-Build-ID", BUILD_ID)
            self.send_header("ETag", f'"{BUILD_ID}"')
            self.send_header("Vary", "Accept-Encoding")
        else:
            self.send_header("Cache-Control","no-store")
        self.end_headers()
        self.wfile.write(body)

    def log_message(self,*_): pass

def run_http():
    srv=HTTPServer(("0.0.0.0",PORT),Handler)
    log.info(f"HTTP on :{PORT}  mode={grid['mode']}  CB={'SET' if CB_API_KEY else 'NOT SET'}")
    srv.serve_forever()

def keep_alive():
    """Ping own /health every 20s to keep container alive and prevent cold starts."""
    time.sleep(10)
    while True:
        try:
            urllib.request.urlopen(f"http://localhost:{PORT}/health", timeout=5)
            log.debug("Keep-alive ping OK")
        except Exception as e:
            log.warning(f"Keep-alive ping failed: {e}")
        time.sleep(20)

if __name__=="__main__":
    with grid_lock:
        recompute_grid()
    threading.Thread(target=run_http, daemon=True).start()
    threading.Thread(target=keep_alive, daemon=True).start()
    log.info(f"XRP Semi-Auto Grid Bot — starting  CB={'SET' if CB_API_KEY else 'NOT SET'}  UPPER={grid['config']['upper']}  LOWER={grid['config']['lower']}")
    asyncio.run(poll_loop())
