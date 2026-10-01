#!/usr/bin/env python3
"""
XAUUSD sweep > MSB > FVG alert script.

Pulls free gold candles from Yahoo Finance, runs the same rules as the EA /
Pine script, and pushes a notification to your phone through ntfy.sh
(free app, no account, no Telegram). You place the pending order yourself
in the MT5 app.

Run:   python3 xauusd_alerts.py
Keep the Mac awake:   caffeinate -i python3 xauusd_alerts.py

Uses only the Python standard library.
"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request

# ======================= SETTINGS =======================
# ntfy topics are PUBLIC by name: anyone who guesses it can read your alerts.
# Make it long and random, e.g. "gold-k82hd91xq7fa". Subscribe to the same
# name in the ntfy phone app.
NTFY_TOPIC = "gold-jjlakey-9k2x7q"

SYMBOL = "GC=F"          # Yahoo gold futures (free). Spot XAUUSD is not reliably available.
ENTRY_INTERVAL = "5m"    # "5m" or "15m"
PRICE_OFFSET = 0.0       # broker price minus feed price; see README note. Added to every level sent.
POLL_SECONDS = 60

EMA_LEN = 50
ATR_LEN = 14
ATR_MULT = 0.5
RR = 2.0
WING = 2
MAX_BARS_MSB = 40
MAX_BARS_PENDING = 15
DEADZONE_PTS = 20
POINT = 0.01             # gold: 2 decimals

STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "alerts_state.json")
INTERVAL_SECONDS = {"5m": 300, "15m": 900}
# ========================================================


def fetch_candles(symbol, interval, rng):
    url = "https://query1.finance.yahoo.com/v8/finance/chart/%s?interval=%s&range=%s" % (
        urllib.parse.quote(symbol), interval, rng)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=20) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    result = data["chart"]["result"][0]
    ts = result["timestamp"]
    q = result["indicators"]["quote"][0]
    out = []
    for i, t in enumerate(ts):
        o, h, l, c = q["open"][i], q["high"][i], q["low"][i], q["close"][i]
        if None in (o, h, l, c):
            continue
        out.append({"t": t, "o": o, "h": h, "l": l, "c": c})
    return out


def drop_forming(candles, seconds):
    """Remove the last candle if it hasn't closed yet (signals use closed candles only)."""
    if candles and candles[-1]["t"] + seconds > time.time():
        return candles[:-1]
    return candles


def ema_series(values, n):
    k = 2.0 / (n + 1)
    out, e = [], None
    for v in values:
        e = v if e is None else v * k + e * (1 - k)
        out.append(e)
    return out


def atr_series(c, n):
    out = [None] * len(c)
    trs = []
    prev_atr = None
    for i, bar in enumerate(c):
        if i == 0:
            tr = bar["h"] - bar["l"]
        else:
            pc = c[i - 1]["c"]
            tr = max(bar["h"] - bar["l"], abs(bar["h"] - pc), abs(bar["l"] - pc))
        trs.append(tr)
        if i == n - 1:
            prev_atr = sum(trs) / float(n)
            out[i] = prev_atr
        elif i >= n:
            prev_atr = (prev_atr * (n - 1) + tr) / float(n)
            out[i] = prev_atr
    return out


def bias_series(entry, hourly, iv_sec):
    """+1 / -1 / 0 per entry candle, using only COMPLETED 1H candles (no lookahead)."""
    closes = [h["c"] for h in hourly]
    em = ema_series(closes, EMA_LEN)
    dz = DEADZONE_PTS * POINT
    out, j = [], -1
    for bar in entry:
        close_time = bar["t"] + iv_sec
        while j + 1 < len(hourly) and hourly[j + 1]["t"] + 3600 <= close_time:
            j += 1
        if j < EMA_LEN:
            out.append(0)
        elif closes[j] > em[j] + dz:
            out.append(1)
        elif closes[j] < em[j] - dz:
            out.append(-1)
        else:
            out.append(0)
    return out


def analyse(c, bias, atr):
    """Replay the state machine over closed candles. Returns a list of events."""
    events = []
    last_sh = last_sl = None
    state = 0
    is_bull = True
    sweep_ext = msb_lvl = entry = sl = tp = None
    sweep_idx = 0
    cnt = 0
    last_fvg = -1

    def ev(t, kind, title, text):
        events.append({"time": c[t]["t"], "kind": kind, "title": title, "text": text})

    for t in range(len(c)):
        # confirm swing pivot at candidate bar p (needs WING bars after it)
        p = t - WING
        if p - WING >= 0:
            hi, lo = c[p]["h"], c[p]["l"]
            if all(hi > c[p - k]["h"] and hi > c[p + k]["h"] for k in range(1, WING + 1)):
                last_sh = hi
            if all(lo < c[p - k]["l"] and lo < c[p + k]["l"] for k in range(1, WING + 1)):
                last_sl = lo

        a = atr[t]
        if a is None:
            continue
        bar = c[t]
        b = bias[t]

        if state == 0:
            if last_sh is not None and last_sl is not None:
                if b == 1 and bar["l"] < last_sl and bar["c"] > last_sl:
                    state, is_bull = 1, True
                    sweep_ext, msb_lvl, sweep_idx, cnt = bar["l"], last_sh, t, 0
                elif b == -1 and bar["h"] > last_sh and bar["c"] < last_sh:
                    state, is_bull = 1, False
                    sweep_ext, msb_lvl, sweep_idx, cnt = bar["h"], last_sl, t, 0

        elif state == 1:
            cnt += 1
            stale = cnt > MAX_BARS_MSB
            failed = bar["c"] < sweep_ext if is_bull else bar["c"] > sweep_ext
            msb = bar["c"] > msb_lvl if is_bull else bar["c"] < msb_lvl
            if stale or failed:
                state = 0
            elif msb:
                n = t - sweep_idx
                f_near, f_idx = None, None
                if n >= 2:
                    for i in range(n - 2, -1, -1):        # oldest -> newest, first gap wins
                        newer, older = c[t - i], c[t - i - 2]
                        if is_bull and newer["l"] > older["h"]:
                            f_near, f_idx = newer["l"], t - i
                            break
                        if (not is_bull) and newer["h"] < older["l"]:
                            f_near, f_idx = newer["h"], t - i
                            break
                if f_near is not None and f_idx != last_fvg:
                    buf = a * ATR_MULT
                    entry = f_near
                    sl = sweep_ext - buf if is_bull else sweep_ext + buf
                    risk = abs(entry - sl)
                    tp = entry + risk * RR if is_bull else entry - risk * RR
                    last_fvg = f_idx
                    state, cnt = 2, 0
                    side = "BUY LIMIT" if is_bull else "SELL LIMIT"
                    ev(t, "setup", "XAUUSD " + side,
                       "%s at %s | SL %s | TP %s" % (side, px(entry), px(sl), px(tp)))
                else:
                    state = 0

        elif state == 2:
            cnt += 1
            filled = bar["l"] <= entry if is_bull else bar["h"] >= entry
            stopped = bar["l"] <= sl if is_bull else bar["h"] >= sl
            if filled:
                state = 3
                ev(t, "filled", "XAUUSD entry reached",
                   "Price reached %s. Your limit order should have filled." % px(entry))
            elif stopped or cnt > MAX_BARS_PENDING:
                state = 0
                ev(t, "cancel", "XAUUSD CANCEL order",
                   "Setup expired/invalid. Delete the pending order at %s." % px(entry))

        elif state == 3:
            hit_sl = bar["l"] <= sl if is_bull else bar["h"] >= sl
            hit_tp = bar["h"] >= tp if is_bull else bar["l"] <= tp
            if hit_sl:
                state = 0
                ev(t, "sl", "XAUUSD stop level hit", "Stop loss level %s was hit." % px(sl))
            elif hit_tp:
                state = 0
                ev(t, "tp", "XAUUSD target level hit", "Take profit level %s was hit." % px(tp))
    return events


def px(x):
    return "%.2f" % (x + PRICE_OFFSET)


def notify(title, message, priority="high"):
    req = urllib.request.Request(
        "https://ntfy.sh/" + NTFY_TOPIC,
        data=message.encode("utf-8"),
        headers={"Title": title, "Priority": priority},
    )
    urllib.request.urlopen(req, timeout=15).read()


def load_last_time():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)["last_time"]
    except Exception:
        return None


def save_last_time(t):
    with open(STATE_FILE, "w") as f:
        json.dump({"last_time": t}, f)


def check_once():
    iv = INTERVAL_SECONDS[ENTRY_INTERVAL]
    entry = drop_forming(fetch_candles(SYMBOL, ENTRY_INTERVAL, "5d"), iv)
    hourly = drop_forming(fetch_candles(SYMBOL, "60m", "1mo"), 3600)
    if len(entry) < 30 or len(hourly) < EMA_LEN + 5:
        print("Not enough data yet.")
        return
    events = analyse(entry, bias_series(entry, hourly, iv), atr_series(entry, ATR_LEN))
    latest = entry[-1]["t"]
    last_time = load_last_time()

    if last_time is None:                       # first run: don't replay old history
        save_last_time(latest)
        notify("XAUUSD alerts started", "Watching %s %s. You will be pinged on new setups." % (
            SYMBOL, ENTRY_INTERVAL), "default")
        print("First run: started watching from now.")
        return

    for e in events:
        fresh = e["time"] > last_time and e["time"] >= latest - 3 * iv   # skip stale, avoid bursts
        if fresh:
            print(time.strftime("%H:%M:%S"), e["title"], "-", e["text"])
            notify(e["title"], e["text"])
    save_last_time(latest)


def main():
    if "CHANGE-ME" in NTFY_TOPIC:
        print("Edit NTFY_TOPIC at the top of this file first (long, random, unique).")
        sys.exit(1)
    if ENTRY_INTERVAL not in INTERVAL_SECONDS:
        print("ENTRY_INTERVAL must be '5m' or '15m'.")
        sys.exit(1)
    print("Watching %s on %s. Ctrl+C to stop." % (SYMBOL, ENTRY_INTERVAL))
    while True:
        try:
            check_once()
        except Exception as ex:
            print("Check failed (will retry):", ex)
        time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    main()
