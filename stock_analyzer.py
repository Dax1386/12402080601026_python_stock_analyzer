"""
================================================================
 Mini Project : Stock Market Data Analyzer
 Concepts used: API Data, Lists, Dictionaries, File Handling, GUI
================================================================

WHAT IT DOES
------------
You type a stock symbol (an Indian one, e.g. RELIANCE.NS, TCS.NS,
INFY.NS, or an index like ^NSEI for NIFTY 50). The program:

  1. Downloads real daily price history from Yahoo Finance
     (free, no API key required)  ->  API Data
  2. Stores the dates and prices in lists and builds a dictionary of
     computed statistics                              -> Lists, Dictionaries
  3. Calculates useful numbers:
        - total return, best/worst day
        - 7-day and 30-day moving averages (SMA)
        - annualised volatility
        - maximum drawdown
        - a simple trend signal (price vs its 30-day average)
  4. Draws a price chart with the moving averages on it
  5. Shows everything in a desktop window (Tkinter GUI)
  6. Can also save / load the data as a CSV file  -> File Handling

HOW TO RUN
----------
    python stock_analyzer.py                # opens the GUI
    python stock_analyzer.py --demo         # works fully offline (no internet)
    python stock_analyzer.py --symbol TCS.NS --chart tcs.png
    python stock_analyzer.py --csv my_prices.csv
    python stock_analyzer.py --search "tata motors"   # find Indian shares by name
    python stock_analyzer.py --find "adani enterprises"  # search + analyze
    python stock_analyzer.py --symbol TCS.NS --range 1d --interval 5m  # intraday
    python stock_analyzer.py --indices    # Nifty / Sensex / Bank Nifty overview

Requirements: only the standard library. matplotlib is OPTIONAL -
if it is installed you get a PNG graph and a chart in the GUI window;
if not, the program prints a text chart instead and still works fully.
    pip install matplotlib        (optional, for the graph)
(The GUI uses tkinter, which ships with Python.)
================================================================
"""

import os
import csv
import sys
import json
import math
import random
import argparse
import statistics
import urllib.request
import urllib.error
import urllib.parse
from datetime import datetime, timedelta, timezone

# ----------------------------------------------------------------
# 1. GETTING THE DATA
# ----------------------------------------------------------------

YAHOO_URL = ("https://query1.finance.yahoo.com/v8/finance/chart/"
             "{symbol}?range={range}&interval={interval}")

# Ready-made symbols shown in the GUI drop-down.
# Indian shares on the NSE end in ".NS"; on the BSE they end in ".BO";
# indices start with "^". Just add any other symbol you need here.
POPULAR_SYMBOLS = [
    "RELIANCE.NS", "TCS.NS", "INFY.NS", "HDFCBANK.NS",
    "ICICIBANK.NS", "SBIN.NS", "ITC.NS", "HINDUNILVR.NS",
    "BHARTIARTL.NS", "LT.NS", "WIPRO.NS", "SUNPHARMA.NS",
    "ADANIENT.NS", "MARUTI.NS", "KOTAKBANK.NS",
    "^NSEI", "^BSESN",
]

SEARCH_URL = ("https://query1.finance.yahoo.com/v1/finance/search?"
              "q={query}&quotesCount=10&newsCount=0")


def is_indian(symbol):
    """True only for Indian listings: NSE (".NS"), BSE (".BO") and
    Indian indices ("^..."). Anything else (NYSE, Nasdaq, foreign
    exchanges) is a global share and is ignored."""
    return symbol.endswith((".NS", ".BO")) or symbol.startswith("^")


def search_symbols(query):
    """Find INDIAN shares by company NAME (e.g. "tata motors").

    Returns a list of matches, each a dictionary:
        {'symbol': str, 'name': str, 'exchange': str}
    Global / foreign listings are filtered out, so only shares traded
    on the NSE or BSE (plus Indian indices) are returned.
    """
    url = SEARCH_URL.format(query=urllib.parse.quote(query))
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urllib.request.urlopen(req, timeout=20) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.URLError as e:
        raise RuntimeError(f"Could not reach the internet: {e}")
    except json.JSONDecodeError:
        raise RuntimeError("The search server sent back data we could not read.")

    matches = []
    for item in payload.get("quotes", []):
        symbol = item.get("symbol")
        if not symbol or not is_indian(symbol):
            continue
        matches.append({
            "symbol": symbol,
            "name": item.get("shortname") or item.get("longname") or symbol,
            "exchange": item.get("exchDisp", ""),
        })
    return matches


# ----------------------------------------------------------------
# 1b. TIMEFRAMES AND INDIAN INDICES
# ----------------------------------------------------------------

# The main Indian indices shown in the "Market indices" box.
INDICES = [
    ("NIFTY 50", "^NSEI"),
    ("SENSEX", "^BSESN"),
    ("BANK NIFTY", "^NSEBANK"),
]

# Ready-made timeframes: (label, Yahoo range, Yahoo interval).
# The first few are intraday, so you can view 1-minute, 15-minute and
# 1-hour candles as well as the usual daily and weekly data.
TIMEFRAMES = [
    ("1 day (1-min candles)", "1d", "1m"),
    ("1 day (5-min candles)", "1d", "5m"),
    ("1 week (15-min candles)", "5d", "15m"),
    ("1 month (1-hour candles)", "1mo", "60m"),
    ("3 months (daily)", "3mo", "1d"),
    ("6 months (daily)", "6mo", "1d"),
    ("1 year (daily)", "1y", "1d"),
    ("2 years (daily)", "2y", "1d"),
    ("5 years (weekly)", "5y", "1wk"),
]

# How many price bars occur in a year - used to annualise volatility
# so the number is meaningful for intraday data too.
PERIODS_PER_YEAR = {
    "1m": 252 * 375, "2m": 252 * 188, "5m": 252 * 75,
    "15m": 252 * 25, "30m": 252 * 13, "60m": 252 * 7,
    "90m": 252 * 4, "1h": 252 * 7, "1d": 252, "5d": 50,
    "1wk": 52, "1mo": 12, "3mo": 4,
}


# Minutes per bar for each interval - used to space the chart's time axis.
INTERVAL_MINUTES = {
    "1m": 1, "2m": 2, "5m": 5, "15m": 15, "30m": 30,
    "60m": 60, "90m": 90, "1h": 60,
}

# The most time labels to draw on the x-axis before spacing them out.
MAX_X_TICKS = 15


def is_intraday(interval):
    """True for anything shorter than a day (minute / hour candles)."""
    return interval not in ("1d", "5d", "1wk", "1mo", "3mo")


def periods_per_year(interval):
    """How many bars of this interval fit in a trading year."""
    return PERIODS_PER_YEAR.get(interval, 252)


def fetch_stock(symbol, range_="1y", interval="1d"):
    """Download price history for a symbol from Yahoo Finance.

    Returns a dictionary:
        {
          'symbol': str, 'currency': str, 'exchange': str,
          'dates':  [ 'YYYY-MM-DD', ... ],
          'closes': [ float, ... ],
          'volumes':[ int, ... ],
        }
    Raises RuntimeError with a friendly message if anything goes wrong.
    """
    url = YAHOO_URL.format(symbol=symbol, range=range_, interval=interval)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})

    try:
        with urllib.request.urlopen(req, timeout=20) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        # HTTPError must be caught before URLError (it is a subclass).
        if e.code == 404:
            raise RuntimeError(
                f"Symbol '{symbol}' was not found. Indian stocks end in .NS "
                f"(e.g. RELIANCE.NS, TCS.NS); indices use ^ (e.g. ^NSEI).")
        raise RuntimeError(f"The data server returned an error (code {e.code}).")
    except urllib.error.URLError as e:
        raise RuntimeError(f"Could not reach the internet: {e}")
    except json.JSONDecodeError:
        raise RuntimeError("The server sent back data we could not read.")

    chart = payload.get("chart", {})
    if chart.get("error"):
        raise RuntimeError(f"Yahoo Finance says: {chart['error'].get('description')}")
    results = chart.get("result")
    if not results:
        raise RuntimeError(f"No data found for symbol '{symbol}'. "
                           "Check the spelling (Indian stocks end in .NS).")

    result = results[0]
    meta = result.get("meta", {})
    stamps = result.get("timestamp", [])
    quote = result["indicators"]["quote"][0]

    # intraday data needs the clock time as well as the date
    date_fmt = "%Y-%m-%d %H:%M" if is_intraday(interval) else "%Y-%m-%d"
    # show times in the exchange's own timezone (e.g. IST for the NSE),
    # not whatever timezone the computer running the program happens to be in
    offset = meta.get("gmtoffset", 0) or 0

    dates, closes, volumes = [], [], []
    for i, ts in enumerate(stamps):
        close = quote["close"][i]
        if close is None:                 # market holidays / missing rows
            continue
        stamp = datetime.fromtimestamp(ts, tz=timezone.utc) + timedelta(seconds=offset)
        dates.append(stamp.strftime(date_fmt))
        closes.append(round(float(close), 2))
        vol = quote["volume"][i]
        volumes.append(int(vol) if vol is not None else 0)

    if not closes:
        raise RuntimeError("The symbol returned no usable price points.")

    return {
        "symbol": meta.get("symbol", symbol),
        "currency": meta.get("currency", ""),
        "exchange": meta.get("fullExchangeName", meta.get("exchangeName", "")),
        "interval": interval,
        "range": range_,
        "dates": dates,
        "closes": closes,
        "volumes": volumes,
    }


# ----------------------------------------------------------------
# 2. FILE HANDLING  (save / load a CSV)
# ----------------------------------------------------------------

def save_csv(data, path):
    """Write the price history to a CSV file."""
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["Date", "Close", "Volume"])
        for d, c, v in zip(data["dates"], data["closes"], data["volumes"]):
            writer.writerow([d, c, v])


def load_csv(path, symbol="(from file)"):
    """Read a price history back from a CSV file."""
    dates, closes, volumes = [], [], []
    with open(path, "r", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            dates.append(row["Date"])
            closes.append(float(row["Close"]))
            volumes.append(int(float(row.get("Volume", 0) or 0)))
    if not closes:
        raise RuntimeError("That CSV file has no rows.")
    return {
        "symbol": symbol, "currency": "", "exchange": "",
        "dates": dates, "closes": closes, "volumes": volumes,
    }


# ----------------------------------------------------------------
# 3. THE ANALYSIS  (Lists + Dictionaries + maths)
# ----------------------------------------------------------------

def simple_moving_average(values, window):
    """Return a list the same length as values, where each entry is the
    average of the last `window` values (None until there are enough)."""
    sma = [None] * len(values)
    running = 0.0
    for i, v in enumerate(values):
        running += v
        if i >= window:
            running -= values[i - window]
        if i >= window - 1:
            sma[i] = running / window
    return sma


def daily_returns(closes):
    """Percentage change from each day to the next."""
    return [(closes[i] - closes[i - 1]) / closes[i - 1] * 100
            for i in range(1, len(closes))]


def max_drawdown(closes):
    """The largest fall from a peak to a later low, as a percentage."""
    peak = closes[0]
    worst = 0.0
    for price in closes:
        peak = max(peak, price)
        drop = (price - peak) / peak * 100
        worst = min(worst, drop)
    return worst


def analyse(data):
    """Compute every statistic and return them in one dictionary."""
    closes = data["closes"]
    dates = data["dates"]
    returns = daily_returns(closes)

    sma7 = simple_moving_average(closes, 7)
    sma30 = simple_moving_average(closes, 30)

    first, last = closes[0], closes[-1]
    total_return = (last - first) / first * 100

    # volatility: standard deviation of the bar returns, scaled to a year
    ppy = periods_per_year(data.get("interval", "1d"))
    vol = statistics.stdev(returns) * math.sqrt(ppy) if len(returns) > 1 else 0.0

    hi = max(closes)
    lo = min(closes)
    best = max(returns) if returns else 0.0
    worst = min(returns) if returns else 0.0

    # trend signal: is today's price above its own 30-day average?
    last_sma30 = sma30[-1]
    if last_sma30 is None:
        trend = "Not enough data for a 30-period trend"
    elif last > last_sma30:
        trend = "UPTREND  (price above its 30-period average)"
    else:
        trend = "DOWNTREND  (price below its 30-period average)"

    return {
        "symbol": data["symbol"],
        "currency": data["currency"],
        "exchange": data["exchange"],
        "interval": data.get("interval", "1d"),
        "start_date": dates[0],
        "end_date": dates[-1],
        "trading_days": len(closes),
        "first_close": first,
        "last_close": last,
        "abs_change": round(last - first, 2),
        "total_return": round(total_return, 2),
        "avg_close": round(statistics.mean(closes), 2),
        "high": hi,
        "high_date": dates[closes.index(hi)],
        "low": lo,
        "low_date": dates[closes.index(lo)],
        "best_day": round(best, 2),
        "worst_day": round(worst, 2),
        "volatility": round(vol, 2),
        "max_drawdown": round(max_drawdown(closes), 2),
        "sma7": round(sma7[-1], 2) if sma7[-1] is not None else None,
        "sma30": round(last_sma30, 2) if last_sma30 is not None else None,
        "trend": trend,
        "sma7_series": sma7,
        "sma30_series": sma30,
    }


def market_overview(indices=None):
    """Latest value and daily % change for the main Indian indices.

    Returns a list of dictionaries: {'name', 'symbol', 'last', 'change'}.
    'last' and 'change' are None if that index could not be loaded.
    """
    rows = []
    for name, symbol in (indices or INDICES):
        try:
            data = fetch_stock(symbol, "5d", "1d")
            closes = data["closes"]
            last = closes[-1]
            prev = closes[-2] if len(closes) > 1 else last
            change = (last - prev) / prev * 100 if prev else 0.0
            rows.append({"name": name, "symbol": symbol,
                         "last": last, "change": round(change, 2)})
        except RuntimeError:
            rows.append({"name": name, "symbol": symbol,
                         "last": None, "change": None})
    return rows


def format_report(stats):
    """Turn the statistics dictionary into a neat text report."""
    cur = stats["currency"]
    intra = is_intraday(stats.get("interval", "1d"))
    bar_word = "bars" if intra else "trading days"
    best_lbl = "Best move" if intra else "Best day"
    worst_lbl = "Worst move" if intra else "Worst day"
    avg_word = "bar" if intra else "day"

    def money(x):
        return f"{x:,.2f} {cur}".strip()

    lines = [
        "=" * 58,
        f"  {stats['symbol']}   ({stats['exchange']})",
        f"  Period: {stats['start_date']}  to  {stats['end_date']}"
        f"   ({stats['trading_days']} {bar_word})",
        "=" * 58,
        "",
        "  PRICE",
        f"    First close ......... {money(stats['first_close'])}",
        f"    Last close .......... {money(stats['last_close'])}",
        f"    Change .............. {stats['abs_change']:+,.2f} {cur}".rstrip(),
        f"    Total return ........ {stats['total_return']:+.2f} %",
        f"    Average close ....... {money(stats['avg_close'])}",
        "",
        "  RANGE",
        f"    Highest ............ {money(stats['high'])}  on {stats['high_date']}",
        f"    Lowest ............. {money(stats['low'])}  on {stats['low_date']}",
        "",
        "  RISK",
        f"    Volatility (annual). {stats['volatility']:.2f} %",
        f"    Max drawdown ....... {stats['max_drawdown']:.2f} %",
        f"    {best_lbl} {'.' * (19 - len(best_lbl))} {stats['best_day']:+.2f} %",
        f"    {worst_lbl} {'.' * (19 - len(worst_lbl))} {stats['worst_day']:+.2f} %",
        "",
        "  TREND",
        f"    7-{avg_word} average ...... {stats['sma7']}",
        f"    30-{avg_word} average ..... {stats['sma30']}",
        f"    Signal ............. {stats['trend']}",
        "=" * 58,
    ]
    return "\n".join(lines)


# ----------------------------------------------------------------
# 4. THE CHART
# ----------------------------------------------------------------

def mpl_available():
    """Return True if matplotlib can be imported (it is optional)."""
    try:
        import matplotlib  # noqa: F401
        return True
    except ImportError:
        return False


def ascii_chart(data, stats, width=66, height=14):
    """Draw a simple price chart using plain text characters, so the
    project still shows a graph when matplotlib is not installed."""
    closes, dates = data["closes"], data["dates"]
    lo, hi = min(closes), max(closes)
    span = (hi - lo) or 1.0

    # squeeze the price series down to `width` columns
    n = len(closes)
    if n >= width:
        step = n / width
        sampled = [closes[int(i * step)] for i in range(width)]
    else:
        sampled = list(closes)
    cols = len(sampled)

    grid = [[" "] * cols for _ in range(height)]
    for x, price in enumerate(sampled):
        row = height - 1 - int(round((price - lo) / span * (height - 1)))
        grid[max(0, min(height - 1, row))][x] = "*"

    margin = 13
    out = [f"  {stats['symbol']} - price chart (text mode)"]
    out.append(f"{hi:>{margin},.2f} |" + "".join(grid[0]))
    for r in grid[1:-1]:
        out.append(" " * margin + " |" + "".join(r))
    out.append(f"{lo:>{margin},.2f} |" + "".join(grid[-1]))
    out.append(" " * margin + " +" + "-" * cols)
    out.append(" " * margin + f"  {dates[0]}  to  {dates[-1]}")
    return "\n".join(out)


def build_chart(data, stats, save_path=None, max_ticks=None):
    """Draw price + moving averages. Saves a PNG if a path is given, and
    also returns the matplotlib Figure (used by the GUI).

    max_ticks controls how many labels the time axis shows. It defaults
    to MAX_X_TICKS; pass a bigger number for a finer time axis.
    """
    if not mpl_available():
        raise RuntimeError("matplotlib is not installed")
    import matplotlib
    matplotlib.use("Agg")                 # safe for saving without a screen
    import matplotlib.pyplot as plt

    date_fmt = ("%Y-%m-%d %H:%M" if is_intraday(data.get("interval", "1d"))
                else "%Y-%m-%d")
    dates = [datetime.strptime(d, date_fmt) for d in data["dates"]]
    fig, ax = plt.subplots(figsize=(10, 5))

    avg_word = "bar" if is_intraday(data.get("interval", "1d")) else "day"
    ax.plot(dates, data["closes"], label="Close price", color="#1f77b4", linewidth=1.4)
    ax.plot(dates, stats["sma7_series"], label=f"7-{avg_word} SMA",
            color="#ff7f0e", linewidth=1.1)
    ax.plot(dates, stats["sma30_series"], label=f"30-{avg_word} SMA",
            color="#d62728", linewidth=1.1)

    ax.set_title(f"{stats['symbol']} - price history")
    ax.set_ylabel(f"Price ({stats['currency']})")
    ax.legend()
    ax.grid(alpha=0.3)

    # ---- space the time axis according to the chosen timeframe ----
    interval = data.get("interval", "1d")
    if is_intraday(interval):
        import matplotlib.dates as mdates
        minutes = INTERVAL_MINUTES.get(interval, 1)
        want = max_ticks or MAX_X_TICKS
        # work out the gap between labels from the real time span, so the
        # spacing stays right for a single day and for several weeks alike
        span_minutes = (dates[-1] - dates[0]).total_seconds() / 60
        step = max(minutes, span_minutes / want)
        # pick the right kind of locator for the size of that gap
        if step < 60:
            locator = mdates.MinuteLocator(interval=max(1, round(step)))
        elif step < 24 * 60:
            locator = mdates.HourLocator(interval=max(1, round(step / 60)))
        else:
            locator = mdates.DayLocator(interval=max(1, round(step / 1440)))
        ax.xaxis.set_major_locator(locator)
        spans_days = dates[0].date() != dates[-1].date()
        ax.xaxis.set_major_formatter(
            mdates.DateFormatter("%d-%b %H:%M" if spans_days else "%H:%M"))
        ax.set_xlabel("Time")
        for label in ax.get_xticklabels():
            label.set_rotation(45)
            label.set_ha("right")
    else:
        ax.set_xlabel("Date")
        fig.autofmt_xdate()

    fig.tight_layout()

    if save_path:
        fig.savefig(save_path, dpi=130)
        print(f"Chart saved to {save_path}")
    return fig


# ----------------------------------------------------------------
# 5. THE GUI
# ----------------------------------------------------------------

def launch_gui():
    """Open the desktop window."""
    import tkinter as tk
    from tkinter import ttk, messagebox
    have_mpl = mpl_available()
    if have_mpl:
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

    root = tk.Tk()
    root.title("Stock Market Data Analyzer")
    root.geometry("1000x720")

    state = {"data": None, "stats": None}

    # --- top control bar ---
    top = ttk.Frame(root, padding=10)
    top.pack(fill="x")

    ttk.Label(top, text="Symbol:").pack(side="left")
    symbol_var = tk.StringVar(value="RELIANCE.NS")
    ttk.Combobox(top, textvariable=symbol_var, values=POPULAR_SYMBOLS,
                 width=14).pack(side="left", padx=4)

    ttk.Label(top, text="Timeframe:").pack(side="left", padx=(10, 0))
    tf_var = tk.StringVar(value="1 year (daily)")
    ttk.Combobox(top, textvariable=tf_var, state="readonly", width=22,
                 values=[t[0] for t in TIMEFRAMES]).pack(side="left")

    status_var = tk.StringVar(value="Enter a symbol and click Analyze.")

    def do_analyze():
        symbol = symbol_var.get().strip().upper()
        status_var.set(f"Downloading {symbol} ...")
        root.update_idletasks()
        try:
            tf = next((t for t in TIMEFRAMES if t[0] == tf_var.get()),
                      ("", "1y", "1d"))
            data = fetch_stock(symbol, range_=tf[1], interval=tf[2])
        except RuntimeError as e:
            messagebox.showerror("Could not load data", str(e))
            status_var.set("Failed. Try another symbol, or use --demo offline.")
            return

        stats = analyse(data)
        state["data"], state["stats"] = data, stats

        # fill the text box (with a text chart if matplotlib is missing)
        content = format_report(stats)
        if not have_mpl:
            content += "\n\n" + ascii_chart(data, stats)
        text_box.configure(state="normal")
        text_box.delete("1.0", "end")
        text_box.insert("1.0", content)
        text_box.configure(state="disabled")

        # draw the graph inside the window (only if matplotlib is available)
        for widget in chart_frame.winfo_children():
            widget.destroy()
        if have_mpl:
            fig = build_chart(data, stats)
            canvas = FigureCanvasTkAgg(fig, master=chart_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill="both", expand=True)
            status_var.set(f"Done - {symbol}")
        else:
            status_var.set(f"Done - {symbol}  (text chart; install matplotlib for a graph)")

    ttk.Button(top, text="Analyze", command=do_analyze).pack(side="left", padx=8)
    ttk.Button(top, text="Save chart PNG",
               command=lambda: save_chart()).pack(side="left")
    ttk.Label(top, textvariable=status_var).pack(side="left", padx=12)

    # --- search bar: find ANY share by company name ---
    search_matches = []
    sbar = ttk.Frame(root, padding=(10, 4))
    sbar.pack(fill="x")
    ttk.Label(sbar, text="Search Indian company:").pack(side="left")
    search_var = tk.StringVar()
    ttk.Entry(sbar, textvariable=search_var, width=30).pack(side="left", padx=6)
    results_box = tk.Listbox(root, height=5)

    def do_search():
        query = search_var.get().strip()
        if not query:
            return
        try:
            matches = search_symbols(query)
        except RuntimeError as e:
            messagebox.showerror("Search failed", str(e))
            return
        results_box.delete(0, "end")
        search_matches.clear()
        if not matches:
            results_box.insert("end", "(no Indian shares found - try the full name)")
            return
        for m in matches:
            results_box.insert("end", f"{m['symbol']:<16} {m['name'][:42]}")
            search_matches.append(m)

    ttk.Button(sbar, text="Search", command=do_search).pack(side="left")
    ttk.Label(sbar, text="(double-click a result to analyze it)").pack(
        side="left", padx=8)
    results_box.pack(fill="x", padx=10)

    def pick_result(_event=None):
        sel = results_box.curselection()
        if sel and sel[0] < len(search_matches):
            symbol_var.set(search_matches[sel[0]]["symbol"])
            do_analyze()

    results_box.bind("<Double-Button-1>", pick_result)

    # --- market indices box (Nifty, Sensex, Bank Nifty) ---
    idx_box = ttk.LabelFrame(root, text="Market indices", padding=6)
    idx_box.pack(fill="x", padx=10, pady=(6, 0))
    index_labels = {}
    for i, (name, sym) in enumerate(INDICES):
        lbl = tk.Label(idx_box, text=f"{name}: ...", anchor="w",
                       font=("Segoe UI", 10, "bold"))
        lbl.grid(row=0, column=i, sticky="w", padx=(4, 18))
        index_labels[sym] = lbl

    def refresh_indices():
        for name, sym in INDICES:
            index_labels[sym].config(text=f"{name}: loading...", fg="gray")
        root.update_idletasks()
        for row in market_overview():
            lbl = index_labels[row["symbol"]]
            if row["last"] is None:
                lbl.config(text=f"{row['name']}: n/a", fg="gray")
                continue
            up = (row["change"] or 0) >= 0
            lbl.config(text=f"{row['name']}: {row['last']:,.2f}  "
                           f"({row['change']:+.2f}%)",
                       fg=("green" if up else "red"))

    ttk.Button(idx_box, text="Refresh", command=refresh_indices).grid(
        row=0, column=len(INDICES), padx=(10, 4))
    root.after(200, refresh_indices)     # load the indices shortly after start

    def save_chart():
        if not state["data"]:
            messagebox.showinfo("Nothing to save", "Analyze a stock first.")
            return
        if not have_mpl:
            messagebox.showinfo("matplotlib needed",
                                "Install matplotlib to save a PNG chart.")
            return
        name = f"{state['data']['symbol'].replace('.', '_')}_chart.png"
        build_chart(state["data"], state["stats"], save_path=name)
        messagebox.showinfo("Saved", f"Chart saved as {name}")

    # --- middle: text report ---
    body = ttk.Frame(root)
    body.pack(fill="both", expand=True, padx=10)

    text_box = tk.Text(body, width=52, font=("Consolas", 10), state="disabled")
    text_box.pack(side="left", fill="y")

    chart_frame = ttk.Frame(body)
    chart_frame.pack(side="right", fill="both", expand=True, padx=(10, 0))

    root.mainloop()


# ----------------------------------------------------------------
# 6. OFFLINE DEMO  (no internet needed)
# ----------------------------------------------------------------

def make_demo_data(symbol="DEMO.NS", days=250, seed=7):
    """Create a realistic-looking price series with a random walk, so the
    project can be demonstrated even without internet access."""
    random.seed(seed)
    price = 1500.0
    dates, closes, volumes = [], [], []
    start = datetime(2025, 1, 1)
    for i in range(days):
        # small upward drift + random daily movement
        price *= 1 + random.gauss(0.0005, 0.013)
        price = max(price, 1.0)
        day = start.fromordinal(start.toordinal() + i)
        if day.weekday() < 5:             # weekdays only
            dates.append(day.strftime("%Y-%m-%d"))
            closes.append(round(price, 2))
            volumes.append(random.randint(1_000_000, 9_000_000))
    return {"symbol": symbol, "currency": "INR", "exchange": "DEMO",
            "dates": dates, "closes": closes, "volumes": volumes}


# ----------------------------------------------------------------
# 7. ENTRY POINT
# ----------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Analyze a stock's price history (Yahoo Finance, no API key)."
    )
    parser.add_argument("--symbol", help="e.g. RELIANCE.NS, TCS.NS, ^NSEI")
    parser.add_argument("--range", default="1y",
                        help="1d, 5d, 1mo, 3mo, 6mo, 1y, 2y, 5y (default 1y)")
    parser.add_argument("--interval", default="1d",
                        help="1m, 5m, 15m, 30m, 60m, 1d, 1wk (default 1d)")
    parser.add_argument("--csv", help="read prices from a CSV instead of the web")
    parser.add_argument("--chart", help="save the chart to this PNG file")
    parser.add_argument("--demo", action="store_true",
                        help="run offline with generated sample data")
    parser.add_argument("--gui", action="store_true", help="open the GUI window")
    parser.add_argument("--ascii", action="store_true",
                        help="print a text chart in the terminal (no matplotlib)")
    parser.add_argument("--search", metavar="NAME",
                        help='find Indian shares by name, e.g. --search "tata motors"')
    parser.add_argument("--find", metavar="NAME",
                        help="search an Indian company and analyze the top match")
    parser.add_argument("--indices", action="store_true",
                        help="show Nifty, Sensex and Bank Nifty in the terminal")
    parser.add_argument("--ticks", type=int,
                        help="max time labels on the chart's x-axis (default 15)")
    args = parser.parse_args()

    # --- market indices overview ---
    if args.indices:
        print("Market indices:\n")
        for row in market_overview():
            if row["last"] is None:
                print(f"  {row['name']:<12} n/a")
            else:
                print(f"  {row['name']:<12} {row['last']:>12,.2f}   "
                      f"{row['change']:+.2f}%")
        return

    # --- find any share by company name ---
    if args.search or args.find:
        query = args.search or args.find
        try:
            matches = search_symbols(query)
        except RuntimeError as e:
            print(f"Error: {e}")
            return
        if not matches:
            print(f"No Indian shares found for '{query}'. "
                  "Try the full company name.")
            return
        print(f"Matches for '{query}':\n")
        for i, m in enumerate(matches, 1):
            print(f"  {i:>2}. {m['symbol']:<16} {m['name']}  ({m['exchange']})")
        if not args.find:
            print("\nNow run:  python stock_analyzer.py --symbol <SYMBOL>")
            return
        args.symbol = matches[0]["symbol"]
        print(f"\nAnalyzing the top match: {args.symbol} ...\n")

    # GUI mode (default when no other options are given)
    if args.gui or (not args.symbol and not args.csv and not args.demo
                    and not args.chart and not args.ascii):
        try:
            launch_gui()
        except Exception as e:
            print(f"Could not open the GUI ({e}).")
            print("Run 'python stock_analyzer.py --demo' for a text demo instead.")
        return

    # get the data
    try:
        if args.demo:
            data = make_demo_data()
            print("Running in DEMO mode with generated sample data.\n")
        elif args.csv:
            data = load_csv(args.csv)
        else:
            print(f"Downloading {args.symbol} "
                  f"({args.range}, {args.interval}) ...")
            data = fetch_stock(args.symbol, range_=args.range,
                               interval=args.interval)
    except RuntimeError as e:
        print(f"Error: {e}")
        print("Tip: run 'python stock_analyzer.py --demo' to try it offline.")
        return
    except (OSError, KeyError, ValueError) as e:
        print(f"Error: could not read that CSV file ({e}).")
        return

    stats = analyse(data)
    print(format_report(stats))

    # text chart when asked, or automatically when matplotlib is missing
    if args.ascii or not mpl_available():
        print()
        print(ascii_chart(data, stats))

    if args.chart:
        if mpl_available():
            build_chart(data, stats, save_path=args.chart, max_ticks=args.ticks)
        else:
            print("\n(could not save a PNG chart - matplotlib is not installed)")


if __name__ == "__main__":
    main()
