#!/usr/bin/env python3
"""
Liest Aurena-Posten-URLs aus einer Textdatei und erzeugt eine HTML-Datei
mit einer Tabelle der Ergebnisse.

Pro URL werden extrahiert:
- Name (in der HTML-Ausgabe als Hyperlink auf die URL)
- Aktuelles Gebot
- Aktuelles Gebot inkl. 20 % MwSt + 18 % Auktionsgebühr
- Ende der Auktion

Eigenschaften:
- Mehrere Links gleichzeitig per ThreadPoolExecutor
- Keine CSV-Dateien, keine Logdatei, keine Debug-Dateien
- Nur eine HTML-Ausgabedatei
- Reihenfolge in der HTML-Tabelle entspricht der Reihenfolge der Eingabedatei

Benötigt:
    pip install requests beautifulsoup4

Beispiel:
    python aurena_scraper_html.py
    python aurena_scraper_html.py aurenalinks.txt aurena_posten.html --workers 8 --delay 0.2
"""

from __future__ import annotations

import argparse
import html
import re
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from urllib.parse import urlparse

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from requests.exceptions import RequestException
from urllib3.util.retry import Retry

INPUT_FILE = Path("aurenalinks.txt")
OUTPUT_FILE = Path("aurena_posten.html")
REQUEST_DELAY_SECONDS = 0.0
TOTAL_FACTOR = Decimal("1.416")
DEFAULT_TIMEOUT = 30
DEFAULT_WORKERS = 5

END_DATETIME_RE = re.compile(r"\b(\d{2}\.\d{2}\.\d{4},\s*\d{2}:\d{2}\s*Uhr)\b")
WHITESPACE_RE = re.compile(r"\s+")
LABEL_BID_RE = re.compile(r"aktuelles\s+gebot", flags=re.IGNORECASE)
LABEL_END_SECTION_RE = re.compile(r"(?:zuschl[aä]ge|gebotsabgabe)", flags=re.IGNORECASE)
MONEY_TEXT_RE = re.compile(
    r"(?:€\s*[0-9][0-9\.\s]*(?:,[0-9]{1,2})?|[0-9][0-9\.\s]*(?:,[0-9]{1,2})?\s*€)"
)
REAL_BLOCK_HINTS = [
    "captcha",
    "verify you are human",
    "attention required",
    "access denied",
    "forbidden",
    "bot detection",
    "unusual traffic",
    "security check",
    "request blocked",
    "cloudflare",
    "cf-chl",
]
EXPECTED_AUCTION_MARKERS = [
    "aktuelles gebot",
    "auktionsgebühr",
    "mehrwertsteuer",
    "gebote",
    "rufpreis",
]

_thread_local = threading.local()


class ExtractionError(RuntimeError):
    """Raised when a required field cannot be extracted."""


@dataclass
class FetchInfo:
    status_code: int
    final_url: str
    content_type: str
    response_size: int


@dataclass
class PageDiagnostics:
    has_h1: bool = False
    bid_label_count: int = 0
    money_candidate_count: int = 0
    auction_marker_count: int = 0
    blocked_hint: str = ""


@dataclass
class ScrapeRow:
    url: str
    name: str
    current_bid: str
    total_price: str
    end_datetime: str


@dataclass
class IndexedOutcome:
    index: int
    url: str
    row: ScrapeRow | None
    error_message: str | None


def build_session() -> requests.Session:
    retry = Retry(
        total=3,
        connect=3,
        read=3,
        backoff_factor=1,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["GET"],
        raise_on_status=False,
        respect_retry_after_header=True,
    )

    session = requests.Session()
    session.headers.update(
        {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/123.0 Safari/537.36"
            ),
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "de-AT,de;q=0.9,en;q=0.8",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
        }
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=DEFAULT_WORKERS * 2, pool_maxsize=DEFAULT_WORKERS * 2)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


def get_session() -> requests.Session:
    session = getattr(_thread_local, "session", None)
    if session is None:
        session = build_session()
        _thread_local.session = session
    return session


def normalize_whitespace(text: str) -> str:
    return WHITESPACE_RE.sub(" ", text).strip()


def clean_money_text(raw: str) -> str:
    return normalize_whitespace(raw.replace("\xa0", " "))


def parse_decimal_eur(raw: str) -> Decimal:
    cleaned = clean_money_text(raw)
    cleaned = cleaned.replace("€", "").replace(" ", "")
    cleaned = cleaned.replace(".-", "").replace(",-", "")
    cleaned = cleaned.replace(".", "").replace(",", ".")
    try:
        return Decimal(cleaned)
    except InvalidOperation as exc:
        raise ExtractionError(f"Betrag konnte nicht geparst werden: {raw!r}") from exc


def format_decimal_de(value: Decimal) -> str:
    quantized = value.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    return f"{quantized:.2f}".replace(".", ",")


def get_text_tokens(soup: BeautifulSoup) -> list[str]:
    tokens: list[str] = []
    for s in soup.stripped_strings:
        token = normalize_whitespace(str(s))
        if token:
            tokens.append(token)
    return tokens


def extract_name(soup: BeautifulSoup) -> str:
    h1 = soup.find("h1")
    if h1:
        name = normalize_whitespace(h1.get_text(" ", strip=True))
        if name:
            return name

    og_title = soup.find("meta", attrs={"property": "og:title"})
    if og_title and og_title.get("content"):
        title = normalize_whitespace(og_title["content"])
        if title:
            return title

    if soup.title and soup.title.string:
        title = normalize_whitespace(soup.title.string)
        title = re.sub(r"\s*günstig in Auktion kaufen.*$", "", title, flags=re.IGNORECASE)
        if title:
            return title

    raise ExtractionError("Name nicht gefunden")


def find_money_candidates(text: str) -> list[tuple[str, Decimal]]:
    candidates: list[tuple[str, Decimal]] = []
    for match in MONEY_TEXT_RE.finditer(text):
        raw = clean_money_text(match.group(0))
        try:
            candidates.append((raw, parse_decimal_eur(raw)))
        except ExtractionError:
            continue
    return candidates


def find_block_hint(text: str) -> str:
    lower_text = text.lower()
    for hint in REAL_BLOCK_HINTS:
        if hint in lower_text:
            return hint
    return ""


def count_auction_markers(text: str) -> int:
    lower_text = text.lower()
    return sum(1 for marker in EXPECTED_AUCTION_MARKERS if marker in lower_text)


def build_diagnostics(soup: BeautifulSoup, text: str) -> PageDiagnostics:
    tokens = get_text_tokens(soup)
    return PageDiagnostics(
        has_h1=soup.find("h1") is not None,
        bid_label_count=len(LABEL_BID_RE.findall(text)),
        money_candidate_count=len(find_money_candidates(text)),
        auction_marker_count=count_auction_markers(text),
        blocked_hint=find_block_hint(text),
    )


def infer_page_type(fetch_info: FetchInfo, diagnostics: PageDiagnostics) -> str:
    if "text/html" not in fetch_info.content_type.lower():
        return "non_html"

    if diagnostics.blocked_hint and diagnostics.auction_marker_count < 2 and not diagnostics.has_h1:
        return "blocked_or_challenge"

    if diagnostics.bid_label_count == 0 and diagnostics.money_candidate_count == 0:
        return "unexpected_page_structure"

    return "html"


def extract_bid_from_text(text: str) -> Decimal:
    patterns = [
        re.compile(
            r"((?:€\s*[0-9][0-9\.\s]*(?:,[0-9]{1,2})?|[0-9][0-9\.\s]*(?:,[0-9]{1,2})?\s*€))\s*Aktuelles\s+Gebot",
            flags=re.IGNORECASE,
        ),
        re.compile(
            r"Aktuelles\s+Gebot\s*((?:€\s*[0-9][0-9\.\s]*(?:,[0-9]{1,2})?|[0-9][0-9\.\s]*(?:,[0-9]{1,2})?\s*€))",
            flags=re.IGNORECASE,
        ),
    ]

    for regex in patterns:
        match = regex.search(text)
        if match:
            return parse_decimal_eur(match.group(1))

    for match in LABEL_BID_RE.finditer(text):
        start = max(0, match.start() - 220)
        end = min(len(text), match.end() + 220)
        window = text[start:end]
        monies = find_money_candidates(window)
        if monies:
            before_window = text[start:match.start()]
            before_monies = find_money_candidates(before_window)
            if before_monies:
                return before_monies[-1][1]
            return monies[0][1]

    raise ExtractionError("Aktuelles Gebot nicht gefunden")


def extract_end_datetime(text: str) -> str:
    bid_match = LABEL_BID_RE.search(text)
    if bid_match:
        start = max(0, bid_match.start() - 150)
        end = min(len(text), bid_match.end() + 600)
        window = text[start:end]
        date_match = END_DATETIME_RE.search(window)
        if date_match:
            return date_match.group(1)

    section_match = LABEL_END_SECTION_RE.search(text)
    if section_match:
        start = max(0, section_match.start() - 50)
        end = min(len(text), section_match.end() + 500)
        window = text[start:end]
        date_match = END_DATETIME_RE.search(window)
        if date_match:
            return date_match.group(1)

    all_matches = [m.group(1) for m in END_DATETIME_RE.finditer(text)]
    if all_matches:
        return all_matches[0]

    raise ExtractionError("Auktionsende nicht gefunden")


def fetch_page(session: requests.Session, url: str, timeout: int) -> tuple[requests.Response, FetchInfo]:
    response = session.get(url, timeout=timeout)
    response.raise_for_status()
    fetch_info = FetchInfo(
        status_code=response.status_code,
        final_url=str(response.url),
        content_type=response.headers.get("Content-Type", ""),
        response_size=len(response.text or ""),
    )
    return response, fetch_info


def load_links(path: Path) -> list[str]:
    if not path.exists():
        raise FileNotFoundError(f"Eingabedatei nicht gefunden: {path}")

    links: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip().strip('"').strip("'")
        if not line or line.startswith("#"):
            continue
        links.append(line)

    if not links:
        raise ValueError(f"Keine URLs in {path} gefunden")

    return list(dict.fromkeys(links))


def parse_page(url: str, timeout: int, pre_request_delay: float = 0.0) -> ScrapeRow:
    session = get_session()
    if pre_request_delay > 0:
        time.sleep(pre_request_delay)

    response, fetch_info = fetch_page(session, url, timeout)
    soup = BeautifulSoup(response.text, "html.parser")
    text = normalize_whitespace(soup.get_text(" ", strip=True))
    diagnostics = build_diagnostics(soup, text)

    page_type = infer_page_type(fetch_info, diagnostics)
    if page_type == "non_html":
        raise ExtractionError(f"Antwort ist kein HTML: {fetch_info.content_type}")
    if page_type == "blocked_or_challenge":
        raise ExtractionError(
            f"Seite wirkt blockiert/ungewöhnlich: Hinweis={diagnostics.blocked_hint} | "
            f"auction_markers={diagnostics.auction_marker_count} | h1={diagnostics.has_h1}"
        )

    name = extract_name(soup)
    current_bid = extract_bid_from_text(text)
    end_datetime = extract_end_datetime(text)
    total_price = current_bid * TOTAL_FACTOR

    return ScrapeRow(
        url=url,
        name=name,
        current_bid=format_decimal_de(current_bid),
        total_price=format_decimal_de(total_price),
        end_datetime=end_datetime,
    )


def process_one(index: int, total: int, url: str, timeout: int, delay: float, workers: int) -> IndexedOutcome:
    pre_request_delay = 0.0
    if delay > 0 and workers > 1:
        pre_request_delay = ((index - 1) % workers) * delay
    elif delay > 0:
        pre_request_delay = delay

    try:
        row = parse_page(url=url, timeout=timeout, pre_request_delay=pre_request_delay)
        return IndexedOutcome(index=index, url=url, row=row, error_message=None)
    except RequestException as exc:
        return IndexedOutcome(index=index, url=url, row=None, error_message=f"HTTP-Fehler: {exc}")
    except Exception as exc:
        return IndexedOutcome(index=index, url=url, row=None, error_message=f"{type(exc).__name__}: {exc}")


def make_html_document(rows: list[ScrapeRow], total_urls: int, failed_count: int) -> str:
    generated_at = time.strftime("%d.%m.%Y %H:%M:%S")
    body_rows: list[str] = []

    for row in rows:
        name_label = html.escape(row.name)
        href = html.escape(row.url, quote=True)
        body_rows.append(
            "<tr>"
            f"<td><a href=\"{href}\" target=\"_blank\" rel=\"noopener noreferrer\">{name_label}</a></td>"
            f"<td class=\"num\">{html.escape(row.current_bid)}</td>"
            f"<td class=\"num\">{html.escape(row.total_price)}</td>"
            f"<td>{html.escape(row.end_datetime)}</td>"
            "</tr>"
        )

    table_html = "\n".join(body_rows)

    return f"""<!DOCTYPE html>
<html lang="de">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Aurena Ergebnisse</title>
  <style>
    :root {{
      color-scheme: light dark;
      --bg: #ffffff;
      --fg: #1f2328;
      --muted: #667085;
      --border: #d0d7de;
      --header: #f6f8fa;
      --row-alt: #fafbfc;
      --link: #0969da;
    }}
    @media (prefers-color-scheme: dark) {{
      :root {{
        --bg: #0d1117;
        --fg: #e6edf3;
        --muted: #9da7b3;
        --border: #30363d;
        --header: #161b22;
        --row-alt: #0f141b;
        --link: #58a6ff;
      }}
    }}
    body {{
      margin: 0;
      font-family: Arial, Helvetica, sans-serif;
      background: var(--bg);
      color: var(--fg);
    }}
    .wrap {{
      max-width: 1200px;
      margin: 0 auto;
      padding: 24px;
    }}
    h1 {{
      margin: 0 0 8px;
      font-size: 28px;
    }}
    .meta {{
      color: var(--muted);
      margin-bottom: 18px;
      line-height: 1.5;
    }}
    .table-wrap {{
      overflow-x: auto;
      border: 1px solid var(--border);
      border-radius: 12px;
    }}
    table {{
      width: 100%;
      border-collapse: collapse;
      min-width: 760px;
      background: var(--bg);
    }}
    thead th {{
      position: sticky;
      top: 0;
      background: var(--header);
      text-align: left;
      font-weight: 700;
      border-bottom: 1px solid var(--border);
    }}
    th, td {{
      padding: 12px 14px;
      border-bottom: 1px solid var(--border);
      vertical-align: top;
    }}
    tbody tr:nth-child(even) {{
      background: var(--row-alt);
    }}
    td.num {{
      text-align: right;
      white-space: nowrap;
      font-variant-numeric: tabular-nums;
    }}
    a {{
      color: var(--link);
      text-decoration: none;
    }}
    a:hover {{
      text-decoration: underline;
    }}
    .empty {{
      padding: 18px;
      color: var(--muted);
    }}
  </style>
</head>
<body>
  <div class="wrap">
    <h1>Aurena Ergebnisse</h1>
    <div class="meta">
      Erzeugt am {html.escape(generated_at)}<br>
      Verarbeitete URLs: {total_urls} | Erfolgreich extrahiert: {len(rows)} | Fehler: {failed_count}
    </div>
    <div class="table-wrap">
      <table>
        <thead>
          <tr>
            <th>Name</th>
            <th>Aktuelles Gebot</th>
            <th>+20% MwSt +18% Geb.</th>
            <th>Ende der Auktion</th>
          </tr>
        </thead>
        <tbody>
          {table_html if table_html else '<tr><td colspan="4" class="empty">Keine erfolgreichen Treffer vorhanden.</td></tr>'}
        </tbody>
      </table>
    </div>
  </div>
</body>
</html>
"""


def write_html(rows: list[ScrapeRow], path: Path, total_urls: int, failed_count: int) -> None:
    html_doc = make_html_document(rows=rows, total_urls=total_urls, failed_count=failed_count)
    path.write_text(html_doc, encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Aurena-Posten scrapen und als HTML-Tabelle speichern")
    parser.add_argument("input", nargs="?", default=str(INPUT_FILE), help="Textdatei mit URLs")
    parser.add_argument("output", nargs="?", default=str(OUTPUT_FILE), help="HTML-Datei für die Ergebnisse")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, help="Request-Timeout in Sekunden")
    parser.add_argument(
        "--delay",
        type=float,
        default=REQUEST_DELAY_SECONDS,
        help="Kleine Zusatzverzögerung vor dem Request. Bei Parallelbetrieb wird sie je Worker-Slot gestaffelt.",
    )
    parser.add_argument("--workers", type=int, default=DEFAULT_WORKERS, help="Anzahl gleichzeitiger Requests")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    input_file = Path(args.input)
    output_file = Path(args.output)
    workers = max(1, args.workers)

    try:
        links = load_links(input_file)
    except Exception as exc:
        print(f"Fehler beim Einlesen der Links: {exc}", file=sys.stderr)
        return 1

    rows_by_index: dict[int, ScrapeRow] = {}
    failed_count = 0

    with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="aurena") as executor:
        futures = {
            executor.submit(process_one, index, len(links), url, args.timeout, args.delay, workers): (index, url)
            for index, url in enumerate(links, start=1)
        }

        for future in as_completed(futures):
            index, url = futures[future]
            try:
                outcome = future.result()
            except Exception as exc:
                failed_count += 1
                print(f"[{index}/{len(links)}] FEHLER | {type(exc).__name__}: {exc} | url={url}", file=sys.stderr)
                continue

            if outcome.row is not None:
                rows_by_index[index] = outcome.row
                print(
                    f"[{index}/{len(links)}] OK     | "
                    f"Bid={outcome.row.current_bid} | "
                    f"Ende={outcome.row.end_datetime} | "
                    f"{outcome.row.name}"
                )
            else:
                failed_count += 1
                print(f"[{index}/{len(links)}] FEHLER | {outcome.error_message} | url={url}", file=sys.stderr)

    rows = [rows_by_index[i] for i in sorted(rows_by_index)]

    try:
        write_html(rows=rows, path=output_file, total_urls=len(links), failed_count=failed_count)
    except Exception as exc:
        print(f"Fehler beim Schreiben der HTML-Datei: {exc}", file=sys.stderr)
        return 2

    print(f"\nHTML geschrieben: {output_file.resolve()}")
    print(f"Gesamt: {len(links)} URLs | Erfolge: {len(rows)} | Fehler: {failed_count} | Workers: {workers}")

    if rows and not failed_count:
        return 0
    if rows and failed_count:
        return 3
    return 4


if __name__ == "__main__":
    raise SystemExit(main())
