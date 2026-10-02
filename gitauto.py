import calendar
import hashlib
import json
import os
import re
import shutil
import sys
import time
import unicodedata
import urllib.parse
import zipfile

import feedparser
import requests

FEEDS = [
    "https://feeds.simplecast.com/54nAGcIl",
    "https://techblogwriter.libsyn.com/rss",
    "https://feeds.feedburner.com/TEDTalks_audio",
    "https://feeds.simplecast.com/ZgXQt_UM",
    "https://podcasts.files.bbci.co.uk/p02nq0gn.rss",
    "https://feed.podbean.com/dailyworldbrief/feed.xml",
    "https://rss.amperwave.net/v2/feed/audacynetwork/4cbf0abf775be3cab2bd61a739939f1b",
    "https://www.omnycontent.com/d/playlist/397b9456-4f75-4509-acff-ac0600b4a6a4/6b5c19f7-a385-49c0-bb95-ad4a0071daea/08535d76-8bf4-4bf2-af8d-ad4a007205a3/podcast.rss",
    "https://feeds.megaphone.fm/GLT1412515089",
    "https://omnycontent.com/d/playlist/e73c998e-6e60-432f-8610-ae210140c5b1/A91018A4-EA4F-4130-BF55-AE270180C327/44710ECC-10BB-48D1-93C7-AE270180C33E/podcast.rss",
    "https://www.omnycontent.com/d/playlist/2ee97a4e-8795-4260-9648-accf00a38c6a/ac2da21e-2193-4683-bcb5-accf011076ad/409bad89-c4c2-46cb-b69b-accf01152781/podcast.rss",
    "https://www.spreaker.com/show/6951904/episodes/feed",
    "https://feeds.simplecast.com/qm_9xx0g",
    "https://feeds.simplecast.com/JZSQrle9",
    "https://feeds.megaphone.fm/WWO7410387571",
    "https://feeds.megaphone.fm/RSV1597324942",
    "https://rss2.flightcast.com/xmsftuzjjykcmqwolaqn6mdn",
    "https://www.omnycontent.com/d/playlist/e73c998e-6e60-432f-8610-ae210140c5b1/32f1779e-bc01-4d36-89e6-afcb01070c82/e0c8382f-48d4-42bb-89d5-afcb01075cb4/podcast.rss",
    "https://anchor.fm/s/1007c648c/podcast/rss",
    "https://anchor.fm/s/102ae1cf0/podcast/rss",
    "https://tonyrobbins.libsyn.com/rss",
    "https://feeds.acast.com/public/shows/67587e77c705e441797aff96",
    "https://feeds.megaphone.fm/ESP6921732651",
    "https://feeds.megaphone.fm/the-rich-roll-podcast",
    "https://anchor.fm/s/10d9805f4/podcast/rss",
    "https://podcastfeeds.nbcnews.com/dateline-nbc",
    "https://www.spreaker.com/show/5956723/episodes/feed",
    "https://feeds.megaphone.fm/SIXMSB5088139739",
    "https://feeds.npr.org/510298/podcast.xml",
    "https://feeds.transistor.fm/think-fast-talk-smart-communication-techniques",
    "https://feeds.megaphone.fm/NRD2548999404",
    "https://api.substack.com/feed/podcast/1449053.rss",
]

STATE_FILE = "seen.json"
FAIL_KEY = "__failures__"          # מונה כשלונות לפי פיד ופרק (בתוך seen.json)
DOWNLOAD_DIR = "podcasts"          # חייב להיות תואם למה שה-Workflow מחפש
TMP_DIR = "tmp_dl"                 # הורדות חלקיות (מחוץ ל-podcasts)
META_DIR = "meta"
META_SHOWS = os.path.join(META_DIR, "shows.json")
PREV_DIR = "prev"                  # ZIPים קיימים של היום (מורדים מה-Release)
OUT_DIR = "out"                    # ZIPים להעלאה

TEST_SEND = os.environ.get("TEST_SEND") == "true"

MAX_ATTEMPTS = 3                   # אחרי כמה ריצות מוותרים על פרק שנכשל
MAX_IDS_FALLBACK = 200             # כמה מזהים לשמור לפיד בלי תאריכים
FALLBACK_WINDOW = 20               # כמה פרקים אחרונים לבדוק בפיד בלי תאריכים
MAX_TITLE_LEN = 150                # אורך מקסימלי של שם פרק בשם הקובץ
ZIP_LIMIT = 1_900_000_000          # מגבלת GitHub לקובץ: 2GiB, משאירים מרווח

SHOWS = {}                         # slug -> שם התוכנית המקורי (לריצה הנוכחית)

HEBREW_MAP = {
    'א': 'a', 'ב': 'b', 'ג': 'g', 'ד': 'd', 'ה': 'h', 'ו': 'v', 'ז': 'z',
    'ח': 'ch', 'ט': 't', 'י': 'y', 'כ': 'k', 'ך': 'k', 'ל': 'l', 'מ': 'm',
    'ם': 'm', 'נ': 'n', 'ן': 'n', 'ס': 's', 'ע': 'a', 'פ': 'p', 'ף': 'p',
    'צ': 'ts', 'ץ': 'ts', 'ק': 'k', 'ר': 'r', 'ש': 'sh', 'ת': 't',
}

# ---------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------


def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                return data
        except Exception as e:
            print(f"Could not read {STATE_FILE}: {e}")
    return {}


def save_state(state):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# Names
# ---------------------------------------------------------------------------

_FORBIDDEN = re.compile(r'[<>:"/\\|?*\x00-\x1f\x7f]')
_INVISIBLE = re.compile('[\u200b-\u200f\u202a-\u202e\u2066-\u2069\ufeff]')
_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} | {f"LPT{i}" for i in range(1, 10)}


def safe_filename(title, max_len=MAX_TITLE_LEN):
    """שם קובץ מלא ומקורי (כולל עברית), רק בלי תווים שאסורים ב-Windows."""
    name = _INVISIBLE.sub("", title or "")
    name = _FORBIDDEN.sub("", name)
    name = re.sub(r"\s+", " ", name).strip()
    name = name[:max_len].rstrip(" .")
    if not name:
        name = "episode"
    if name.split(".")[0].upper() in _RESERVED:
        name = "_" + name
    return name


def show_slug(name, feed_url=""):
    """שם ASCII בטוח ל-ZIP (אותיות, ספרות, _ בלבד) - GitHub לא משבש אותו."""
    text = "".join(HEBREW_MAP.get(c, c) for c in (name or ""))
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if c.isascii())
    text = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_")[:50].strip("_")
    if not text:
        text = "podcast_" + hashlib.md5(feed_url.encode()).hexdigest()[:8]
    return text


def unique_path(folder, base, ext):
    path = os.path.join(folder, f"{base}.{ext}")
    k = 2
    while os.path.exists(path):
        path = os.path.join(folder, f"{base} ({k}).{ext}")
        k += 1
    return path


# ---------------------------------------------------------------------------
# File type detection
# ---------------------------------------------------------------------------

TYPE_EXT = {
    "audio/mpeg": "mp3", "audio/mp3": "mp3", "audio/mpeg3": "mp3", "audio/x-mpeg": "mp3",
    "audio/mp4": "m4a", "audio/x-m4a": "m4a", "audio/m4a": "m4a",
    "audio/aac": "aac", "audio/aacp": "aac", "audio/x-aac": "aac",
    "audio/ogg": "ogg", "application/ogg": "ogg", "audio/opus": "opus", "audio/x-opus+ogg": "opus",
    "audio/wav": "wav", "audio/x-wav": "wav", "audio/wave": "wav",
    "audio/flac": "flac", "audio/x-flac": "flac",
    "audio/webm": "webm", "video/webm": "webm",
    "video/mp4": "mp4", "video/x-m4v": "m4v", "video/quicktime": "mov",
}
KNOWN_EXT = set(TYPE_EXT.values())


def ext_from_type(content_type):
    if not content_type:
        return None
    return TYPE_EXT.get(content_type.split(";")[0].strip().lower())


def ext_from_url(url):
    ext = os.path.splitext(urllib.parse.urlparse(url).path)[1].lower().lstrip(".")
    return ext if ext in KNOWN_EXT else None


def sniff_ext(head, hint):
    """זיהוי פורמט אמיתי לפי תחילת הקובץ (חזק יותר ממה שהפיד מצהיר)."""
    if head[:3] == b"ID3":
        return "mp3"
    if head[:4] == b"OggS":
        return "opus" if b"OpusHead" in head else "ogg"
    if head[:4] == b"RIFF" and head[8:12] == b"WAVE":
        return "wav"
    if head[:4] == b"fLaC":
        return "flac"
    if head[:4] == b"\x1aE\xdf\xa3":
        return "webm"
    if head[4:8] == b"ftyp":
        brand = head[8:12]
        if brand in (b"M4A ", b"M4B ", b"M4P "):
            return "m4a"
        return "m4a" if hint in ("m4a", "mp3", "aac", "ogg", "opus", "wav", "flac") else "mp4"
    if len(head) >= 2 and head[0] == 0xFF and (head[1] & 0xE0) == 0xE0:
        return "aac" if (head[1] & 0x06) == 0 else "mp3"
    return None


def pick_enclosure(entry):
    encs = entry.get("enclosures") or []
    for e in encs:
        t = (e.get("type") or "").lower()
        if e.get("href") and (t.startswith("audio/") or t.startswith("video/") or t == "application/ogg"):
            return e
    for e in encs:
        if e.get("href") and not (e.get("type") or "").lower().startswith("image/"):
            return e
    return None


# ---------------------------------------------------------------------------
# Download
# ---------------------------------------------------------------------------

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
}


def download_to(url, dest):
    """מוריד לקובץ זמני. מחזיר את ה-Content-Type של התשובה."""
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    for attempt in range(1, 4):
        try:
            with requests.get(url, headers=HEADERS, stream=True, timeout=(30, 300)) as r:
                r.raise_for_status()
                ctype = r.headers.get("Content-Type", "")
                with open(dest, "wb") as f:
                    for chunk in r.iter_content(chunk_size=1024 * 512):
                        if chunk:
                            f.write(chunk)
            return ctype
        except Exception as e:
            print(f"ניסיון {attempt} נכשל בהורדה: {e}")
            if attempt == 3:
                raise
            time.sleep(5)


def process_entry(feed_url, feed_title, entry):
    """מחזיר True אם הפרק טופל (ירד, או שאין מה להוריד), False אם נכשל ושווה לנסות שוב."""
    title = (entry.get("title") or "").strip() or "New episode"
    enc = pick_enclosure(entry)
    if not enc:
        print(f"No audio file found for: {title}")
        return True

    url = enc["href"]
    slug = show_slug(feed_title, feed_url)
    show_dir = os.path.join(DOWNLOAD_DIR, slug)
    tmp = os.path.join(TMP_DIR, hashlib.md5((feed_url + url).encode()).hexdigest() + ".part")

    try:
        ctype = download_to(url, tmp)

        size = os.path.getsize(tmp)
        with open(tmp, "rb") as f:
            head = f.read(64)
        if size < 1024 or head.lstrip()[:1] == b"<":
            raise ValueError(f"התקבל קובץ לא תקין ({size} bytes)")

        hint = ext_from_type(enc.get("type")) or ext_from_url(url) or ext_from_type(ctype)
        ext = sniff_ext(head, hint) or hint or "mp3"

        os.makedirs(show_dir, exist_ok=True)
        path = unique_path(show_dir, safe_filename(title), ext)
        shutil.move(tmp, path)

        pub = entry.get("published_parsed")
        if pub:
            ts = calendar.timegm(pub)
            if ts > 315532800:  # ZIP לא תומך בתאריכים לפני 1980
                os.utime(path, (ts, ts))

        SHOWS[slug] = (feed_title or "").strip() or slug
        print(f"Downloaded to [{slug}]: {os.path.basename(path)}")
        return True
    except Exception as e:
        print(f"Failed to download '{title}': {e}")
        return False
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Fetch mode (default)
# ---------------------------------------------------------------------------


def entry_ts(e):
    p = e.get("published_parsed") or e.get("updated_parsed")
    return calendar.timegm(p) if p else None


def entry_id(e):
    return e.get("id") or e.get("link") or e.get("title")


def handle_dated(state, failures, feed_url, feed_title, entries, stamps):
    """מצב ברירת מחדל: שומרים רק תאריך של הפרק האחרון שהורד."""
    latest = max(stamps)
    old = state.get(feed_url)

    # ריצה ראשונה, או מעבר מהפורמט הישן (רשימת מזהים): רק מסמנים, לא מורידים
    if not isinstance(old, int):
        state[feed_url] = latest
        return

    fail = failures.setdefault(feed_url, {})
    new = sorted(
        ((t, e) for t, e in zip(stamps, entries) if t > old),
        key=lambda x: x[0],
    )
    last = old
    for t, e in new:
        eid = entry_id(e)
        if process_entry(feed_url, feed_title, e):
            last = t
            fail.pop(eid, None)
        else:
            n = fail.get(eid, 0) + 1
            if n >= MAX_ATTEMPTS:
                print(f"מוותר על פרק אחרי {n} ריצות שנכשלו: {eid}")
                last = t
                fail.pop(eid, None)
            else:
                fail[eid] = n
                break   # לא מתקדמים, ינסה שוב בריצה הבאה

    state[feed_url] = last
    current = {entry_id(e) for e in entries}
    failures[feed_url] = {k: v for k, v in fail.items() if k in current}


def handle_undated(state, failures, feed_url, feed_title, entries):
    """פיד בלי תאריכים: רשימת מזהים קצרה, ובודקים רק את הפרקים האחרונים."""
    window = entries[:FALLBACK_WINDOW]
    ids = [entry_id(e) for e in window]
    old = state.get(feed_url)

    if not isinstance(old, list):     # ריצה ראשונה (או שהיה מספר)
        state[feed_url] = ids
        return

    seen = set(old)
    fail = failures.setdefault(feed_url, {})
    for e, i in reversed(list(zip(window, ids))):
        if i in seen:
            continue
        if process_entry(feed_url, feed_title, e):
            seen.add(i)
            fail.pop(i, None)
        else:
            n = fail.get(i, 0) + 1
            if n >= MAX_ATTEMPTS:
                print(f"מוותר על פרק אחרי {n} ריצות שנכשלו: {i}")
                seen.add(i)
                fail.pop(i, None)
            else:
                fail[i] = n

    ids_set = set(ids)
    state[feed_url] = (ids + [i for i in old if i not in ids_set])[:MAX_IDS_FALLBACK]
    failures[feed_url] = {k: v for k, v in fail.items() if k in ids_set}


def main():
    state = load_state()
    failures = state.get(FAIL_KEY, {})

    for feed_url in FEEDS:
        if not feed_url.strip():
            continue

        parsed = feedparser.parse(feed_url)
        if not parsed.entries:
            print(f"הפיד ריק או לא נטען, מדלג: {feed_url}")
            continue

        feed_title = parsed.feed.get("title", "Podcast")
        entries = parsed.entries

        if TEST_SEND:
            process_entry(feed_url, feed_title, entries[0])
            continue

        stamps = [entry_ts(e) for e in entries]
        dated = sum(1 for t in stamps if t)

        if dated == len(entries):
            handle_dated(state, failures, feed_url, feed_title, entries, stamps)
        else:
            print(f"אין תאריכים בפיד ({dated}/{len(entries)} עם תאריך), "
                  f"עובר לשיטת מזהים: {feed_title}")
            handle_undated(state, failures, feed_url, feed_title, entries)

    state[FAIL_KEY] = failures
    save_state(state)

    if SHOWS:
        os.makedirs(META_DIR, exist_ok=True)
        with open(META_SHOWS, "w", encoding="utf-8") as f:
            json.dump(SHOWS, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# Publish mode: מיזוג עם ZIPים קיימים של היום + בניית הערות ה-Release
# ---------------------------------------------------------------------------

PART_RE = re.compile(r"^(?P<slug>.+?)(?:_part(?P<n>\d+))?\.zip$")


def part_name(slug, n):
    return f"{slug}.zip" if n == 1 else f"{slug}_part{n}.zip"


def list_parts(folder):
    """{slug: {n: path}} לכל ה-ZIPים בתיקייה."""
    result = {}
    if not os.path.isdir(folder):
        return result
    for fname in os.listdir(folder):
        m = PART_RE.match(fname)
        if m:
            result.setdefault(m.group("slug"), {})[int(m.group("n") or 1)] = os.path.join(folder, fname)
    return result


def add_show(slug, title, prev_parts):
    show_dir = os.path.join(DOWNLOAD_DIR, slug)
    files = [os.path.join(show_dir, f) for f in os.listdir(show_dir)]
    files = [f for f in files if os.path.isfile(f)]
    files.sort(key=lambda p: (os.path.getmtime(p), os.path.basename(p)))

    parts = dict(prev_parts)            # n -> path (prev או out)
    names = {}                          # שם קובץ -> גודל, בכל החלקים הקיימים
    for p in parts.values():
        with zipfile.ZipFile(p) as z:
            for info in z.infolist():
                names[info.filename] = info.file_size

    n = max(parts) if parts else 1
    current_size = os.path.getsize(parts[n]) if n in parts else 0
    opened = {}

    def open_part(k):
        if k in opened:
            return opened[k]
        out_path = os.path.join(OUT_DIR, part_name(slug, k))
        if k in parts and os.path.dirname(parts[k]) == PREV_DIR:
            shutil.copy2(parts[k], out_path)
        mode = "a" if os.path.exists(out_path) else "w"
        zf = zipfile.ZipFile(out_path, mode, zipfile.ZIP_STORED, allowZip64=True)
        zf.comment = title.encode("utf-8")
        opened[k] = zf
        parts[k] = out_path
        return zf

    added = 0
    for path in files:
        name = os.path.basename(path)
        size = os.path.getsize(path)

        if name in names:
            stem, ext = os.path.splitext(name)
            variants = [name] + [f"{stem} ({k}){ext}" for k in range(2, 200)]
            if any(names.get(v) == size for v in variants):
                print(f"כבר קיים ב-ZIP, מדלג: {name}")
                continue
            k = 2
            while f"{stem} ({k}){ext}" in names:
                k += 1
            name = f"{stem} ({k}){ext}"

        if size > ZIP_LIMIT:
            print(f"אזהרה: {name} גדול מ-2GB, ההעלאה ל-GitHub תיכשל")
        if current_size > 0 and current_size + size > ZIP_LIMIT:
            n += 1
            current_size = 0

        open_part(n).write(path, name)
        names[name] = size
        current_size += size + 200
        added += 1

    for zf in opened.values():
        zf.close()
    print(f"[{slug}] נוספו {added} קבצים, חלקים שעודכנו: {sorted(opened)}")


def build_notes():
    today = os.environ.get("TODAY", "")
    final = list_parts(PREV_DIR)
    for slug, p in list_parts(OUT_DIR).items():
        final.setdefault(slug, {}).update(p)   # out גובר על prev

    rows = []
    for slug, parts in final.items():
        count, title = 0, ""
        for n in sorted(parts):
            with zipfile.ZipFile(parts[n]) as z:
                count += len(z.infolist())
                if not title and z.comment:
                    title = z.comment.decode("utf-8", "replace")
        files = ", ".join(os.path.basename(parts[n]) for n in sorted(parts))
        rows.append((title or slug, files, count))
    rows.sort(key=lambda r: r[0].lower())

    lines = [f"## ארכיון פודקאסטים - {today}", "",
             "| קובץ להורדה | שם התוכנית | פרקים |", "|---|---|---|"]
    for title, files, count in rows:
        lines.append(f"| {files} | {title.replace('|', '¦')} | {count} |")
    with open(os.path.join(OUT_DIR, "notes.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def publish():
    if not os.path.exists(META_SHOWS):
        print("אין פרקים חדשים לפרסום.")
        return
    with open(META_SHOWS, "r", encoding="utf-8") as f:
        shows = json.load(f)

    os.makedirs(OUT_DIR, exist_ok=True)
    prev = list_parts(PREV_DIR)
    for slug, title in shows.items():
        if os.path.isdir(os.path.join(DOWNLOAD_DIR, slug)):
            add_show(slug, title, prev.get(slug, {}))
    build_notes()


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "publish":
        publish()
    else:
        main()
