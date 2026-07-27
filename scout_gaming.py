#!/usr/bin/env python3
"""
scout_gaming.py - Raccolta segnali per il brief mattutino di Phane.yt

Gira prima dell'agente (es. cron alle 07:00), interroga RSS + YouTube,
raggruppa le notizie per storia, calcola i segnali di visibilita' e
scrive un JSON che l'agente legge alle 08:00.

Uso:
    export YOUTUBE_API_KEY="..."        # opzionale ma consigliato
    python3 scout_gaming.py

Output:
    ./out/scout_YYYY-MM-DD.json         # candidati del giorno
    ./state/seen_stories.json           # storico anti-duplicato (auto)
"""

import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

try:
    import feedparser
except ImportError:
    sys.exit("Manca feedparser: pip install feedparser")

# ============================================================
# CONFIG
# ============================================================

# Finestra di raccolta: quante ore indietro guardare
LOOKBACK_HOURS = 30

# Quanti cluster passare a YouTube (ogni ricerca costa 100 unita' di quota,
# il default giornaliero e' 10.000, quindi tieniti largo)
YOUTUBE_TOP_N = 15

# Quanti candidati finali scrivere nel JSON (l'agente ne sceglie 5)
MAX_CANDIDATES = 20

# --- Feed anglofoni: definiscono la copertura internazionale ---
FEEDS_EN = {
    "VGC": "https://www.videogameschronicle.com/feed/",
    "Eurogamer": "https://www.eurogamer.net/feed",
    "PC Gamer": "https://www.pcgamer.com/rss/",
    "GamesIndustry": "https://www.gamesindustry.biz/feed",
    "Rock Paper Shotgun": "https://www.rockpapershotgun.com/feed",
    "Polygon": "https://www.polygon.com/rss/index.xml",
    "IGN": "https://feeds.ign.com/ign/games-all",
    "GameSpot": "https://www.gamespot.com/feeds/news/",
    "Nintendo Life": "https://www.nintendolife.com/feeds/latest",
    "Push Square": "https://www.pushsquare.com/feeds/latest",
    "Pure Xbox": "https://www.purexbox.com/feeds/latest",
    "Game Developer": "https://www.gamedeveloper.com/rss.xml",
    "Kotaku": "https://kotaku.com/rss",
}

# --- Feed italiani: servono SOLO a misurare il gap linguistico ---
# Se una storia e' qui dentro, il tuo vantaggio di velocita' e' gia' bruciato.
FEEDS_IT = {
    "Multiplayer": "https://multiplayer.it/feed/rss/news/",
    "Everyeye": "https://www.everyeye.it/rss/notizie.xml",
    "SpazioGames": "https://www.spaziogames.it/feed/",
    "Tom's Hardware IT": "https://www.tomshw.it/feed/",
    "Gamesurf": "https://www.gamesurf.it/rss/",
}

# --- Tematiche: match sul titolo, danno bonus di rilevanza ---
TOPICS = {
    "pokemon":     ["pokemon", "pokémon", "game freak", "nintendo pokemon"],
    "nintendo":    ["nintendo", "switch 2", "switch", "mario", "zelda", "metroid", "kirby"],
    "playstation": ["playstation", "ps5", "ps6", "sony", "psn", "naughty dog", "insomniac"],
    "xbox":        ["xbox", "game pass", "microsoft", "bethesda", "activision", "blizzard"],
    "pc_gaming":   ["pc gaming", "gpu", "nvidia", "amd", "rtx", "steam deck", "framerate"],
    "steam":       ["steam", "valve", "steam deck", "steamos", "half-life"],
    "aaa":         ["aaa", "gta", "rockstar", "ubisoft", "ea ", "call of duty", "assassin"],
    "indie":       ["indie", "solo developer", "small studio", "kickstarter"],
    "easter_egg":  ["easter egg", "hidden", "secret", "datamine", "found in", "discovered"],
    "feel_good":   ["fan", "tribute", "memorial", "charity", "wholesome", "surprise", "gift",
                    "restored", "preserved", "reunited", "raised"],
    "storie":      ["story behind", "history of", "documentary", "interview", "lost media",
                    "cancelled", "prototype", "archive", "leak", "unreleased"],
    "industria":   ["layoff", "layoffs", "lawsuit", "union", "closure", "shut down",
                    "acquisition", "price increase", "delisted", "patent"],
}

# Pesi dello scoring
W = {
    "coverage":    12.0,   # per testata che copre la storia
    "velocity":    18.0,   # copertura concentrata nelle ultime ore
    "it_gap":      25.0,   # nessuna testata italiana ne parla
    "yt_demand":   30.0,   # domanda video misurata su YouTube
    "yt_room":     15.0,   # domanda alta ma pochi video = spazio libero
    "topic":        8.0,   # match con le tue tematiche
    "freshness":   10.0,   # quanto e' recente il primo articolo
}

OUT_DIR = Path("./out")
STATE_DIR = Path("./state")
SEEN_PATH = STATE_DIR / "seen_stories.json"

STOPWORDS = {
    "the", "a", "an", "is", "are", "was", "were", "be", "been", "to", "of", "in",
    "on", "for", "and", "or", "but", "with", "at", "by", "from", "as", "it", "its",
    "this", "that", "these", "those", "has", "have", "had", "will", "would", "can",
    "could", "new", "now", "says", "said", "after", "you", "your", "how", "why",
    "what", "who", "all", "out", "up", "more", "than", "first", "into", "over",
    "il", "lo", "la", "i", "gli", "le", "un", "una", "di", "che", "e", "per",
    "con", "su", "da", "del", "della", "dei", "delle", "al", "alla", "non",
}

# ============================================================
# UTILITY
# ============================================================


def now_utc():
    return datetime.now(timezone.utc)


def parse_entry_date(entry):
    """Estrae la data di pubblicazione da un entry feedparser."""
    for field in ("published_parsed", "updated_parsed"):
        val = entry.get(field)
        if val:
            try:
                return datetime(*val[:6], tzinfo=timezone.utc)
            except (TypeError, ValueError):
                continue
    return None


def tokenize(text):
    """Token normalizzati, senza stopword e senza roba corta."""
    text = text.lower()
    text = re.sub(r"[^a-z0-9àèéìòùáíóúñ\s]", " ", text)
    return {t for t in text.split() if len(t) > 2 and t not in STOPWORDS}


def similarity(tokens_a, tokens_b):
    """
    Overlap coefficient: intersezione / cardinalita' del set piu' piccolo.
    Meglio di Jaccard qui, perche' le testate riscrivono lo stesso fatto con
    titoli di lunghezza molto diversa e Jaccard le penalizza a caso.
    """
    if not tokens_a or not tokens_b:
        return 0.0
    inter = len(tokens_a & tokens_b)
    if inter < 2:  # un solo token in comune non fa una storia
        return 0.0
    return inter / min(len(tokens_a), len(tokens_b))


def slugify(text, maxlen=60):
    s = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return s[:maxlen]


# ============================================================
# RACCOLTA RSS
# ============================================================


def fetch_feeds(feeds, lang, cutoff):
    """Scarica i feed e ritorna la lista di articoli entro la finestra."""
    articles = []
    failures = []

    for source, url in feeds.items():
        try:
            parsed = feedparser.parse(url)
            if parsed.bozo and not parsed.entries:
                failures.append({"source": source, "error": str(parsed.bozo_exception)[:120]})
                continue

            for entry in parsed.entries:
                published = parse_entry_date(entry)
                if published is None or published < cutoff:
                    continue
                title = (entry.get("title") or "").strip()
                if not title:
                    continue
                articles.append({
                    "source": source,
                    "lang": lang,
                    "title": title,
                    "url": entry.get("link", ""),
                    "published": published.isoformat(),
                    "_published_dt": published,
                    "_tokens": tokenize(title),
                })
        except Exception as exc:  # feed morto, timeout, DNS...
            failures.append({"source": source, "error": str(exc)[:120]})

    return articles, failures


# ============================================================
# CLUSTERING
# ============================================================


def cluster_articles(articles, threshold=0.40):
    """
    Raggruppa articoli che parlano dello stesso fatto.
    Greedy single-pass: per ogni articolo cerca il cluster piu' simile,
    altrimenti ne apre uno nuovo. Ordina per data cosi' il primo articolo
    di un cluster e' il piu' vecchio (serve per la velocity).

    Il confronto avviene contro il SEED del cluster, non contro l'unione dei
    token: altrimenti il centroide si gonfia a ogni articolo aggiunto e la
    similarita' crolla artificialmente.
    """
    articles = sorted(articles, key=lambda a: a["_published_dt"])
    clusters = []

    for art in articles:
        best_cl = None
        best_sim = threshold
        for cl in clusters:
            sim = similarity(art["_tokens"], cl["_seed_tokens"])
            if sim >= best_sim:
                best_sim = sim
                best_cl = cl

        if best_cl is not None:
            best_cl["articles"].append(art)
            best_cl["_tokens"] |= art["_tokens"]
        else:
            clusters.append({
                "articles": [art],
                "_seed_tokens": set(art["_tokens"]),
                "_tokens": set(art["_tokens"]),
            })

    return clusters


# ============================================================
# YOUTUBE
# ============================================================


def youtube_demand(query, api_key, published_after_hours=48, max_results=10):
    """
    Misura la domanda video su un argomento.
    Ritorna: n. video caricati di recente, view mediane, view del top video.
    Costo quota: 100 (search.list) + 1 (videos.list) per chiamata.
    """
    if not api_key:
        return None

    after = (now_utc() - timedelta(hours=published_after_hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    search_params = {
        "part": "snippet",
        "q": query,
        "type": "video",
        "order": "viewCount",
        "publishedAfter": after,
        "maxResults": max_results,
        "relevanceLanguage": "en",
        "key": api_key,
    }
    search_url = "https://www.googleapis.com/youtube/v3/search?" + urllib.parse.urlencode(search_params)

    try:
        with urllib.request.urlopen(search_url, timeout=20) as resp:
            data = json.load(resp)
    except Exception as exc:
        return {"error": str(exc)[:120]}

    ids = [item["id"]["videoId"] for item in data.get("items", []) if item.get("id", {}).get("videoId")]
    if not ids:
        return {"video_count": 0, "median_views": 0, "top_views": 0, "top_title": None}

    stats_params = {"part": "statistics,snippet", "id": ",".join(ids), "key": api_key}
    stats_url = "https://www.googleapis.com/youtube/v3/videos?" + urllib.parse.urlencode(stats_params)

    try:
        with urllib.request.urlopen(stats_url, timeout=20) as resp:
            stats = json.load(resp)
    except Exception as exc:
        return {"error": str(exc)[:120]}

    views = []
    top_title = None
    top_views = 0
    for item in stats.get("items", []):
        v = int(item.get("statistics", {}).get("viewCount", 0))
        views.append(v)
        if v > top_views:
            top_views = v
            top_title = item.get("snippet", {}).get("title")

    views.sort()
    median = views[len(views) // 2] if views else 0

    return {
        "video_count": len(views),
        "median_views": median,
        "top_views": top_views,
        "top_title": top_title,
    }


def build_youtube_query(cluster):
    """Costruisce una query dai token piu' distintivi del cluster."""
    counts = defaultdict(int)
    for art in cluster["articles"]:
        for tok in art["_tokens"]:
            counts[tok] += 1
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return " ".join(tok for tok, _ in ranked[:5])


# ============================================================
# SCORING
# ============================================================


def match_topics(cluster):
    """Ritorna le tematiche toccate dal cluster."""
    blob = " ".join(a["title"].lower() for a in cluster["articles"])
    hits = []
    for topic, keywords in TOPICS.items():
        if any(kw in blob for kw in keywords):
            hits.append(topic)
    return hits


def score_cluster(cluster, now):
    """Calcola il punteggio e il dettaglio dei segnali."""
    arts = cluster["articles"]
    en_arts = [a for a in arts if a["lang"] == "en"]
    it_arts = [a for a in arts if a["lang"] == "it"]

    sources_en = {a["source"] for a in en_arts}
    sources_it = {a["source"] for a in it_arts}

    first_dt = min(a["_published_dt"] for a in arts)
    age_hours = (now - first_dt).total_seconds() / 3600

    # copertura: quante testate anglofone, saturata a 6
    coverage = min(len(sources_en), 6) / 6

    # velocity: quota di articoli usciti nelle ultime 8h
    recent = [a for a in en_arts if (now - a["_published_dt"]).total_seconds() / 3600 <= 8]
    velocity = len(recent) / len(en_arts) if en_arts else 0

    # gap italiano: pieno se nessuno in Italia ne parla, MA vale solo in
    # proporzione alla trazione internazionale. Una storia che nessuno copre,
    # ne' in EN ne' in IT, non e' un'opportunita': e' una non-notizia.
    raw_gap = 1.0 if not sources_it else max(0.0, 1 - len(sources_it) / 3)
    it_gap = raw_gap * coverage

    # freshness: massima sotto le 12h, decade a 0 a 30h
    freshness = max(0.0, min(1.0, (30 - age_hours) / 18))

    topics = match_topics(cluster)
    topic_score = min(len(topics), 3) / 3

    # segnali YouTube
    yt = cluster.get("youtube") or {}
    yt_available = bool(yt) and "error" not in yt and yt.get("video_count") is not None
    yt_demand = 0.0
    yt_room = 0.0
    if yt_available and yt.get("video_count"):
        # domanda: mediana view su scala radice, 100k = pieno
        median = max(yt.get("median_views", 0), 1)
        yt_demand = min(1.0, (median ** 0.5) / (100000 ** 0.5))
        # spazio: domanda alta ma pochi video gia' caricati
        if yt["video_count"] <= 4 and median > 5000:
            yt_room = 1.0
        elif yt["video_count"] <= 7 and median > 20000:
            yt_room = 0.6

    parts = {
        "coverage": coverage,
        "velocity": velocity,
        "it_gap": it_gap,
        "topic": topic_score,
        "freshness": freshness,
    }
    if yt_available:
        parts["yt_demand"] = yt_demand
        parts["yt_room"] = yt_room

    # normalizzo sui soli segnali disponibili: un cluster senza dati YouTube
    # non deve risultare peggiore solo perche' non ha ricevuto la quota API
    earned = sum(W[k] * v for k, v in parts.items())
    available = sum(W[k] for k in parts)
    total = 100 * earned / available if available else 0.0

    return round(total, 1), {
        "coverage": round(coverage, 2),
        "velocity": round(velocity, 2),
        "it_gap": round(it_gap, 2),
        "yt_demand": round(yt_demand, 2),
        "yt_room": round(yt_room, 2),
        "topic": round(topic_score, 2),
        "freshness": round(freshness, 2),
    }, topics, age_hours, sources_en, sources_it


# ============================================================
# STORICO ANTI-DUPLICATO
# ============================================================


def load_seen():
    if SEEN_PATH.exists():
        try:
            return json.loads(SEEN_PATH.read_text())
        except json.JSONDecodeError:
            return {}
    return {}


def save_seen(seen, candidates):
    """Registra i candidati proposti oggi, tiene 30 giorni di storico."""
    today = now_utc().date().isoformat()
    for c in candidates:
        seen[c["story_id"]] = {"date": today, "title": c["headline"]}

    cutoff = (now_utc() - timedelta(days=30)).date().isoformat()
    seen = {k: v for k, v in seen.items() if v.get("date", "") >= cutoff}

    STATE_DIR.mkdir(parents=True, exist_ok=True)
    SEEN_PATH.write_text(json.dumps(seen, indent=2, ensure_ascii=False))
    return seen


# ============================================================
# MAIN
# ============================================================


def main():
    now = now_utc()
    cutoff = now - timedelta(hours=LOOKBACK_HOURS)
    api_key = os.environ.get("YOUTUBE_API_KEY")

    print(f"[scout] finestra: ultime {LOOKBACK_HOURS}h", file=sys.stderr)

    en_articles, en_fail = fetch_feeds(FEEDS_EN, "en", cutoff)
    it_articles, it_fail = fetch_feeds(FEEDS_IT, "it", cutoff)
    print(f"[scout] articoli: {len(en_articles)} EN, {len(it_articles)} IT", file=sys.stderr)

    clusters = cluster_articles(en_articles + it_articles)
    # tieni solo cluster con almeno una fonte anglofona
    clusters = [c for c in clusters if any(a["lang"] == "en" for a in c["articles"])]
    print(f"[scout] cluster: {len(clusters)}", file=sys.stderr)

    # primo scoring senza YouTube, per decidere chi merita la quota
    prelim = []
    for cl in clusters:
        score, _, _, _, _, _ = score_cluster(cl, now)
        prelim.append((score, cl))
    prelim.sort(key=lambda x: -x[0])

    # YouTube solo sui top N
    if api_key:
        for i, (_, cl) in enumerate(prelim[:YOUTUBE_TOP_N]):
            query = build_youtube_query(cl)
            cl["youtube"] = youtube_demand(query, api_key)
            cl["youtube_query"] = query
            time.sleep(0.3)
        print(f"[scout] YouTube interrogato su {min(YOUTUBE_TOP_N, len(prelim))} cluster", file=sys.stderr)
    else:
        print("[scout] YOUTUBE_API_KEY assente, salto i segnali video", file=sys.stderr)

    seen = load_seen()

    # scoring finale
    results = []
    for _, cl in prelim:
        score, signals, topics, age_h, src_en, src_it = score_cluster(cl, now)
        headline = cl["articles"][0]["title"]
        story_id = slugify(" ".join(sorted(list(cl["_tokens"]))[:6]))

        results.append({
            "story_id": story_id,
            "score": score,
            "already_proposed": story_id in seen,
            "headline": headline,
            "topics": topics,
            "age_hours": round(age_h, 1),
            "signals": signals,
            "coverage_en": sorted(src_en),
            "coverage_it": sorted(src_it),
            "youtube": cl.get("youtube"),
            "youtube_query": cl.get("youtube_query"),
            "articles": [
                {"source": a["source"], "title": a["title"], "url": a["url"], "published": a["published"]}
                for a in cl["articles"]
            ],
        })

    results.sort(key=lambda r: (r["already_proposed"], -r["score"]))
    results = results[:MAX_CANDIDATES]

    payload = {
        "generated_at": now.isoformat(),
        "lookback_hours": LOOKBACK_HOURS,
        "feed_failures": en_fail + it_fail,
        "youtube_enabled": bool(api_key),
        "candidates": results,
    }

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = OUT_DIR / f"scout_{now.date().isoformat()}.json"
    out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False))

    # copia a nome fisso: e' quella che legge l'agente, cosi' l'URL non cambia
    latest_path = OUT_DIR / "latest.json"
    latest_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False))

    save_seen(seen, results)

    if en_fail or it_fail:
        print(f"[scout] feed falliti: {[f['source'] for f in en_fail + it_fail]}", file=sys.stderr)
    print(f"[scout] scritto {out_path} con {len(results)} candidati", file=sys.stderr)


if __name__ == "__main__":
    main()
