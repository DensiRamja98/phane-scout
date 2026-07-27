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
import math
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
    "pokemon":     ["pokemon", "pokémon", "game freak", "pokemon company", "masuda",
                    "ohmori", "pocket monsters"],
    "nintendo":    ["nintendo", "switch 2", "switch", "mario", "zelda", "metroid", "kirby",
                    "miyamoto", "aonuma", "furukawa", "splatoon", "animal crossing",
                    "donkey kong", "smash bros", "fire emblem", "xenoblade"],
    "playstation": ["playstation", "ps5", "ps6", "sony", "psn", "naughty dog", "insomniac",
                    "santa monica studio", "guerrilla", "bluepoint", "housemarque",
                    "sucker punch", "team asobi", "ryan", "hulst"],
    "xbox":        ["xbox", "game pass", "microsoft", "bethesda", "activision", "blizzard",
                    "obsidian", "id software", "arkane", "halo", "gears of war",
                    "spencer", "series x", "series s"],
    "pc_gaming":   ["pc gaming", "gpu", "nvidia", "amd", "rtx", "steam deck", "framerate",
                    "frame rate", "dlss", "fsr", "ray tracing", "benchmark", "vram",
                    "optimization", "pc port", "stutter"],
    "steam":       ["steam", "valve", "steam deck", "steamos", "half-life", "counter-strike",
                    "steam sale", "wishlist", "early access", "gabe newell"],
    "aaa":         ["aaa", "gta", "grand theft auto", "rockstar", "ubisoft", "ea sports",
                    "electronic arts", "call of duty", "assassin's creed", "far cry",
                    "battlefield", "capcom", "square enix", "resident evil", "final fantasy",
                    "sequel", "remake", "remaster", "reboot"],
    "indie":       ["indie", "solo developer", "solo dev", "small studio", "kickstarter",
                    "two-person", "one-man", "first game", "debut game"],
    "easter_egg":  ["easter egg", "hidden", "secret", "datamine", "datamined", "found in",
                    "discovered", "uncovered", "buried in", "years later", "nobody noticed",
                    "hidden message", "unused"],
    "feel_good":   ["fan", "fans", "tribute", "memorial", "charity", "wholesome", "surprise",
                    "gift", "restored", "preserved", "reunited", "raised", "donated",
                    "community came together", "helped"],
    "storie":      ["story behind", "history of", "documentary", "interview", "lost media",
                    "cancelled", "canceled", "prototype", "archive", "leak", "leaked",
                    "unreleased", "never released", "scrapped", "shelved", "what happened to",
                    "oral history", "behind the scenes"],
    "industria":   ["layoff", "layoffs", "lawsuit", "sued", "union", "unionize", "closure",
                    "shut down", "shutting down", "studio closed", "acquisition", "acquired",
                    "price increase", "price hike", "delisted", "patent", "microtransaction",
                    "live service", "subscription", "delisting", "server shutdown",
                    "hacked", "malware", "data breach", "ddos", "cheat", "banned",
                    "ban wave", "drm", "denuvo", "refund"],
}

# --- Filtri anti-rumore, ricavati dal primo output reale ---
# Polygon, IGN e Kotaku mescolano cinema, serie TV, anime e giochi da tavolo
# nello stesso feed dei videogiochi. Questi articoli vengono scartati.
HARD_EXCLUDE = [
    "anime", "netflix", "star trek", "star wars series", "marvel", "dc comics",
    "movie review", "film review", "tv show", "tv series", "streaming right now",
    "to stream", "where to watch", "thriller", "best movies", "best shows",
    "comic con", "sdcc", "box office", "trailer breakdown",
    "dungeons & dragons", "d&d", "magic: the gathering", "board game",
    "trading card", "warhammer", "tabletop", "lego set",
    # articoli su serie TV: "House of the Dragon season 3 episode 6 ending
    # explained" era passato indenne al primo filtro
    "ending explained", "recap", "who dies in", "season finale",
    "house of the dragon", "the last of us season", "fallout season",
]

# "season 3 episode 6" e simili: pattern, non parola singola
EXCLUDE_PATTERNS = [
    re.compile(r"\bseason\s+\d+\s+episode\s+\d+", re.I),
    re.compile(r"\bs\d+e\d+\b", re.I),
    re.compile(r"\bepisode\s+\d+\s+(recap|review|ending)", re.I),
]

# Formati che non fanno un video: liste sconti, sondaggi alla community,
# editoriali senza notizia, review vecchie ripubblicate nel feed.
SOFT_PENALTY = [
    "best deals", "deals today", "deal of the", "discount", "on sale now",
    "talking point", "what have you", "how do you feel", "poll:", "your thoughts",
    "review (20",  # PC Gamer ripubblica vecchie review con data odierna
    "weekly roundup", "this week in", "what are you playing",
]


def is_noise(title):
    """True se l'articolo va scartato prima ancora del clustering."""
    t = title.lower()
    if any(kw in t for kw in HARD_EXCLUDE):
        return True
    return any(p.search(title) for p in EXCLUDE_PATTERNS)


def is_weak_format(title):
    """True se il titolo e' un formato che raramente diventa un buon short."""
    t = title.lower()
    return any(kw in t for kw in SOFT_PENALTY)


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
    # articoli, preposizioni, congiunzioni
    "the", "a", "an", "is", "are", "was", "were", "be", "been", "being", "to", "of",
    "in", "on", "for", "and", "or", "but", "with", "at", "by", "from", "as", "it",
    "its", "this", "that", "these", "those", "has", "have", "had", "will", "would",
    "can", "could", "should", "may", "might", "must", "shall", "does", "did", "do",
    "into", "over", "under", "about", "after", "before", "than", "then", "when",
    "while", "where", "which", "who", "whom", "whose", "what", "why", "how",
    # verbi e avverbi generici
    "get", "gets", "got", "getting", "make", "makes", "made", "take", "takes",
    "look", "looks", "looking", "come", "comes", "coming", "going", "goes", "went",
    "say", "says", "said", "see", "sees", "seen", "know", "knows", "think", "want",
    "give", "gives", "given", "try", "trying", "miss", "put", "let", "keep",
    "just", "even", "still", "already", "never", "always", "now", "soon", "back",
    "here", "there", "again", "also", "very", "really", "quite", "actually",
    "more", "most", "less", "least", "much", "many", "some", "any", "all", "both",
    "each", "every", "other", "another", "same", "own", "such", "only", "out",
    "up", "down", "off", "away", "you", "your", "our", "their", "his", "her",
    "them", "they", "we", "us", "me", "my", "one", "two", "first", "second",
    "last", "next", "new", "old", "good", "bad", "best", "worst", "better",
    "big", "little", "long", "right", "way", "thing", "things", "point", "lot",
    "free", "full", "real", "sure", "like", "likes", "want", "wants", "need",
    # italiano
    "il", "lo", "la", "i", "gli", "le", "un", "una", "uno", "di", "che", "e",
    "per", "con", "su", "da", "del", "della", "dei", "delle", "al", "alla",
    "non", "come", "piu", "anche", "solo", "dopo", "prima", "sono", "essere",
    "questo", "questa", "suo", "sua", "loro", "tutto", "tutti", "ora", "gia",
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


def compute_idf(articles):
    """
    Quanto e' raro ogni token nella giornata.
    'game' compare ovunque e non dice niente; 'myst' compare in due titoli
    e quasi certamente indica la stessa storia. L'IDF cattura la differenza.
    """
    n = max(len(articles), 1)
    df = defaultdict(int)
    for art in articles:
        for tok in art["_tokens"]:
            df[tok] += 1
    return {tok: math.log(n / count) + 1.0 for tok, count in df.items()}


def similarity(tokens_a, tokens_b, idf=None):
    """
    Overlap coefficient, deliberatamente conservativo: servono almeno due
    token in comune.

    Ho provato a pesare per IDF sperando di agganciare i titoli che
    condividono un solo nome proprio ("Myst"), ma su ~15 articoli al giorno
    il conteggio e' troppo piccolo: un token condiviso compare per
    definizione due volte, quindi risulta MENO raro di quelli unici e la
    formula lavora al contrario. Meglio due cluster separati che uno
    sbagliato: le storie sospette finiscono in "related", e decide l'agente.
    """
    if not tokens_a or not tokens_b:
        return 0.0
    inter = tokens_a & tokens_b
    if len(inter) < 2:
        return 0.0
    return len(inter) / min(len(tokens_a), len(tokens_b))


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
                if not title or is_noise(title):
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


def cluster_articles(articles, idf=None, threshold=0.42):
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
            sim = similarity(art["_tokens"], cl["_seed_tokens"], idf)
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


def find_related(clusters, all_articles, max_df=2, min_len=4):
    """
    Cluster che condividono un token raro senza aver superato la soglia.
    Tipico caso: due testate scrivono della stessa notizia con parole
    diverse e in comune resta solo il nome proprio. Non li unisco, li
    segnalo: e' un giudizio che l'agente fa meglio di una euristica.
    """
    df = defaultdict(int)
    for art in all_articles:
        for tok in art["_tokens"]:
            df[tok] += 1

    rare_index = defaultdict(list)
    for i, cl in enumerate(clusters):
        for tok in cl["_tokens"]:
            if df.get(tok, 99) <= max_df and len(tok) >= min_len:
                rare_index[tok].append(i)

    related = defaultdict(set)
    for tok, idxs in rare_index.items():
        if len(idxs) < 2:
            continue
        for i in idxs:
            for j in idxs:
                if i != j:
                    related[i].add((j, tok))
    return related


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


def build_youtube_query(cluster, idf=None):
    """
    Query costruita coi token piu' distintivi del cluster.

    Senza IDF l'ordinamento a parita' di frequenza ripiegava sull'alfabeto e
    usciva roba tipo "actually fantastic game get looking": le prime cinque
    parole in ordine alfabetico. Pesando per rarita' escono invece i nomi
    propri, che sono quello che serve per cercare su YouTube.
    """
    counts = defaultdict(int)
    for art in cluster["articles"]:
        for tok in art["_tokens"]:
            counts[tok] += 1
    idf = idf or {}
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], -idf.get(kv[0], 1.0)))
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

    # velocity: quota di articoli usciti nelle ultime 14h.
    # Non 8: il brief gira alle 5-7 del mattino, e a quell'ora le notizie
    # "calde" sono quelle della sera prima. Con 8h la velocity era 0 su tutto.
    recent = [a for a in en_arts if (now - a["_published_dt"]).total_seconds() / 3600 <= 14]
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

    # formati che raramente diventano un buon short: liste sconti, sondaggi,
    # review vecchie ripubblicate. Non li scarto, li mando in fondo.
    weak = all(is_weak_format(a["title"]) for a in arts)
    if weak:
        total *= 0.35

    return round(total, 1), {
        "coverage": round(coverage, 2),
        "velocity": round(velocity, 2),
        "it_gap": round(it_gap, 2),
        "yt_demand": round(yt_demand, 2),
        "yt_room": round(yt_room, 2),
        "topic": round(topic_score, 2),
        "freshness": round(freshness, 2),
        "weak_format": weak,
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

    all_articles = en_articles + it_articles
    idf = compute_idf(all_articles)
    clusters = cluster_articles(all_articles, idf)
    # tieni solo cluster con almeno una fonte anglofona
    clusters = [c for c in clusters if any(a["lang"] == "en" for a in c["articles"])]
    related_map = find_related(clusters, all_articles)
    for i, cl in enumerate(clusters):
        cl["_index"] = i
    print(f"[scout] cluster: {len(clusters)}, con correlazioni: {len(related_map)}", file=sys.stderr)

    # primo scoring senza YouTube, per decidere chi merita la quota
    prelim = []
    for cl in clusters:
        score, _, _, _, _, _ = score_cluster(cl, now)
        prelim.append((score, cl))
    prelim.sort(key=lambda x: -x[0])

    # YouTube solo sui top N
    if api_key:
        queried = prelim[:YOUTUBE_TOP_N]
        for _, cl in queried:
            query = build_youtube_query(cl, idf)
            cl["youtube"] = youtube_demand(query, api_key)
            cl["youtube_query"] = query
            time.sleep(0.3)
        print(f"[scout] YouTube interrogato su {len(queried)} cluster", file=sys.stderr)

        # La classifica finale esce SOLO da questi. Altrimenti un cluster mai
        # interrogato batte uno interrogato con domanda video bassa: il
        # punteggio normalizzato lo premia per il segnale che gli manca.
        prelim = queried
    else:
        print("[scout] YOUTUBE_API_KEY assente, salto i segnali video", file=sys.stderr)

    seen = load_seen()
    today = now.date().isoformat()

    # scoring finale
    results = []
    for _, cl in prelim:
        score, signals, topics, age_h, src_en, src_it = score_cluster(cl, now)
        headline = cl["articles"][0]["title"]
        story_id = slugify(" ".join(sorted(list(cl["_tokens"]))[:6]))

        # "gia' proposta" solo se compariva in un brief di un giorno PRECEDENTE.
        # Altrimenti bastava rilanciare il workflow due volte per marcare
        # tutto come vecchio e svuotare la classifica.
        prev = seen.get(story_id)
        already = bool(prev) and prev.get("date", "") < today

        results.append({
            "story_id": story_id,
            "score": score,
            "already_proposed": already,
            "headline": headline,
            "topics": topics,
            "age_hours": round(age_h, 1),
            "signals": signals,
            "coverage_en": sorted(src_en),
            "coverage_it": sorted(src_it),
            "youtube": cl.get("youtube"),
            "youtube_query": cl.get("youtube_query"),
            "related": [
                {"headline": clusters[j]["articles"][0]["title"], "shared_term": tok}
                for j, tok in sorted(related_map.get(cl.get("_index", -1), []))[:3]
            ],
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
