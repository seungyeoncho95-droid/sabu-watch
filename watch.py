#!/usr/bin/env python3
"""사회부 당번용 속보 감시기.

네이버 뉴스 검색 API + 구글 뉴스 RSS를 주기적으로 폴링해서
사회부 관련 [단독]·[속보]·주요 사건사고 기사가 뜨면
macOS 알림(배너+사운드)을 즉시 보낸다.

사용법:
    python3 watch.py            # 3분 간격 무한 감시 (Ctrl+C로 종료)
    python3 watch.py --once     # 1회만 돌고 종료 (테스트용)
    python3 watch.py --interval 120   # 폴링 간격(초) 변경
"""

import argparse
import html
import json
import os
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
STATE_FILE = BASE_DIR / "state.json"
LOG_FILE = BASE_DIR / "alerts.log"
# 네이버 API 자격증명은 community-scraper의 .env를 재사용
ENV_CANDIDATES = [
    BASE_DIR / ".env",
    Path.home() / "community-scraper" / ".env",
]

KST = timezone(timedelta(hours=9))

# ── 필터 규칙 ────────────────────────────────────────────────

# 사회부 관련성 판별 키워드 (제목+요약에서 검색)
SOCIAL_KEYWORDS = [
    # 법조
    "법원", "재판", "판결", "선고", "영장", "구속", "검찰", "기소", "송치",
    "대법원", "헌재", "헌법재판소", "공수처", "항소", "실형", "무죄", "국선",
    "압수수색", "구형", "국과수", "구치소", "교도소", "보호관찰", "전자발찌",
    "특검", "특별검사", "공판", "공소", "피의자", "피고인", "진술", "변호인",
    "소환", "내란", "계엄", "탄핵", "위증",
    # 경찰·사건
    "경찰", "수사", "입건", "체포", "검거", "폭행", "살인", "살해", "사망",
    "숨졌", "숨진", "숨져", "실종", "마약", "성폭행", "성추행", "성착취",
    "스토킹", "학대", "사기", "횡령", "배임", "보이스피싱", "전세사기",
    "묻지마", "흉기", "총기", "테러", "뺑소니", "음주운전", "유괴", "납치",
    "변사", "극단적 선택", "투신",
    # 재난·재해·사고
    "화재", "폭발", "붕괴", "추락", "침수", "산사태", "지진", "익사",
    "감전", "매몰", "전복", "충돌", "탈선", "정전", "폭우", "폭염", "한파",
    "태풍", "호우", "대피", "소방", "119", "구조", "심정지", "중태",
    "산재", "중대재해", "질식", "가스 누출", "누출",
    # 행정·교육·복지·노동
    "서울시", "시청", "구청", "자치구", "교육청", "학교폭력", "학폭",
    "어린이집", "유치원", "요양원", "병원", "응급실", "복지", "노조",
    "파업", "집회", "시위", "전장연", "이태원", "참사",
]

# 제목에 있으면 제외 (타 부서·노이즈)
EXCLUDE_KEYWORDS = [
    "코스피", "코스닥", "주가", "증시", "환율", "비트코인", "가상자산",
    "분양", "청약", "금리", "영업이익", "실적 발표", "신제품", "출시",
    "아이돌", "컴백", "앨범", "뮤직", "예능", "드라마", "시청률",
    "KBO", "프로야구", "K리그", "프로축구", "손흥민", "이강인", "메이저리그",
    "홈런", "골 폭발", "배구", "V리그",
    # 보험사명에 '화재'가 들어가 오탐되는 경우
    "삼성화재", "메리츠화재", "현대해상", "DB손해보험", "KB손해보험", "화재보험",
]

# [단독] / [속보] 류 머리표 감지
DANDOK_RE = re.compile(r"[\[\(<〈【`']\s*단독")
SOKBO_RE = re.compile(r"[\[\(<〈【`']\s*(속보|긴급)")

# 사건사고 심각성 판별 (머리표 없는 기사용)
SEVERITY_RE = re.compile(
    r"사망|숨졌|숨진|숨져|심정지|중태|매몰|실종|붕괴|폭발|전소|대피|"
    r"부상|참변|참사|급파|아수라장"
)

# 해설·칼럼·인터뷰류 (머리표 없는 사건사고 판별에서 제외)
OPINION_RE = re.compile(r"칼럼|기고|사설|기자수첩|데스크|인터뷰|논평|\?\s*$")

# 소관기관 추출 (긴 접미어를 앞에 둬야 대법원이 '법원'으로 잘리지 않음)
AGENCY_RE = re.compile(
    r"[가-힣]{1,8}?(?:경찰서|경찰청|해양경찰서|해경|지검|고검|대검|검찰청|"
    r"지법|고법|대법원|헌법재판소|헌재|가정법원|행정법원|회생법원|법원|공수처|"
    r"구청|시청|군청|도청|교육청|소방서|소방본부|교도소|구치소|세관|국과수)"
)

# 네이버 뉴스 검색 질의 목록
# (구글 RSS도 병행했으나 네이버 뉴스 링크로만 알림하기로 하면서 제거 — 2026-07-12)
NAVER_QUERIES = ["단독", "속보", "화재", "붕괴", "추락 사망", "흉기", "실종", "폭발 사고"]

# 시작 직후 과거 기사 알림 폭주 방지: 첫 사이클은 최근 N분 이내만
FIRST_RUN_LOOKBACK_MIN = 30
# GitHub Actions 무료 cron이 1~3.5시간씩 밀리는 게 실측 확인됨(2026-07-17) —
# 실행이 밀려도 그 사이 기사를 놓치지 않도록 허용 나이를 넉넉히 둔다.
# (이미 본 기사는 seen/클러스터가 막아주므로 늘려도 재알림 없음)
LOOKBACK_MIN = 360          # 평상시 허용 기사 나이(분)
MAX_ALERTS_PER_CYCLE = 15   # 한 사이클 알림 상한 (실행 공백 후 몰림 대비)
STATE_TTL_HOURS = 72        # 본 기사 기록 보관 시간

# ── 유틸 ────────────────────────────────────────────────────


def load_env():
    """자격증명 로드 — 환경변수(GitHub Actions Secrets)가 최우선, 다음 `.env` 파일들."""
    creds = {}
    for key in ("NAVER_CLIENT_ID", "NAVER_CLIENT_SECRET",
                "TELEGRAM_BOT_TOKEN", "TELEGRAM_CHAT_ID"):
        if os.environ.get(key):
            creds[key] = os.environ[key]
    for path in ENV_CANDIDATES:
        if not path.exists():
            continue
        for line in path.read_text().splitlines():
            line = line.strip()
            if line.startswith("#") or "=" not in line:
                continue
            k, _, v = line.partition("=")
            creds.setdefault(k.strip(), v.strip().strip('"').strip("'"))
    return creds


def clean_title(raw):
    """네이버 API의 <b> 태그·HTML 엔티티 제거."""
    return html.unescape(re.sub(r"</?b>", "", raw)).strip()


def norm_title(title):
    """중복 판별용 제목 정규화 (머리표·기호·공백 제거)."""
    t = re.sub(r"[\[\(<〈【].{1,6}?[\]\)>〉】]", "", title)  # [단독] 등 머리표 제거
    t = re.sub(r"[^가-힣a-zA-Z0-9]", "", t)
    return t[:60]


def bigrams(s):
    return {s[i:i + 2] for i in range(len(s) - 1)}


# 사건 클러스터 병합 기준: 새 제목 조각의 38% 이상이 클러스터 어휘에 포함되면 같은 사건.
# 클러스터가 병합된 기사들의 어휘를 계속 흡수하므로 "승조원→일병→병사",
# "고성→동해→NLL" 식으로 표현이 바뀌는 후속 기사도 잡힌다
# (실측: 해군 실종 후속 15건이 0.43~0.94, 별개 사건은 0.3 미만 — 그 사이 값).
CLUSTER_THRESHOLD = 0.38
CLUSTER_MAX_BIGRAMS = 300  # 어휘가 무한정 커져 무관한 기사까지 삼키는 것 방지


def find_cluster(clusters, cand_bigrams):
    """새 기사가 속하는 기존 사건 클러스터를 찾는다. 없으면 None."""
    best, best_ratio = None, 0.0
    for c in clusters:
        ratio = len(cand_bigrams & set(c["b"])) / max(1, len(cand_bigrams))
        if ratio > best_ratio:
            best, best_ratio = c, ratio
    return best if best_ratio >= CLUSTER_THRESHOLD else None


def http_get(url, headers=None, timeout=15):
    req = urllib.request.Request(url, headers=headers or {"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


# ── 수집 ────────────────────────────────────────────────────


def fetch_naver(query, cid, csec):
    """네이버 뉴스 검색 API — 최신순 50건."""
    url = (
        "https://openapi.naver.com/v1/search/news.json?"
        + urllib.parse.urlencode({"query": query, "display": 50, "sort": "date"})
    )
    data = json.loads(http_get(url, {"X-Naver-Client-Id": cid, "X-Naver-Client-Secret": csec}))
    items = []
    for it in data.get("items", []):
        try:
            pub = parsedate_to_datetime(it["pubDate"])
        except Exception:
            continue
        # 네이버 뉴스에 송고된 기사만 (미송고 기사는 link가 언론사 원문 주소)
        link = it.get("link", "")
        if "news.naver.com" not in link:
            continue
        items.append({
            "title": clean_title(it["title"]),
            "desc": clean_title(it.get("description", "")),
            "link": link,
            "pub": pub,
            "source": "네이버",
            "query": query,
        })
    return items


# ── 판별 ────────────────────────────────────────────────────


def categorize(text):
    """알림 배너에 붙일 대분류."""
    for cat, kws in [
        ("법조", ["법원", "재판", "판결", "선고", "영장", "검찰", "기소", "대법원", "헌재", "공수처", "구형", "실형", "무죄"]),
        ("재난·사고", ["화재", "폭발", "붕괴", "추락", "침수", "산사태", "지진", "매몰", "탈선", "전복", "태풍", "호우", "대피", "소방", "산재", "중대재해"]),
        ("경찰·사건", ["경찰", "구속", "입건", "체포", "검거", "살인", "살해", "폭행", "흉기", "마약", "실종", "사망", "숨졌", "숨진", "스토킹", "학대", "사기"]),
        ("행정", ["서울시", "시청", "구청", "자치구", "교육청"]),
    ]:
        if any(k in text for k in kws):
            return cat
    return "사회"


def judge(item):
    """알림 대상 여부와 라벨을 반환. 대상이 아니면 None."""
    title, desc = item["title"], item["desc"]
    text = title + " " + desc

    if any(k in title for k in EXCLUDE_KEYWORDS):
        return None
    # 제목에 키워드가 있거나, 제목+요약에 서로 다른 키워드 2개 이상
    # (요약에 한 단어만 스치는 기사 — "지진 위험 적은 입지" 류 — 오탐 방지)
    is_social = any(k in title for k in SOCIAL_KEYWORDS) or sum(
        k in text for k in SOCIAL_KEYWORDS
    ) >= 2

    if DANDOK_RE.search(title):
        return ("단독", categorize(text)) if is_social else None
    if SOKBO_RE.search(title):
        return ("속보", categorize(text)) if is_social else None
    # 머리표 없는 사건사고: 심각성 어휘가 제목에 있어야 알림 (해설·칼럼류 제외)
    if (
        item["query"] not in ("단독", "속보")
        and is_social
        and SEVERITY_RE.search(title)
        and not OPINION_RE.search(title)
    ):
        return ("사건사고", categorize(text))
    return None


# ── 알림 ────────────────────────────────────────────────────


def notify_banner(label, cat, title):
    """macOS 배너 알림 + 사운드 (텔레그램 미설정·실패 시 폴백, 맥에서만)."""
    if sys.platform != "darwin":
        return
    def esc(s):
        return s.replace("\\", "\\\\").replace('"', '\\"')
    script = (
        f'display notification "{esc(title)}" '
        f'with title "🚨 [{label}] {cat}" sound name "Glass"'
    )
    try:
        subprocess.run(["osascript", "-e", script], capture_output=True)
    except OSError:
        pass


PRESS_CACHE = {}  # 네이버 언론사 id(oid) → 언론사명 (페이지 조회 실패 시 폴백)


def fetch_article_meta(link):
    """네이버 기사 페이지에서 (언론사명, 전체 제목) 추출.

    검색 API가 긴 제목을 "..."로 말줄임하므로 전체 제목은 페이지의
    og:title에서 가져온다. 실패 시 (캐시된 언론사명 또는 '미상', None).
    """
    m = re.search(r"/article/(\d+)/", link or "")
    oid = m.group(1) if m else None
    try:
        page = http_get(link).decode("utf-8", "ignore")
        m_press = re.search(r'property="og:article:author" content="([^"|]+)', page)
        m_title = re.search(r'property="og:title" content="([^"]+)"', page)
        press = m_press.group(1).strip() if m_press else "미상"
        title = html.unescape(m_title.group(1)).strip() if m_title else None
        if oid and m_press:
            PRESS_CACHE[oid] = press
        return press, title
    except Exception:
        return PRESS_CACHE.get(oid, "미상"), None


def extract_agency(text):
    """제목·요약에서 소관기관(○○경찰서, ○○지법 등) 추출. 없으면 대분류로 대체."""
    found = []
    for m in AGENCY_RE.finditer(text):
        if m.group(0) not in found:
            found.append(m.group(0))
    return "·".join(found[:2]) if found else categorize(text)


def notify_telegram(token, chat_id, label, cat, item):
    """텔레그램 메시지 전송: @언론사명/전체제목=소관기관 + 링크."""
    press, full_title = fetch_article_meta(item.get("link", ""))
    title = full_title or item["title"]  # 페이지 조회 실패 시 API 제목(말줄임 가능)
    agency = extract_agency(title + " " + item.get("desc", ""))
    text = (
        f"@{html.escape(press)}/{html.escape(title)}={html.escape(agency)}\n"
        f"{item.get('link', '')}"
    )
    payload = json.dumps({"chat_id": chat_id, "text": text, "parse_mode": "HTML"}).encode()
    req = urllib.request.Request(
        f"https://api.telegram.org/bot{token}/sendMessage",
        data=payload,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=10) as resp:
        return json.loads(resp.read()).get("ok", False)


def notify(tg, label, cat, item):
    """텔레그램 우선, 미설정이거나 실패하면 macOS 배너."""
    token, chat_id = tg
    if token and chat_id:
        try:
            if notify_telegram(token, chat_id, label, cat, item):
                return
        except Exception as e:
            print(f"  ⚠️ 텔레그램 전송 실패(배너로 대체): {e}", flush=True)
    notify_banner(label, cat, item["title"])


def log_alert(now, label, cat, item):
    line = f"[{now:%H:%M}] 🚨 [{label}·{cat}] {item['title']}\n        {item['link']}"
    print(line, flush=True)
    with LOG_FILE.open("a") as f:
        f.write(f"{now:%Y-%m-%d %H:%M} [{label}·{cat}] ({item['source']}) {item['title']}\n{item['link']}\n\n")


# ── 상태(중복 방지) ─────────────────────────────────────────


def load_state():
    """상태 로드. seen=본 기사(링크·제목), clusters=알림 나간 사건 클러스터."""
    if STATE_FILE.exists():
        try:
            data = json.loads(STATE_FILE.read_text())
            if "seen" in data:
                return data
            # 구버전(평면 dict) 마이그레이션
            return {"seen": {k: v for k, v in data.items() if not k.startswith("A:")},
                    "clusters": []}
        except Exception:
            pass
    return {"seen": {}, "clusters": []}


def save_state(state):
    # 오래된 기록 정리 (클러스터는 마지막 병합 시점 기준 — 진행 중 사건은 계속 억제)
    cutoff = time.time() - STATE_TTL_HOURS * 3600
    state["seen"] = {k: v for k, v in state["seen"].items() if v > cutoff}
    state["clusters"] = [c for c in state["clusters"] if c["ts"] > cutoff]
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False))
    return state


# ── 메인 루프 ───────────────────────────────────────────────


def run_cycle(cid, csec, tg, state, first_run):
    now = datetime.now(KST)
    lookback = timedelta(minutes=FIRST_RUN_LOOKBACK_MIN if first_run else LOOKBACK_MIN)

    items = []
    for q in NAVER_QUERIES:
        try:
            items += fetch_naver(q, cid, csec)
        except Exception as e:
            print(f"  ⚠️ 네이버 '{q}' 수집 실패: {e}", flush=True)
        time.sleep(0.5)  # 네이버 초당 호출 제한(429) 회피

    seen, clusters = state["seen"], state["clusters"]
    alerted = merged = 0
    for item in items:
        if not item["link"] or now - item["pub"] > lookback:
            continue
        key_link = "L:" + item["link"]
        nt = norm_title(item["title"])
        key_title = "T:" + nt
        if key_link in seen or key_title in seen:
            continue
        seen[key_link] = seen[key_title] = time.time()

        verdict = judge(item)
        if not verdict:
            continue
        label, cat = verdict

        # 이미 알림 나간 사건의 후속·타 매체 기사면 클러스터에 병합 (로그만 남김)
        cand = bigrams(nt)
        cluster = find_cluster(clusters, cand)
        if cluster:
            merged += 1
            if len(cluster["b"]) < CLUSTER_MAX_BIGRAMS:
                cluster["b"] = list(set(cluster["b"]) | cand)
            cluster["ts"] = time.time()
            with LOG_FILE.open("a") as f:
                f.write(f"{now:%Y-%m-%d %H:%M} (후속기사 병합→{cluster['t'][:20]}) "
                        f"{item['title']}\n{item['link']}\n\n")
            continue
        clusters.append({"t": item["title"], "b": list(cand), "ts": time.time()})

        log_alert(now, label, cat, item)
        if alerted < MAX_ALERTS_PER_CYCLE:
            notify(tg, label, cat, item)
            alerted += 1
        else:
            print("        (알림 상한 초과 — 터미널에만 표시)", flush=True)

    print(
        f"[{now:%H:%M}] 점검 완료 — 수집 {len(items)}건, 알림 {alerted}건, 후속기사 병합 {merged}건",
        flush=True,
    )
    return state


def setup_telegram(creds):
    """봇에게 보낸 최근 메시지에서 chat_id를 찾아 .env에 기록하고 테스트 발송."""
    token = creds.get("TELEGRAM_BOT_TOKEN")
    if not token:
        sys.exit(
            "TELEGRAM_BOT_TOKEN이 없습니다.\n"
            "1) 텔레그램에서 @BotFather에게 /newbot → 봇 이름 지정 → 토큰 복사\n"
            f"2) {BASE_DIR / '.env'} 에 TELEGRAM_BOT_TOKEN=토큰 한 줄 추가\n"
            "3) 만든 봇에게 아무 메시지나 하나 보낸 뒤 이 명령을 다시 실행"
        )
    data = json.loads(http_get(f"https://api.telegram.org/bot{token}/getUpdates"))
    chats = [
        u["message"]["chat"] for u in data.get("result", []) if "message" in u
    ]
    if not chats:
        sys.exit("봇이 받은 메시지가 없습니다. 텔레그램에서 봇에게 아무 메시지나 보낸 뒤 다시 실행하세요.")
    chat = chats[-1]
    chat_id = str(chat["id"])

    env_path = BASE_DIR / ".env"
    lines = env_path.read_text().splitlines() if env_path.exists() else []
    lines = [l for l in lines if not l.startswith("TELEGRAM_CHAT_ID=")]
    lines.append(f"TELEGRAM_CHAT_ID={chat_id}")
    env_path.write_text("\n".join(lines) + "\n")

    notify_telegram(token, chat_id, "테스트", "설정", {
        "title": "텔레그램 연결 완료 — 이제 속보 알림이 여기로 옵니다.",
        "link": "",
    })
    print(f"✅ chat_id={chat_id} ({chat.get('first_name', '')}) 등록 완료. 테스트 메시지를 보냈습니다.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true", help="1회만 실행")
    ap.add_argument("--interval", type=int, default=180, help="폴링 간격(초), 기본 180")
    ap.add_argument("--setup-telegram", action="store_true", help="텔레그램 chat_id 자동 등록")
    args = ap.parse_args()

    creds = load_env()
    if args.setup_telegram:
        setup_telegram(creds)
        return

    cid, csec = creds.get("NAVER_CLIENT_ID"), creds.get("NAVER_CLIENT_SECRET")
    if not (cid and csec):
        sys.exit("네이버 자격증명(NAVER_CLIENT_ID/SECRET)을 .env에서 못 찾았습니다.")
    tg = (creds.get("TELEGRAM_BOT_TOKEN"), creds.get("TELEGRAM_CHAT_ID"))
    channel = "텔레그램" if all(tg) else "macOS 배너 (텔레그램 미설정)"

    print(f"👮 사회부 당번 속보 감시 시작 — {args.interval}초 간격, 알림: {channel}, Ctrl+C로 종료", flush=True)
    state = load_state()
    first_run = not state["seen"]  # 상태 파일이 비어있으면 첫 실행으로 간주
    while True:
        try:
            state = save_state(run_cycle(cid, csec, tg, state, first_run))
        except Exception as e:
            print(f"  ⚠️ 사이클 오류(계속 진행): {e}", flush=True)
        first_run = False
        if args.once:
            break
        time.sleep(args.interval)


if __name__ == "__main__":
    main()
