"""
grades.py — Flask web app to view student grades and generate evidence PDFs.
Run:  python grades.py
Then open http://127.0.0.1:5000 in your browser.
"""

import csv
import html
import io
import os
import sqlite3
import base64
import re
import textwrap

import requests
from flask import Flask, render_template_string, request, send_file, g

from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
  Image as RLImage, KeepTogether, HRFlowable, PageBreak,
)
from reportlab.lib.enums import TA_LEFT, TA_CENTER
from PIL import Image as PILImage
from PIL import ImageOps as PILImageOps

BASE = "https://aimarker.replit.app"
API_KEY = "vagEqbnj0uoocoXuqBQ69r7oYKlhbGWktPNorsYtTrz6PZRjLWE6aQ"
HEADERS = {"X-Api-Key": API_KEY}

DB_PATH = os.path.join(os.path.dirname(__file__), "candidates.db")
CSV_PATH = os.path.join(os.path.dirname(__file__), "candidates.csv")
EVIDENCE_STATUS_CSV_PATH = os.path.join(os.path.dirname(__file__), "y11scores.csv")

app = Flask(__name__)

# ---------------------------------------------------------------------------
# Database helpers
# ---------------------------------------------------------------------------

def get_db():
    db = getattr(g, "_database", None)
    if db is None:
        db = g._database = sqlite3.connect(DB_PATH)
        db.row_factory = sqlite3.Row
    return db


@app.teardown_appcontext
def close_db(exc):
    db = getattr(g, "_database", None)
    if db is not None:
        db.close()


def init_db():
    """Create (or recreate) the candidates table from the CSV."""
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("DROP TABLE IF EXISTS candidates")
    cur.execute("""
        CREATE TABLE candidates (
            email        TEXT PRIMARY KEY,
            candidate_no TEXT,
            school_code  TEXT,
            surname      TEXT,
            forename     TEXT,
            year_group   TEXT,
            form         TEXT,
            gender       TEXT,
            dob          TEXT,
            uci          TEXT
        )
    """)
    with open(CSV_PATH, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        rows = []
        for row in reader:
            rows.append((
                row.get("Student Email Address", "").strip().lower(),
                row.get("Candidate #", "").strip(),
                row.get("School Code", "").strip(),
                row.get("Surname", "").strip(),
                row.get("Forename", "").strip(),
                row.get("Year Group", "").strip(),
                row.get("Form", "").strip(),
                row.get("Gender", "").strip(),
                row.get("DOB", "").strip(),
                row.get("UCI", "").strip(),
            ))
        cur.executemany(
            "INSERT OR IGNORE INTO candidates VALUES (?,?,?,?,?,?,?,?,?,?)", rows
        )
    conn.commit()
    conn.close()
    print(f"[DB] Imported {len(rows)} candidates into {DB_PATH}")


def lookup_candidate(email: str):
    """Return candidate row dict or None."""
    cur = get_db().execute(
        "SELECT * FROM candidates WHERE email = ?", (email.strip().lower(),)
    )
    row = cur.fetchone()
    return dict(row) if row else None


def lookup_candidates_by_candidate_numbers(candidate_nos: list[str]) -> dict:
  """Return candidate rows keyed by candidate number."""
  clean_numbers = [str(candidate_no).strip() for candidate_no in candidate_nos if str(candidate_no).strip()]
  if not clean_numbers:
    return {}
  placeholders = ",".join("?" for _ in clean_numbers)
  cur = get_db().execute(
    f"SELECT * FROM candidates WHERE candidate_no IN ({placeholders})",
    clean_numbers,
  )
  return {row["candidate_no"]: dict(row) for row in cur.fetchall()}


def parse_percentage(value: str | None) -> float | None:
  if value is None:
    return None
  text = str(value).strip()
  if not text:
    return None
  text = text.replace("%", "").strip()
  try:
    return float(text)
  except ValueError:
    return None


def parse_code_list(value: str) -> list[str]:
  seen = set()
  codes = []
  for part in re.split(r"[\n,]+", value or ""):
    code = part.strip()
    if not code or code in seen:
      continue
    seen.add(code)
    codes.append(code)
  return codes


def attempt_percentage(attempt: dict) -> float | None:
  pct = attempt.get("percentage")
  if pct is not None:
    try:
      return float(pct)
    except (TypeError, ValueError):
      pass

  awarded = attempt.get("marks_awarded")
  possible = attempt.get("marks_possible")
  if awarded is None or not possible:
    return None

  try:
    return (float(awarded) / float(possible)) * 100
  except (TypeError, ValueError, ZeroDivisionError):
    return None


def load_existing_evidence_rows() -> list:
  """Load existing evidence scores from the local Year 11 CSV."""
  if not os.path.exists(EVIDENCE_STATUS_CSV_PATH):
    return []

  rows = []
  with open(EVIDENCE_STATUS_CSV_PATH, newline="", encoding="utf-8-sig") as f:
    reader = csv.DictReader(f)
    fieldnames = reader.fieldnames or []
    score_columns = [name for name in fieldnames if name not in {"Candidate #", "Student"}]
    for row in reader:
      candidate_no = (row.get("Candidate #") or "").strip()
      if not candidate_no:
        continue
      existing_items = []
      for column in score_columns:
        score = parse_percentage(row.get(column))
        if score is None:
          continue
        existing_items.append({
          "label": column,
          "percentage": score,
          "display": f"{score:.0f}%",
          "grade_label": grade_suggestion(score),
          "grade_class": grade_badge_class(score),
        })
      rows.append({
        "candidate_no": candidate_no,
        "student_name": (row.get("Student") or "").strip(),
        "existing_items": existing_items,
        "evidence_count": len(existing_items),
      })
  return rows


def fetch_quiz_attempt_groups(class_code: str, quiz_codes: list[str], include_questions: bool = False) -> dict:
  """Fetch attempts for an explicit list of quiz codes."""
  raw_by_quiz = {}
  for quiz_code in quiz_codes:
    data = fetch_grades(class_code, quiz_code, include_questions=include_questions)
    raw_by_quiz[quiz_code] = data.get("attempts", [])
  return raw_by_quiz


def build_student_quiz_score_map(raw_by_quiz: dict) -> dict:
  """Return best per-quiz score rows keyed by student email then quiz code."""
  student_scores = {}
  for quiz_code, attempts in raw_by_quiz.items():
    for raw_attempt in attempts:
      attempt = _normalise_attempt_questions(raw_attempt)
      email = (attempt.get("student_email") or "").strip().lower()
      if not email:
        continue
      percentage = attempt_percentage(attempt)
      marks_possible = attempt.get("marks_possible") or 0
      attempted_questions, total_questions = _question_attempt_progress(attempt)
      current = {
        "quiz_code": quiz_code,
        "label": quiz_code,
        "source_quiz_codes": [quiz_code],
        "percentage": percentage,
        "marks_awarded": attempt.get("marks_awarded"),
        "marks_possible": marks_possible,
        "minutes": round(marks_possible) if marks_possible else 0,
        "attempted_questions": attempted_questions,
        "total_questions": total_questions,
        "attempt_date": _attempt_date(attempt),
        "type": "single",
      }
      prev = student_scores.setdefault(email, {}).get(quiz_code)
      prev_pct = prev.get("percentage") if prev else None
      current_pct = current.get("percentage")
      choose_current = prev is None
      if not choose_current:
        if current_pct is not None and prev_pct is None:
          choose_current = True
        elif current_pct is not None and prev_pct is not None and current_pct > prev_pct:
          choose_current = True
        elif current_pct == prev_pct:
          current_date = current.get("attempt_date")
          prev_date = prev.get("attempt_date")
          choose_current = current_date is not None and (prev_date is None or current_date > prev_date)
      if choose_current:
        student_scores[email][quiz_code] = current
  return student_scores


def parse_merge_groups(value: str, valid_quiz_codes: list[str] | None = None, name_prefix: str | None = None) -> list:
  """Parse merge groups from semicolon-separated groups of quiz codes."""
  if not value.strip():
    return []

  valid_set = set(valid_quiz_codes or [])
  groups = []
  for raw_group in re.split(r"[;\n]+", value):
    parts = []
    for code in re.split(r"[+,]+", raw_group):
      clean = code.strip()
      if clean and clean not in parts:
        parts.append(clean)
    if len(parts) < 2:
      continue
    label = f"{name_prefix}{len(groups) + 1}" if name_prefix else " + ".join(parts)
    groups.append({
      "label": label,
      "source_label": " + ".join(parts),
      "quiz_codes": parts,
      "unknown_codes": [code for code in parts if valid_set and code not in valid_set],
    })
  return groups


def ensure_quiz_attempt_groups(class_code: str, raw_by_quiz: dict, quiz_codes: list[str], months_ago: int | None = None) -> dict:
  """Ensure explicit quiz codes exist in the grouped attempts map."""
  cutoff = _cutoff_date(months_ago)
  for quiz_code in quiz_codes:
    if quiz_code in raw_by_quiz:
      continue
    try:
      data = fetch_grades(class_code, quiz_code)
      raw_by_quiz[quiz_code] = _filter_attempts_by_date(data.get("attempts", []), cutoff)
    except Exception:
      raw_by_quiz[quiz_code] = []
  return raw_by_quiz


def _merged_percentage(items: list[dict]) -> float | None:
  if not items:
    return None

  total_marks = sum(item.get("marks_possible") or 0 for item in items)
  valid_percentages = [item.get("percentage") for item in items if item.get("percentage") is not None]
  if not valid_percentages:
    return None

  if total_marks > 0 and len(valid_percentages) == len(items):
    return sum((item.get("percentage") or 0) * (item.get("marks_possible") or 0) for item in items) / total_marks
  return sum(valid_percentages) / len(valid_percentages)


def build_merged_quiz_summaries(raw_by_quiz: dict, merge_groups: list) -> tuple:
  """Build merged quiz summaries plus per-student merged score rows."""
  if not merge_groups:
    return [], {}

  source_summaries = {item["quiz_code"]: item for item in _summaries_from_groups(raw_by_quiz)}
  student_scores = build_student_quiz_score_map(raw_by_quiz)
  merged_infos = []
  merged_details = {}

  for group in merge_groups:
    source_infos = [
      source_summaries.get(
        quiz_code,
        {
          "quiz_code": quiz_code,
          "label": quiz_code,
          "source_quiz_codes": [quiz_code],
          "source_label": quiz_code,
          "est_minutes": 0,
          "avg_marks_possible": 0,
          "avg_percentage": None,
          "attempt_count": 0,
          "latest_date": None,
          "type": "single",
        },
      )
      for quiz_code in group["quiz_codes"]
    ]

    student_rows = []
    latest_attempt = None
    for email, score_map in sorted(student_scores.items()):
      items = [score_map.get(quiz_code) for quiz_code in group["quiz_codes"]]
      if any(item is None or item.get("percentage") is None for item in items):
        continue

      merged_pct = _merged_percentage(items)
      merged_marks = sum(item.get("marks_possible") or 0 for item in items)
      merged_minutes = sum(item.get("minutes") or 0 for item in items)
      attempt_dates = [item.get("attempt_date") for item in items if item.get("attempt_date") is not None]
      student_latest = max(attempt_dates) if attempt_dates else None
      if student_latest is not None and (latest_attempt is None or student_latest > latest_attempt):
        latest_attempt = student_latest

      student_rows.append({
        "email": email,
        "percentage": merged_pct,
        "marks_possible": merged_marks,
        "total_minutes": merged_minutes,
        "component_percentages": {item["quiz_code"]: item.get("percentage") for item in items},
        "attempt_date": student_latest,
      })

    avg_marks_possible = sum(info.get("avg_marks_possible") or 0 for info in source_infos)
    avg_percentage = None
    if student_rows:
      avg_percentage = sum(row.get("percentage") or 0 for row in student_rows if row.get("percentage") is not None) / len(student_rows)
      if not avg_marks_possible:
        avg_marks_possible = sum(row.get("marks_possible") or 0 for row in student_rows) / len(student_rows)

    merged_infos.append({
      "quiz_code": group["label"],
      "label": group["label"],
      "source_quiz_codes": group["quiz_codes"],
      "source_label": group["source_label"],
      "est_minutes": round(avg_marks_possible),
      "avg_marks_possible": avg_marks_possible,
      "avg_percentage": avg_percentage,
      "attempt_count": len(student_rows),
      "latest_date": latest_attempt.strftime("%d %b %Y") if latest_attempt else None,
      "type": "merged",
    })
    merged_details[group["label"]] = student_rows

  return merged_infos, merged_details


def build_merged_score_rows(score_map: dict, merge_groups: list) -> list:
  merged_rows = []
  for group in merge_groups:
    missing = []
    components = []
    if group["unknown_codes"]:
      merged_rows.append({
        "label": group["label"],
        "percentage": None,
        "total_minutes": None,
        "missing": group["unknown_codes"],
      })
      continue

    for quiz_code in group["quiz_codes"]:
      item = score_map.get(quiz_code)
      if not item or item.get("percentage") is None:
        missing.append(quiz_code)
        continue
      components.append(item)

    if missing:
      merged_rows.append({
        "label": group["label"],
        "percentage": None,
        "total_minutes": None,
        "missing": missing,
      })
      continue

    total_marks = sum(item.get("marks_possible") or 0 for item in components)
    if total_marks > 0:
      percentage = sum((item.get("percentage") or 0) * (item.get("marks_possible") or 0) for item in components) / total_marks
    else:
      percentage = sum(item.get("percentage") or 0 for item in components) / len(components)

    merged_rows.append({
      "label": group["label"],
      "percentage": percentage,
      "total_minutes": sum(item.get("minutes") or 0 for item in components),
      "attempted_questions": sum(item.get("attempted_questions") or 0 for item in components),
      "total_questions": sum(item.get("total_questions") or 0 for item in components),
      "missing": [],
    })
  return merged_rows


# ---------------------------------------------------------------------------
# API helpers
# ---------------------------------------------------------------------------

def fetch_grades(class_code: str, quiz_code: str):
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    params = {"quiz_code": quiz_code}
    resp = requests.get(url, headers=HEADERS, params=params, timeout=30)
    resp.raise_for_status()
    return resp.json()


def fetch_grades(class_code: str, quiz_code: str, include_questions: bool = False):
    """Fetch attempt list, optionally with inline question/answer data."""
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    params = {"quiz_code": quiz_code}
    if include_questions:
        params["include_questions"] = "true"
    resp = requests.get(url, headers=HEADERS, params=params, timeout=60)
    resp.raise_for_status()
    return resp.json()


def fetch_attempt_detail(attempt_id: str):
    """Fetch full question/answer detail for a single attempt (fallback)."""
    url = f"{BASE}/ext-api/attempts/{attempt_id}/"
    resp = requests.get(url, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    return resp.json()


def fetch_all_attempts(class_code: str):
    """Fetch ALL attempts for a class with no quiz_code filter."""
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    resp = requests.get(url, headers=HEADERS, timeout=60)
    resp.raise_for_status()
    data = resp.json()
    if isinstance(data, list):
        return data
    return data.get("attempts", [])


def _attempt_date(attempt: dict):
    """Return a datetime for the attempt, or None if unparseable."""
    from datetime import datetime, timezone
    for key in ("last_answer_at", "first_answer_at", "submitted_at", "completed_at", "created_at", "date", "timestamp", "taken_at", "answered_at"):
        raw = attempt.get(key)
        if not raw:
            continue
        try:
            raw = str(raw).replace("Z", "+00:00")
            return datetime.fromisoformat(raw)
        except Exception:
            pass
    return None


def _cutoff_date(months_ago: int | None):
    """Return a timezone-aware cutoff datetime, or None if months_ago is falsy."""
    if not months_ago:
        return None
    from datetime import datetime, timezone, timedelta
    return datetime.now(timezone.utc) - timedelta(days=months_ago * 30.44)


def _filter_attempts_by_date(attempts: list, cutoff) -> list:
    """Keep attempts on or after cutoff. Attempts with no parseable date are kept."""
    if cutoff is None:
        return attempts
    from datetime import timezone
    result = []
    for a in attempts:
        d = _attempt_date(a)
        if d is None:
            result.append(a)  # no date info — keep
            continue
        # Make both offset-aware for comparison
        if d.tzinfo is None:
            from datetime import timezone
            d = d.replace(tzinfo=timezone.utc)
        if d >= cutoff:
            result.append(a)
    return result


# Candidate field names that might carry a spec/topic reference on a question object
_SPEC_FIELDS = (
    "speccode", "spec_code", "spec", "specification", "topic_code", "topic",
    "category", "ref", "code", "question_code", "sub_topic",
    "learning_objective", "objective", "strand",
)


def _quiz_matches_spec(class_code: str, quiz_code: str, spec_code: str) -> bool:
    """Return True if >=50% of questions in this quiz contain spec_code
    in any recognised spec/topic field (case-insensitive substring match)."""
    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
        attempts = data.get("attempts", [])
        if not attempts:
            return False
        first = attempts[0]
        questions = (
            first.get("questions") or first.get("question_list")
            or first.get("responses") or first.get("answers") or []
        )
        if not questions:
            return False
        needle = spec_code.strip().lower()
        matched = 0
        for q in questions:
            for field in _SPEC_FIELDS:
                val = str(q.get(field, "")).strip().lower()
                if val and needle in val:
                    matched += 1
                    break  # count each question at most once
        return (matched / len(questions)) >= 0.5
    except Exception:
        return False


def discover_quiz_summaries(
    class_code: str,
    manual_codes: str = "",
    months_ago: int | None = None,
    spec_code: str = "",
) -> tuple:
    """Return (quiz_summaries list, raw_attempts_by_quiz_code dict).
    If manual_codes is given (comma-separated), fetch each individually.
    Otherwise fetch all attempts at once and group by quiz_code field."""
    cutoff = _cutoff_date(months_ago)
    raw_by_quiz = {}  # quiz_code -> [attempt dicts]
    if manual_codes:
        codes = [c.strip() for c in manual_codes.split(",") if c.strip()]
        for qc in codes:
            try:
                data = fetch_grades(class_code, qc)
                filtered = _filter_attempts_by_date(data.get("attempts", []), cutoff)
                if filtered:
                    raw_by_quiz[qc] = filtered
            except Exception:
                continue
    else:
        all_attempts = fetch_all_attempts(class_code)
        for a in _filter_attempts_by_date(all_attempts, cutoff):
            qc = a.get("quiz_code") or a.get("quiz") or a.get("quiz_id") or a.get("quiz_name")
            if qc:
                raw_by_quiz.setdefault(str(qc), []).append(a)

    infos = _summaries_from_groups(raw_by_quiz)

    # Apply spec_code filter — requires a questions fetch per quiz
    if spec_code:
        valid = {q["quiz_code"] for q in infos if _quiz_matches_spec(class_code, q["quiz_code"], spec_code)}
        infos = [q for q in infos if q["quiz_code"] in valid]
        raw_by_quiz = {qc: v for qc, v in raw_by_quiz.items() if qc in valid}

    return infos, raw_by_quiz


def _summaries_from_groups(grouped: dict) -> list:
  result = []
  for qc, attempts in grouped.items():
    possible_values = [a.get("marks_possible") for a in attempts if a.get("marks_possible") is not None]
    pct_values = [attempt_percentage(a) for a in attempts]
    pct_values = [value for value in pct_values if value is not None]
    avg_possible = sum(possible_values) / len(possible_values) if possible_values else 0
    avg_pct = sum(pct_values) / len(pct_values) if pct_values else None
    dates = [_attempt_date(a) for a in attempts]
    dates = [d for d in dates if d is not None]
    latest = max(dates).strftime("%d %b %Y") if dates else None
    result.append({
      "quiz_code": qc,
      "label": qc,
      "source_quiz_codes": [qc],
      "source_label": qc,
      "est_minutes": round(avg_possible),
      "avg_marks_possible": avg_possible,
      "avg_percentage": avg_pct,
      "attempt_count": len(attempts),
      "latest_date": latest,
      "type": "single",
    })
  return result


def compute_per_student_evidence(
    raw_by_quiz: dict,
    target_min: int = 50,
    target_max: int = 70,
    top_n: int = 3,
    merge_groups: list | None = None,
) -> list:
    """Build per-student best evidence from {quiz_code: [attempts]} mapping.
    For each student uses their own percentage (best attempt per quiz)."""
    student_best = build_student_quiz_score_map(raw_by_quiz)

    for quiz_map in student_best.values():
        for item in list(quiz_map.values()):
            item.setdefault("est_minutes", item.get("minutes") or round(item.get("marks_possible") or 0))
            item.setdefault("avg_marks_possible", item.get("marks_possible") or 0)
            item.setdefault("avg_percentage", item.get("percentage"))
            item.setdefault("attempt_count", 1)
            item.setdefault("latest_date", item.get("attempt_date"))

        for group in merge_groups or []:
            items = [quiz_map.get(quiz_code) for quiz_code in group["quiz_codes"]]
            if any(item is None or item.get("percentage") is None for item in items):
                continue

            merged_marks = sum(item.get("marks_possible") or 0 for item in items)
            merged_minutes = sum(item.get("minutes") or 0 for item in items)
            merged_pct = _merged_percentage(items)
            attempt_dates = [item.get("attempt_date") for item in items if item.get("attempt_date") is not None]
            latest_attempt = max(attempt_dates) if attempt_dates else None
            quiz_map[group["label"]] = {
                "quiz_code": group["label"],
                "label": group["label"],
                "source_quiz_codes": group["quiz_codes"],
                "source_label": group["source_label"],
                "est_minutes": merged_minutes,
                "avg_marks_possible": merged_marks,
                "avg_percentage": merged_pct,
                "attempt_count": 1,
                "latest_date": latest_attempt.strftime("%d %b %Y") if latest_attempt else None,
                "type": "merged",
            }

    results = []
    for email, quiz_map in sorted(student_best.items()):
        evidence = find_best_evidence(list(quiz_map.values()), target_min, target_max, top_n)
        results.append({"email": email, "evidence": evidence})
    return results



def grade_suggestion(percentage: float | None) -> str:
  """Map percentage to descriptive attainment bands."""
  if percentage is None:
    return "No grade"
  thresholds = [
    (85, "Very secure 9"),
    (80, "Likely 9"),
    (71, "Likely 8"),
    (62, "Likely 7"),
    (52, "Likely 6"),
    (42, "Likely 5"),
    (32, "Likely 4"),
  ]
  for threshold, label in thresholds:
    if percentage >= threshold:
      return label
  return "Below likely 4"


def grade_threshold_rows() -> list[dict]:
  return [
    {"threshold": "85%+", "label": "Very secure 9", "badge": "9"},
    {"threshold": "80%+", "label": "Likely 9", "badge": "9"},
    {"threshold": "71%+", "label": "Likely 8", "badge": "8"},
    {"threshold": "62%+", "label": "Likely 7", "badge": "7"},
    {"threshold": "52%+", "label": "Likely 6", "badge": "6"},
    {"threshold": "42%+", "label": "Likely 5", "badge": "5"},
    {"threshold": "32%+", "label": "Likely 4", "badge": "4"},
    {"threshold": "Below 32%", "label": "Below likely 4", "badge": "1"},
  ]


def grade_badge_class(percentage: float | None) -> str:
  """Return the numeric badge class used for styling grade labels."""
  if percentage is None:
    return "?"
  thresholds = [
    (85, "9"),
    (80, "9"),
    (71, "8"),
    (62, "7"),
    (52, "6"),
    (42, "5"),
    (32, "4"),
  ]
  for threshold, badge in thresholds:
    if percentage >= threshold:
      return badge
  return "1"


def find_best_evidence(quizzes_info: list, target_min: int = 50, target_max: int = 70, top_n: int = 3):
    """
    Given a list of quiz summary dicts (each with est_minutes, avg_percentage),
    find the top_n best single or paired quizzes that meet the time target.
    Returns a list of evidence dicts sorted by quality score.
    """
    candidates = []

    # Single quizzes
    for q in quizzes_info:
      mins = q["est_minutes"]
      if mins >= target_min:
        score = _evidence_score(mins, q["avg_percentage"], target_min, target_max)
        candidates.append({
          "type": "single",
          "quizzes": [q],
          "quiz_codes": [q["quiz_code"]],
          "source_quiz_codes": q.get("source_quiz_codes") or [q["quiz_code"]],
          "total_minutes": mins,
          "avg_percentage": q["avg_percentage"],
          "grade": grade_suggestion(q["avg_percentage"]),
          "grade_class": grade_badge_class(q["avg_percentage"]),
          "score": score,
          "label": q.get("label") or q["quiz_code"],
        })

    # Pairs of quizzes
    for i in range(len(quizzes_info)):
      for j in range(i + 1, len(quizzes_info)):
        q1, q2 = quizzes_info[i], quizzes_info[j]
        q1_sources = set(q1.get("source_quiz_codes") or [q1["quiz_code"]])
        q2_sources = set(q2.get("source_quiz_codes") or [q2["quiz_code"]])
        if q1_sources & q2_sources:
          continue

        total_mins = q1["est_minutes"] + q2["est_minutes"]
        if total_mins >= target_min:
          w1 = q1["avg_marks_possible"]
          w2 = q2["avg_marks_possible"]
          total_w = w1 + w2
          if total_w > 0 and q1["avg_percentage"] is not None and q2["avg_percentage"] is not None:
            combined_pct = (q1["avg_percentage"] * w1 + q2["avg_percentage"] * w2) / total_w
          else:
            combined_pct = q1["avg_percentage"] or q2["avg_percentage"]

          score = _evidence_score(total_mins, combined_pct, target_min, target_max)
          candidates.append({
            "type": "combined",
            "quizzes": [q1, q2],
            "quiz_codes": [q1["quiz_code"], q2["quiz_code"]],
            "source_quiz_codes": sorted(q1_sources | q2_sources),
            "total_minutes": total_mins,
            "avg_percentage": combined_pct,
            "grade": grade_suggestion(combined_pct),
            "grade_class": grade_badge_class(combined_pct),
            "score": score,
            "label": f"{q1['quiz_code']} + {q2['quiz_code']}",
          })

    candidates.sort(key=lambda x: x["score"], reverse=True)
    return candidates[:top_n]


def _evidence_score(total_mins: int, avg_pct: float | None, target_min: int, target_max: int) -> float:
    """Score an evidence candidate. Higher is better.
    Prefers items in the 50-70 min range; penalises far above target_max.
    Also weights by average percentage performance."""
    if total_mins < target_min:
        time_score = total_mins / target_min  # partial credit
    elif total_mins <= target_max:
        time_score = 1.0
    else:
        # Slight penalty for going very long, but still valid
        time_score = max(0.5, 1.0 - (total_mins - target_max) / 60)
    pct_score = (avg_pct or 50) / 100
    return time_score * 0.6 + pct_score * 0.4


def build_rows(attempts: list) -> list:
    rows = []
    for a in sorted(attempts, key=lambda x: x.get("student_email", "")):
        awarded  = a.get("marks_awarded")
        possible = a.get("marks_possible")
        fully    = a.get("fully_marked", False)
        unmarked = a.get("questions_unmarked", 0)

        if fully:
            status = "Marked"
        elif unmarked > 0:
            status = f"{unmarked} unmarked"
        else:
            status = "Partial"

        rows.append({
            "email":      a.get("student_email", "unknown"),
            "attempt_id": a.get("id") or a.get("attempt_id", ""),
            "marks_str":  f"{awarded}/{possible}" if awarded is not None else "—/—",
            "marks_possible": possible,
            "percentage": a.get("percentage"),
            "status":     status,
        })
    return rows


# ---------------------------------------------------------------------------
# HTML Templates
# ---------------------------------------------------------------------------

BASE_STYLE = """
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: system-ui, sans-serif; background: #f0f2f5; color: #1a1a2e; padding: 2rem; }
  h1 { font-size: 1.6rem; margin-bottom: 1.5rem; color: #16213e; }
  h2 { font-size: 1.2rem; margin-bottom: 1rem; color: #16213e; }

  .card { background: #fff; border-radius: 10px; box-shadow: 0 2px 8px rgba(0,0,0,.1); padding: 1.5rem; margin-bottom: 1.5rem; }

  form { display: flex; gap: 1rem; flex-wrap: wrap; align-items: flex-end; }
  label { display: flex; flex-direction: column; gap: .3rem; font-size: .85rem; font-weight: 600; }
  input[type=text], input[type=number], select {
    padding: .5rem .75rem; border: 1px solid #ccc; border-radius: 6px;
    font-size: .95rem; width: 180px;
  }
  input[type=text]:focus, input[type=number]:focus, select:focus {
    outline: 2px solid #0f3460; border-color: transparent;
  }
  .btn { padding: .55rem 1.4rem; background: #0f3460; color: #fff; border: none;
         border-radius: 6px; font-size: 1rem; cursor: pointer; text-decoration: none;
         display: inline-block; }
  .btn:hover { background: #16213e; }
  .btn-sm { padding: .3rem .9rem; font-size: .85rem; }
  .btn-green { background: #065f46; }
  .btn-green:hover { background: #064e3b; }

  .meta { display: flex; gap: 2rem; flex-wrap: wrap; }
  .meta-item { display: flex; flex-direction: column; }
  .meta-item span:first-child { font-size: .75rem; font-weight: 700; text-transform: uppercase; color: #888; }
  .meta-item span:last-child { font-size: 1.1rem; font-weight: 600; }

  table { width: 100%; border-collapse: collapse; font-size: .9rem; }
  thead th { background: #0f3460; color: #fff; padding: .65rem 1rem; text-align: left; }
  tbody tr:nth-child(even) { background: #f7f8fc; }
  tbody td { padding: .6rem 1rem; border-bottom: 1px solid #e8e8e8; }
  tbody tr:hover { background: #eef1fb; }

  .badge { display: inline-block; padding: .2rem .6rem; border-radius: 999px; font-size: .8rem; font-weight: 600; }
  .badge-ok   { background: #d1fae5; color: #065f46; }
  .badge-warn { background: #fef9c3; color: #713f12; }
  .badge-part { background: #e0e7ff; color: #3730a3; }

  .bar-wrap { width: 120px; background: #e5e7eb; border-radius: 4px; height: 8px;
              display: inline-block; vertical-align: middle; margin-right: .4rem; }
  .bar-fill  { height: 8px; border-radius: 4px; background: #0f3460; }

  .error { background: #fee2e2; color: #991b1b; padding: .75rem 1rem; border-radius: 6px; }
  .no-data { color: #666; font-style: italic; }
  .info { color: #555; font-size: .9rem; }

  .pdf-options { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 1rem; }
  .checkbox-row { display: flex; gap: .5rem; align-items: center; font-size: .9rem; font-weight: 500; }
  input[type=checkbox] { width: 16px; height: 16px; cursor: pointer; }
  .section-title { font-size: .75rem; font-weight: 700; text-transform: uppercase;
                   color: #0f3460; margin-bottom: .5rem; letter-spacing: .05em; }
  .time-badge { background: #eff6ff; color: #1e40af; padding: .2rem .7rem;
                border-radius: 999px; font-size: .8rem; font-weight: 600; margin-left: .5rem; }

  .tabs { display: flex; gap: .25rem; margin-bottom: 1.5rem; border-bottom: 2px solid #e5e7eb; }
  .tab  { padding: .6rem 1.4rem; border-radius: 8px 8px 0 0; font-size: .95rem; font-weight: 600;
           text-decoration: none; color: #555; background: #e9ecef; border: 1px solid #ddd;
           border-bottom: none; position: relative; top: 2px; }
  .tab:hover  { background: #dde3f0; color: #0f3460; }
  .tab.active { background: #fff; color: #0f3460; border-color: #e5e7eb; z-index: 1; }

  .ev-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(340px, 1fr)); gap: 1.2rem; margin-bottom: 1.5rem; }
  .ev-card { background: #fff; border-radius: 10px; box-shadow: 0 2px 8px rgba(0,0,0,.1);
             border-left: 5px solid #0f3460; padding: 1.2rem; }
  .ev-card.rank-1 { border-left-color: #d97706; }
  .ev-card.rank-2 { border-left-color: #6b7280; }
  .ev-card.rank-3 { border-left-color: #92400e; }
  .ev-rank { font-size: .75rem; font-weight: 800; text-transform: uppercase; letter-spacing: .1em;
             color: #888; margin-bottom: .3rem; }
  .ev-label { font-size: 1.05rem; font-weight: 700; color: #0f3460; margin-bottom: .5rem; word-break: break-all; }
  .ev-meta { display: flex; gap: 1rem; flex-wrap: wrap; margin-bottom: .8rem; }
  .ev-pill { padding: .2rem .65rem; border-radius: 999px; font-size: .8rem; font-weight: 600; }
  .ev-pill-time { background: #eff6ff; color: #1e40af; }
  .ev-pill-pct  { background: #f0fdf4; color: #065f46; }
  .ev-grade { font-size: 2rem; font-weight: 900; color: #0f3460; margin-bottom: .8rem; }
  .ev-grade small { font-size: .85rem; font-weight: 500; color: #888; margin-left: .25rem; }
  .ev-component { background: #f8faff; border-radius: 6px; padding: .5rem .75rem;
                  font-size: .85rem; margin-bottom: .4rem; }
  .ev-component b { color: #16213e; }
  .ev-actions { margin-top: .8rem; display: flex; flex-wrap: wrap; gap: .5rem; }

  .grade-badge {
    display: inline-block; padding: .15rem .55rem; border-radius: 4px;
    font-weight: 800; font-size: .95rem; margin-left: .3rem;
  }
  .grade-9 { background: #1e3a5f; color: #fff; }
  .grade-8 { background: #1e40af; color: #fff; }
  .grade-7 { background: #0369a1; color: #fff; }
  .grade-6 { background: #0891b2; color: #fff; }
  .grade-5 { background: #059669; color: #fff; }
  .grade-4 { background: #65a30d; color: #fff; }
  .grade-3 { background: #ca8a04; color: #fff; }
  .grade-2 { background: #ea580c; color: #fff; }
  .grade-1 { background: #dc2626; color: #fff; }
  .grade-? { background: #9ca3af; color: #fff; }

  .student-picker { display: grid; grid-template-columns: repeat(auto-fill, minmax(250px, 1fr)); gap: .8rem; max-height: 420px; overflow-y: auto; padding: .2rem; }
  .student-option { display: block; border: 1px solid #dbe3f0; border-radius: 10px; background: #f8fbff; padding: .85rem; cursor: pointer; }
  .student-option:hover { border-color: #93c5fd; background: #f0f7ff; }
  .student-option input { margin-right: .45rem; }
  .student-name { font-weight: 700; color: #0f3460; }
  .student-meta { display: block; color: #64748b; font-size: .8rem; margin-top: .2rem; }
  .student-tags { display: flex; flex-wrap: wrap; gap: .35rem; margin-top: .55rem; }
  .score-chip { display: inline-flex; align-items: center; gap: .35rem; padding: .2rem .55rem; border-radius: 999px; font-size: .75rem; font-weight: 600; }
  .score-chip-existing { background: #eef2ff; color: #3730a3; }
  .score-chip-live { background: #ecfdf5; color: #065f46; }
  .score-chip-merge { background: #fff7ed; color: #9a3412; }
  .score-cell { min-width: 150px; }
  .score-main { font-size: 1rem; font-weight: 800; color: #0f3460; }
  .score-sub { color: #64748b; font-size: .8rem; margin-top: .2rem; }
  .soft-btn { background: #e2e8f0; color: #0f172a; }
  .soft-btn:hover { background: #cbd5e1; }
</style>
"""

INDEX_TEMPLATE = BASE_STYLE + """
<h1>Grade Viewer</h1>

<nav class="tabs">
  <a class="tab active" href="/">Grades</a>
  <a class="tab" href="/evidence{% if class_code %}?class_code={{ class_code }}{% endif %}">Best Evidence</a>
  <a class="tab" href="/evidence/planner">Evidence Planner</a>
</nav>

<div class="card">
  <form method="get" action="/">
    <label>Class Code
      <input type="text" name="class_code" value="{{ class_code }}" placeholder="e.g. CS101" required>
    </label>
    <label>Quiz Code
      <input type="text" name="quiz_code" value="{{ quiz_code }}" placeholder="e.g. QUIZ1" required>
    </label>
    <button type="submit" class="btn">View Grades</button>
  </form>
</div>

{% if error %}<div class="card error">{{ error }}</div>{% endif %}

{% if data %}
<div class="card">
  <div class="meta">
    <div class="meta-item"><span>Class</span><span>{{ data.class_code }}</span></div>
    <div class="meta-item"><span>Quiz</span><span>{{ quiz_code }}</span></div>
    <div class="meta-item"><span>Owner</span><span>{{ data.owner_email or "—" }}</span></div>
    <div class="meta-item"><span>Students in class</span><span>{{ data.student_count or "—" }}</span></div>
    <div class="meta-item"><span>Attempts</span><span>{{ data.attempt_count or attempts|length }}</span></div>
    {% if est_minutes %}
    <div class="meta-item"><span>Est. time</span>
      <span><span class="time-badge">~{{ est_minutes }} min</span></span>
    </div>
    {% endif %}
  </div>
</div>

<div class="card">
  <h2>Generate PDF Evidence</h2>
  <form method="get" action="/pdf">
    <input type="hidden" name="class_code" value="{{ class_code }}">
    <input type="hidden" name="quiz_code" value="{{ quiz_code }}">

    <div class="pdf-options">
      <div>
        <div class="section-title">Students</div>
        <label>Student (leave blank = all)
          <input type="text" name="student_email" value="" placeholder="email or blank">
        </label>
      </div>

      <div>
        <div class="section-title">Include in PDF</div>
        <div class="checkbox-row">
          <input type="checkbox" name="inc_marks" id="inc_marks" value="1" checked>
          <label for="inc_marks">Total marks</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_percentage" id="inc_percentage" value="1" checked>
          <label for="inc_percentage">Percentage</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_question_marks" id="inc_question_marks" value="1" checked>
          <label for="inc_question_marks">Question max marks below question</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_comments" id="inc_comments" value="1" checked>
          <label for="inc_comments">Examiner comments</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_questions" id="inc_questions" value="1" checked>
          <label for="inc_questions">Questions</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_labels" id="inc_labels" value="1" checked>
          <label for="inc_labels">Section labels (e.g. "Student response:")</label>
        </div>
      </div>

      <div>
        <div class="section-title">Header</div>
        <label>Centre number
          <input type="text" name="centre_number" value="" placeholder="optional override">
        </label>
        <div class="section-title" style="margin-top:1rem">Page margins (mm)</div>
        <label>Top / Bottom
          <input type="number" name="margin_tb" value="15" min="5" max="50">
        </label>
        <label style="margin-top:.5rem">Left / Right
          <input type="number" name="margin_lr" value="15" min="5" max="50">
        </label>
      </div>

      <div>
        <div class="section-title">Image-only responses</div>
        <label>Image width (% of page)
          <input type="number" name="img_pct" value="100" min="30" max="150">
        </label>
        <label style="margin-top:.5rem">Crop top of image
          <select name="img_crop_pct">
            <option value="0">None (0%)</option>
            <option value="2">2%</option>
            <option value="3" selected>3% (default)</option>
            <option value="5">5%</option>
            <option value="10">10%</option>
            <option value="15">15%</option>
          </select>
        </label>
        <label style="margin-top:.5rem">Page break between students?
          <select name="page_break">
            <option value="1" selected>Yes</option>
            <option value="0">No</option>
          </select>
        </label>
      </div>
    </div>

    <div style="margin-top:1.2rem">
      <button type="submit" class="btn btn-green">Download PDF</button>
    </div>
  </form>
</div>

<div class="card">
  {% if attempts %}
  <table>
    <thead>
      <tr>
        <th>Candidate #</th>
        <th>Student Name</th>
        <th>Student Email</th>
        <th>Marks</th>
        <th>Percentage</th>
        <th>Status</th>
      </tr>
    </thead>
    <tbody>
      {% for a in attempts %}
      <tr>
        <td>{{ a.candidate_no or "—" }}</td>
        <td>{{ a.full_name or "—" }}</td>
        <td>{{ a.email }}</td>
        <td>{{ a.marks_str }}</td>
        <td>
          {% if a.percentage is not none %}
            <div class="bar-wrap"><div class="bar-fill" style="width:{{ [a.percentage,100]|min }}%"></div></div>
            {{ "%.1f"|format(a.percentage) }}%
          {% else %}—{% endif %}
        </td>
        <td>
          {% if a.status == "Marked" %}<span class="badge badge-ok">Marked</span>
          {% elif "unmarked" in a.status %}<span class="badge badge-warn">{{ a.status }}</span>
          {% else %}<span class="badge badge-part">{{ a.status }}</span>{% endif %}
        </td>
      </tr>
      {% endfor %}
    </tbody>
  </table>
  {% else %}
  <p class="no-data">No attempts found for this class/quiz combination.</p>
  {% endif %}
</div>
{% endif %}
"""

# ---------------------------------------------------------------------------
# PDF options partial (reused in both templates)
# ---------------------------------------------------------------------------
PDF_OPTIONS_PARTIAL = """
<div class="pdf-options">
  <div>
    <div class="section-title">Include in PDF</div>
    <div class="checkbox-row">
      <input type="checkbox" name="inc_marks" id="pdf_inc_marks_{uid}" value="1" checked>
      <label for="pdf_inc_marks_{uid}">Total marks</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_percentage" id="pdf_inc_percentage_{uid}" value="1" checked>
      <label for="pdf_inc_percentage_{uid}">Percentage</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_question_marks" id="pdf_inc_question_marks_{uid}" value="1" checked>
      <label for="pdf_inc_question_marks_{uid}">Question max marks below question</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_comments" id="pdf_inc_comments_{uid}" value="1" checked>
      <label for="pdf_inc_comments_{uid}">Examiner comments</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_questions" id="pdf_inc_questions_{uid}" value="1" checked>
      <label for="pdf_inc_questions_{uid}">Questions</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_labels" id="pdf_inc_labels_{uid}" value="1" checked>
      <label for="pdf_inc_labels_{uid}">Section labels</label>
    </div>
  </div>
  <div>
    <div class="section-title">Header</div>
    <label>Centre number
      <input type="text" name="centre_number" value="" placeholder="optional override">
    </label>
    <div class="section-title" style="margin-top:1rem">Page margins (mm)</div>
    <label>Top / Bottom <input type="number" name="margin_tb" value="15" min="5" max="50"></label>
    <label style="margin-top:.5rem">Left / Right <input type="number" name="margin_lr" value="15" min="5" max="50"></label>
  </div>
  <div>
    <div class="section-title">Image-only responses</div>
    <label>Image width (% of page) <input type="number" name="img_pct" value="100" min="30" max="150"></label>
    <label style="margin-top:.5rem">Crop top of image
      <select name="img_crop_pct">
        <option value="0">None (0%)</option>
        <option value="2">2%</option>
        <option value="3" selected>3% (default)</option>
        <option value="5">5%</option>
        <option value="10">10%</option>
        <option value="15">15%</option>
      </select>
    </label>
    <label style="margin-top:.5rem">Page break between students?
      <select name="page_break">
        <option value="1" selected>Yes</option>
        <option value="0">No</option>
      </select>
    </label>
  </div>
</div>
"""

EVIDENCE_TEMPLATE = BASE_STYLE + """
<h1>Grade Viewer</h1>

<nav class="tabs">
  <a class="tab" href="/">Grades</a>
  <a class="tab active" href="/evidence{% if class_code %}?class_code={{ class_code }}{% endif %}">Best Evidence</a>
  <a class="tab" href="/evidence/planner">Evidence Planner</a>
</nav>

<div class="card">
  <h2>Find Best Evidence</h2>
  <p class="info" style="margin-bottom:1rem">
    Enter a class code and click <strong>Find Evidence</strong> — quizzes are auto-detected from
    student attempts. You can also override by entering specific quiz codes (comma-separated).
  </p>
  <form method="get" action="/evidence">
    <label>Class Code
      <input type="text" name="class_code" value="{{ class_code }}" placeholder="e.g. oxaqa25" required>
    </label>
    <label>Quiz Codes <span style="font-weight:400;color:#888">(optional — auto-detected if blank)</span>
      <input type="text" name="quiz_codes" value="{{ quiz_codes }}" placeholder="leave blank to auto-detect" style="width:320px">
    </label>
    <label>Student email <span style="font-weight:400;color:#888">(blank = all)</span>
      <input type="text" name="student_email" value="{{ student_email }}" placeholder="leave blank for class">
    </label>
    <label>Min. minutes
      <input type="number" name="target_min" value="{{ target_min }}" min="20" max="120">
    </label>
    <label>Target max minutes
      <input type="number" name="target_max" value="{{ target_max }}" min="30" max="180">
    </label>
    <label>Up to how many months ago
      <select name="months_ago">
        <option value="" {% if not months_ago %}selected{% endif %}>Any time</option>
        <option value="1" {% if months_ago == '1' %}selected{% endif %}>Last 1 month</option>
        <option value="2" {% if months_ago == '2' %}selected{% endif %}>Last 2 months</option>
        <option value="3" {% if months_ago == '3' %}selected{% endif %}>Last 3 months</option>
        <option value="6" {% if months_ago == '6' %}selected{% endif %}>Last 6 months</option>
        <option value="12" {% if months_ago == '12' %}selected{% endif %}>Last 12 months</option>
        <option value="24" {% if months_ago == '24' %}selected{% endif %}>Last 24 months</option>
      </select>
    </label>
    <label>Spec code filter <span style="font-weight:400;color:#888">(optional)</span>
      <input type="text" name="spec_code" value="{{ spec_code }}" placeholder="e.g. 3.1.2 or Networks">
    </label>
    <label>Merged quiz pairs <span style="font-weight:400;color:#888">(optional — e.g. Q1+Q2; Q3+Q4)</span>
      <input type="text" name="merge_groups" value="{{ merge_groups_raw }}" placeholder="Q1+Q2; Q3+Q4" style="width:320px">
    </label>
    <button type="submit" class="btn">Find Evidence</button>
  </form>
</div>

{% if error %}<div class="card error">{{ error|safe }}</div>{% endif %}

{% if evidence or all_quizzes %}
<div class="card">
  <h2>Top {{ evidence|length }} Evidence Options
    <span class="time-badge">{{ quizzes_checked }} quiz{{ 'zes' if quizzes_checked != 1 else '' }} checked</span>
  </h2>
  <div class="ev-grid">
    {% for ev in evidence %}
    {% set rank = loop.index %}
    <div class="ev-card rank-{{ rank }}">
      <div class="ev-rank">
        {% if rank == 1 %}🥇 Top pick{% elif rank == 2 %}🥈 2nd{% else %}🥉 3rd{% endif %}
      </div>
      <div class="ev-label">{{ ev.label }}</div>
      <div class="ev-meta">
        <span class="ev-pill ev-pill-time">~{{ ev.total_minutes }} min</span>
        {% if ev.avg_percentage is not none %}
        <span class="ev-pill ev-pill-pct">{{ "%.1f"|format(ev.avg_percentage) }}% avg</span>
        {% endif %}
        {% if ev.type == "combined" %}<span class="ev-pill" style="background:#fef9c3;color:#713f12">Combined</span>{% endif %}
      </div>
      {% if ev.quizzes|length == 1 and ev.quizzes[0].source_quiz_codes|length > 1 %}
      <div class="info" style="margin-bottom:.8rem">Built from {{ ev.quizzes[0].source_label }}</div>
      {% endif %}
      <div class="ev-grade">
        <span class="grade-badge grade-{{ ev.grade_class }}">{{ ev.grade }}</span>
        <small>suggested</small>
      </div>

      {% for q in ev.quizzes %}
      <div class="ev-component">
        <b>{{ q.quiz_code }}</b> —
        ~{{ q.est_minutes }} min
        {% if q.avg_percentage is not none %} · {{ "%.1f"|format(q.avg_percentage) }}%{% endif %}
        · {{ q.attempt_count }} attempt{{ 's' if q.attempt_count != 1 else '' }}
        {% if q.source_quiz_codes|length > 1 %} · {{ q.source_label }}{% endif %}
      </div>
      {% endfor %}

      <div class="ev-actions">
        <form method="get" action="{% if ev.source_quiz_codes|length > 1 %}/evidence/pdf/merged{% else %}/evidence/pdf{% endif %}" style="display:block">
          <input type="hidden" name="class_code" value="{{ class_code }}">
          {% if ev.source_quiz_codes|length > 1 %}
          <input type="hidden" name="quiz_codes" value="{{ ev.source_quiz_codes|join(',') }}">
          <input type="hidden" name="merged_name" value="{{ ev.quizzes[0].quiz_code if ev.quizzes|length == 1 else ev.label }}">
          {% else %}
          <input type="hidden" name="quiz_code" value="{{ ev.source_quiz_codes[0] }}">
          {% endif %}
          {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
          <details style="margin-top:.5rem">
            <summary style="cursor:pointer;color:#0f3460;font-size:.85rem">PDF options</summary>
            {{ render_pdf_options('ev_' ~ rank)|safe }}
          </details>
          <button type="submit" class="btn btn-green btn-sm" style="margin-top:.5rem">⬇ {% if ev.source_quiz_codes|length > 1 %}Merged PDF{% else %}PDF{% endif %}</button>
        </form>
      </div>
    </div>
    {% endfor %}
  </div>
</div>

<div class="card">
  <h2>All Quizzes Analysed</h2>
  <table>
    <thead>
      <tr>
        <th>Quiz Code</th>
        <th>Est. Time (min)</th>
        <th>Avg %</th>
        <th>Suggested Grade</th>
        <th>Attempts</th>
        <th>Latest Attempt</th>
        <th>Actions</th>
      </tr>
    </thead>
    <tbody>
      {% for q in all_quizzes %}
      <tr>
        <td>
          {{ q.quiz_code }}
          {% if q.source_quiz_codes|length > 1 %}
          <br><small style="color:#64748b">{{ q.source_label }}</small>
          {% endif %}
        </td>
        <td>~{{ q.est_minutes }}</td>
        <td>
          {% if q.avg_percentage is not none %}
          <div class="bar-wrap"><div class="bar-fill" style="width:{{ [q.avg_percentage,100]|min }}%"></div></div>
          {{ "%.1f"|format(q.avg_percentage) }}%
          {% else %}—{% endif %}
        </td>
        <td><span class="grade-badge grade-{{ grade_class_of(q.avg_percentage) }}">{{ grade_of(q.avg_percentage) }}</span></td>
        <td>{{ q.attempt_count }}</td>
        <td>{{ q.latest_date or "—" }}</td>
        <td>
          <form method="get" action="{% if q.source_quiz_codes|length > 1 %}/evidence/pdf/merged{% else %}/evidence/pdf{% endif %}" style="display:inline-block;min-width:180px">
            <input type="hidden" name="class_code" value="{{ class_code }}">
            {% if q.source_quiz_codes|length > 1 %}
            <input type="hidden" name="quiz_codes" value="{{ q.source_quiz_codes|join(',') }}">
            <input type="hidden" name="merged_name" value="{{ q.quiz_code }}">
            {% else %}
            <input type="hidden" name="quiz_code" value="{{ q.quiz_code }}">
            {% endif %}
            {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
            <details>
              <summary style="cursor:pointer;color:#0f3460;font-size:.8rem">PDF options</summary>
              {{ render_pdf_options('all_' ~ loop.index0)|safe }}
            </details>
            <button type="submit" class="btn btn-sm btn-green" style="margin-top:.35rem">⬇ {% if q.source_quiz_codes|length > 1 %}Merged PDF{% else %}PDF{% endif %}</button>
          </form>
        </td>
      </tr>
      {% endfor %}
    </tbody>
  </table>
</div>

{% if merged_assessments %}
<div class="card">
  <h2>Merged Assessments
    <span class="time-badge">{{ merged_assessments|length }} merge{{ 's' if merged_assessments|length != 1 else '' }}</span>
  </h2>
  {% for merged in merged_assessments %}
  <div style="border:1px solid #dbe3f0;border-radius:10px;padding:1rem;margin-top:1rem;background:#f8fbff">
    <div class="meta" style="margin-bottom:1rem">
      <div class="meta-item"><span>Name</span><span>{{ merged.quiz_code }}</span></div>
      <div class="meta-item"><span>Source quizzes</span><span>{{ merged.source_label }}</span></div>
      <div class="meta-item"><span>Est. time</span><span>~{{ merged.est_minutes }} min</span></div>
      <div class="meta-item"><span>Attempted both</span><span>{{ merged.attempt_count }}</span></div>
      <div class="meta-item"><span>Avg %</span><span>{% if merged.avg_percentage is not none %}{{ "%.1f"|format(merged.avg_percentage) }}%{% else %}—{% endif %}</span></div>
    </div>

    <form method="get" action="/evidence/pdf/merged" style="margin-bottom:1rem">
      <input type="hidden" name="class_code" value="{{ class_code }}">
      <input type="hidden" name="quiz_codes" value="{{ merged.source_quiz_codes|join(',') }}">
      <input type="hidden" name="merged_name" value="{{ merged.quiz_code }}">
      {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
      <details>
        <summary style="cursor:pointer;color:#0f3460;font-size:.85rem">PDF options</summary>
        {{ render_pdf_options('merged_' ~ loop.index0)|safe }}
      </details>
      <button type="submit" class="btn btn-green btn-sm" style="margin-top:.5rem">⬇ Download merged PDF</button>
    </form>

    {% if merged.student_rows %}
    <div style="overflow-x:auto">
      <table>
        <thead>
          <tr>
            <th>Cand #</th>
            <th>Student</th>
            <th>Email</th>
            <th>{{ merged.quiz_code }}</th>
            {% for qc in merged.source_quiz_codes %}<th>{{ qc }}</th>{% endfor %}
          </tr>
        </thead>
        <tbody>
          {% for row in merged.student_rows %}
          <tr>
            <td>{{ row.candidate_no or "—" }}</td>
            <td>{{ row.full_name or row.email }}</td>
            <td>{{ row.email }}</td>
            <td>
              {% if row.percentage is not none %}
              <div class="bar-wrap"><div class="bar-fill" style="width:{{ [row.percentage,100]|min }}%"></div></div>
              {{ "%.1f"|format(row.percentage) }}%
              {% else %}—{% endif %}
            </td>
            {% for qc in merged.source_quiz_codes %}
            {% set component_pct = row.component_percentages.get(qc) %}
            <td>{% if component_pct is not none %}{{ "%.1f"|format(component_pct) }}%{% else %}—{% endif %}</td>
            {% endfor %}
          </tr>
          {% endfor %}
        </tbody>
      </table>
    </div>
    {% else %}
    <p class="no-data">No students have attempted every quiz in this merged assessment yet.</p>
    {% endif %}
  </div>
  {% endfor %}
</div>
{% endif %}

{% if student_evidence %}
<div class="card">
  <h2>Per-Student Best Evidence
    <span class="time-badge">{{ student_evidence|length }} students</span>
  </h2>
  <div style="overflow-x:auto">
  <table>
    <thead>
      <tr>
        <th>Cand #</th>
        <th>Student</th>
        <th>#1 Evidence</th>
        <th>#2 Evidence</th>
        <th>#3 Evidence</th>
      </tr>
    </thead>
    <tbody>
      {% for s in student_evidence %}
      {% set student_index = loop.index0 %}
      <tr>
        <td style="white-space:nowrap">{{ s.candidate_no or "—" }}</td>
        <td style="white-space:nowrap">
          {{ s.full_name or s.email }}
          {% if s.full_name %}<br><small style="color:#888">{{ s.email }}</small>{% endif %}
        </td>
        {% for i in range(3) %}
          {% if i < s.evidence|length %}
          {% set ev = s.evidence[i] %}
          <td style="min-width:200px;vertical-align:top">
            <div style="font-weight:700;font-size:.85rem;color:#0f3460;margin-bottom:.2rem">{{ ev.label }}</div>
            {% if ev.quizzes[0].source_quiz_codes|length > 1 %}
            <div style="font-size:.75rem;color:#64748b;margin-bottom:.3rem">{{ ev.quizzes[0].source_label }}</div>
            {% endif %}
            <div style="font-size:.8rem;color:#555;margin-bottom:.3rem">
              ~{{ ev.total_minutes }} min
              {% if ev.avg_percentage is not none %} &middot; {{ "%.0f"|format(ev.avg_percentage) }}%{% endif %}
            </div>
            <span class="grade-badge grade-{{ ev.grade_class }}" style="font-size:.8rem;margin-bottom:.4rem;display:inline-block">{{ ev.grade }}</span>
            <form method="get" action="{% if ev.source_quiz_codes|length > 1 %}/evidence/pdf/merged{% else %}/evidence/pdf{% endif %}" style="margin-top:.35rem">
              <input type="hidden" name="class_code" value="{{ class_code }}">
              {% if ev.source_quiz_codes|length > 1 %}
              <input type="hidden" name="quiz_codes" value="{{ ev.source_quiz_codes|join(',') }}">
              <input type="hidden" name="merged_name" value="{{ ev.quizzes[0].quiz_code if ev.quizzes|length == 1 else ev.label }}">
              {% else %}
              <input type="hidden" name="quiz_code" value="{{ ev.source_quiz_codes[0] }}">
              {% endif %}
              <input type="hidden" name="student_email" value="{{ s.email }}">
              <details>
                <summary style="cursor:pointer;color:#0f3460;font-size:.8rem">PDF options</summary>
                {{ render_pdf_options('student_' ~ student_index ~ '_' ~ i)|safe }}
              </details>
              <button type="submit" class="btn btn-green btn-sm" style="margin-top:.35rem">⬇ {% if ev.source_quiz_codes|length > 1 %}Merged PDF{% else %}PDF{% endif %}</button>
            </form>
          </td>
          {% else %}
          <td style="color:#ccc;text-align:center;vertical-align:middle">—</td>
          {% endif %}
        {% endfor %}
      </tr>
      {% endfor %}
    </tbody>
  </table>
  </div>
</div>
{% endif %}

{% endif %}
"""

PLANNER_TEMPLATE = BASE_STYLE + """
<h1>Grade Viewer</h1>

<nav class="tabs">
  <a class="tab" href="/">Grades</a>
  <a class="tab" href="/evidence">Best Evidence</a>
  <a class="tab active" href="/evidence/planner">Evidence Planner</a>
</nav>

<div class="card">
  <h2>Evidence Planner</h2>
  <p class="info" style="margin-bottom:1rem">
    This page uses the existing evidence file <strong>y11scores.csv</strong>. Tick the students you want,
    enter quiz codes separated by commas, and optionally define merge groups using
    <strong>semicolon-separated groups</strong> such as <strong>Q1+Q2; Q3+Q4</strong>.
  </p>
  <div style="display:flex;flex-wrap:wrap;gap:.45rem;margin-bottom:1rem">
    {% for band in grade_thresholds %}
    <span class="score-chip" style="background:#f8fafc;color:#0f172a;border:1px solid #dbe3f0">
      <span class="grade-badge grade-{{ band.badge }}" style="margin-left:0">{{ band.label }}</span>
      <span>{{ band.threshold }}</span>
    </span>
    {% endfor %}
  </div>
  <form method="get" action="/evidence/planner">
    <label>Class Code
      <input type="text" name="class_code" value="{{ class_code }}" placeholder="e.g. oxaqa25" required>
    </label>
    <label>Quiz Codes
      <input type="text" name="quiz_codes" value="{{ quiz_codes_raw }}" placeholder="Q1, Q2, Q3" style="width:320px" required>
    </label>
    <label>Merged Quiz Groups
      <input type="text" name="merge_groups" value="{{ merge_groups_raw }}" placeholder="Q1+Q2; Q3+Q4" style="width:320px">
    </label>
    <button type="submit" class="btn">Show Scores</button>
    <button type="button" class="btn soft-btn" onclick="document.querySelectorAll('input[name=selected_candidate]').forEach(el => el.checked = true)">Select All</button>
    <button type="button" class="btn soft-btn" onclick="document.querySelectorAll('input[name=selected_candidate]').forEach(el => el.checked = false)">Clear All</button>

    <div style="width:100%;margin-top:.8rem">
      <div class="section-title">Students</div>
      <div class="student-picker">
        {% for student in students %}
        <label class="student-option">
          <div>
            <input type="checkbox" name="selected_candidate" value="{{ student.candidate_no }}" {% if student.selected %}checked{% endif %}>
            <span class="student-name">{{ student.display_name }}</span>
          </div>
          <span class="student-meta">#{{ student.candidate_no }} · {{ student.evidence_count }} existing evidence piece{{ 's' if student.evidence_count != 1 else '' }}</span>
          {% if student.email %}<span class="student-meta">{{ student.email }}</span>{% endif %}
          <div class="student-tags">
            {% for item in student.existing_items %}
            <span class="score-chip score-chip-existing">{{ item.label }}: {{ item.display }} · {{ item.grade_label }}</span>
            {% endfor %}
          </div>
        </label>
        {% endfor %}
      </div>
    </div>
  </form>
</div>

{% if error %}<div class="card error">{{ error }}</div>{% endif %}

{% if selected_results %}
<div class="card">
  <div class="meta">
    <div class="meta-item"><span>Selected Students</span><span>{{ selected_results|length }}</span></div>
    <div class="meta-item"><span>Quizzes</span><span>{{ quiz_codes|length }}</span></div>
    <div class="meta-item"><span>Merged Groups</span><span>{{ merge_groups|length }}</span></div>
  </div>
</div>

<div class="card">
  <div style="overflow-x:auto">
    <table>
      <thead>
        <tr>
          <th>Candidate #</th>
          <th>Student</th>
          <th>Existing Evidence</th>
          {% for quiz_code in quiz_codes %}<th>{{ quiz_code }}</th>{% endfor %}
          {% for group in merge_groups %}<th>{{ group.label }}</th>{% endfor %}
        </tr>
      </thead>
      <tbody>
        {% for row in selected_results %}
        <tr>
          <td>{{ row.candidate_no }}</td>
          <td style="white-space:nowrap">
            {{ row.display_name }}
            {% if row.email %}<br><small style="color:#64748b">{{ row.email }}</small>{% endif %}
          </td>
          <td class="score-cell">
            {% for item in row.existing_items %}
            <div class="score-chip score-chip-existing" style="margin-bottom:.35rem">{{ item.label }}: {{ item.display }} · {{ item.grade_label }}</div>
            {% endfor %}
            {% if not row.existing_items %}<span class="no-data">No existing evidence</span>{% endif %}
          </td>
          {% for cell in row.quiz_scores %}
          <td class="score-cell">
            {% if cell.percentage is not none %}
            <div class="score-main">{{ "%.1f"|format(cell.percentage) }}%</div>
            <div class="score-sub">~{{ cell.minutes }} min · {{ grade_of(cell.percentage) }}</div>
            {% else %}
            <span class="no-data">—</span>
            {% endif %}
          </td>
          {% endfor %}
          {% for cell in row.merged_scores %}
          <td class="score-cell">
            {% if cell.percentage is not none %}
            <div class="score-main">{{ "%.1f"|format(cell.percentage) }}%</div>
            <div class="score-sub">~{{ cell.total_minutes }} min · {{ grade_of(cell.percentage) }}</div>
            {% if cell.total_questions %}
            <div class="score-sub">Attempted {{ cell.attempted_questions }}/{{ cell.total_questions }} questions ({{ "%.0f"|format((cell.attempted_questions / cell.total_questions) * 100) }}%)</div>
            {% endif %}
            <div class="score-chip score-chip-merge" style="margin-top:.35rem">{{ '1 hr+' if cell.total_minutes >= 60 else 'Under 1 hr' }}</div>
            {% elif cell.missing %}
            <div class="score-sub">Missing: {{ cell.missing|join(', ') }}</div>
            {% else %}
            <span class="no-data">—</span>
            {% endif %}
          </td>
          {% endfor %}
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>
{% endif %}
"""


# ---------------------------------------------------------------------------
# PDF generation
# ---------------------------------------------------------------------------

def _download_image(url: str) -> io.BytesIO | None:
    """Download image URL and return as BytesIO, or None on failure."""
    try:
        r = requests.get(url, timeout=20)
        r.raise_for_status()
        buf = io.BytesIO(r.content)
        buf.seek(0)
        return buf
    except Exception:
        return None


def _is_image_only_response(answer) -> bool:
  """
  Detect if the student response is image-only:
  - answer is a string URL/data-url pointing to an image, OR
  - answer is a dict with an image key but no text.
  """
  if answer is None:
    return False
  if isinstance(answer, str):
    low = answer.lower().strip()
    return (low.startswith("http") or low.startswith("data:image/")) and any(
      ext in low for ext in (".jpg", ".jpeg", ".png", ".gif", ".webp", "/image", "image/")
    )
  if isinstance(answer, dict):
    has_image = bool(answer.get("image_url") or answer.get("image"))
    has_text = bool(str(answer.get("text", "")).strip())
    return has_image and not has_text
  return False


def _answer_image_url(answer) -> str | None:
  if isinstance(answer, str):
    low = answer.lower().strip()
    if (low.startswith("http") or low.startswith("data:image/")) and any(
      ext in low for ext in (".jpg", ".jpeg", ".png", ".gif", ".webp", "/image", "image/")
    ):
      return answer
  if isinstance(answer, dict):
    return answer.get("image_url") or answer.get("image")
  return None


def _answer_text(answer) -> str:
  if answer is None:
    return ""
  if isinstance(answer, str):
    return answer
  if isinstance(answer, dict):
    return answer.get("text", "") or ""
  return str(answer)


def _extract_image_src(value: str) -> str | None:
  if not value:
    return None
  match = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', value, re.IGNORECASE)
  if match:
    return match.group(1).strip()
  return None


def _strip_image_tags(value: str) -> str:
  if not value:
    return ""
  return re.sub(r'<img[^>]*>', '', value, flags=re.IGNORECASE).strip()


def _format_question_max_marks(value) -> str | None:
  if value is None:
    return None
  try:
    numeric = float(value)
  except (TypeError, ValueError):
    return None
  if numeric.is_integer():
    numeric = int(numeric)
  suffix = "mark" if numeric == 1 else "marks"
  return f"[{numeric} {suffix}]"


def _normalise_attempt_questions(attempt: dict) -> dict:
  if attempt.get("questions"):
    return attempt
  for alt in ("question_list", "responses", "answers", "items", "quiz_responses"):
    if attempt.get(alt):
      return {**attempt, "questions": attempt[alt]}
  return attempt


def _build_candidate_map(emails: list[str]) -> dict:
  db = get_db()
  candidate_map = {}
  for email in {email.lower() for email in emails if email}:
    row = db.execute("SELECT * FROM candidates WHERE email=?", (email,)).fetchone()
    if row:
      candidate_map[email] = dict(row)
  return candidate_map


def _should_replace_attempt(previous: dict | None, current: dict) -> bool:
  if previous is None:
    return True

  previous_pct = attempt_percentage(previous)
  current_pct = attempt_percentage(current)
  if current_pct is not None and previous_pct is None:
    return True
  if current_pct is not None and previous_pct is not None and current_pct > previous_pct:
    return True
  if current_pct == previous_pct:
    previous_date = _attempt_date(previous)
    current_date = _attempt_date(current)
    return current_date is not None and (previous_date is None or current_date > previous_date)
  return False


def build_student_best_attempt_map(raw_by_quiz: dict) -> dict:
  best_attempts = {}
  for quiz_code, attempts in raw_by_quiz.items():
    for raw_attempt in attempts:
      attempt = _normalise_attempt_questions(raw_attempt)
      email = (attempt.get("student_email") or "").strip().lower()
      if not email:
        continue
      previous = best_attempts.setdefault(email, {}).get(quiz_code)
      if _should_replace_attempt(previous, attempt):
        best_attempts[email][quiz_code] = {**attempt, "quiz_code": quiz_code}
  return best_attempts


def _build_pdf_image(
  url: str,
  *,
  max_width: float,
  max_height: float,
  img_pct: float,
  crop_top_pct: float = 0.0,
) -> RLImage | None:
  img_buf = _download_image(url)
  if not img_buf:
    return None

  try:
    with PILImage.open(img_buf) as pil:
      image = PILImageOps.exif_transpose(pil)
      if crop_top_pct > 0:
        crop_pixels = int(image.height * (crop_top_pct / 100.0))
        if 0 < crop_pixels < image.height:
          image = image.crop((0, crop_pixels, image.width, image.height))

      width, height = image.size
      if not width or not height:
        return None

      target_width = min(max_width * max(img_pct, 1) / 100.0, max_width)
      scale = min(target_width / width, max_height / height, 1.0)
      output = io.BytesIO()
      image.save(output, format="PNG")
      output.seek(0)
      return RLImage(output, width=width * scale, height=height * scale)
  except Exception:
    return None


def _pdf_request_options(args) -> dict:
  def arg_bool(name: str) -> bool:
    return args.get(name) in {"1", "true", "True", "on", "yes"}

  def arg_float(name: str, default: float, minimum: float | None = None, maximum: float | None = None) -> float:
    try:
      value = float(args.get(name, default))
    except (TypeError, ValueError):
      value = default
    if minimum is not None:
      value = max(minimum, value)
    if maximum is not None:
      value = min(maximum, value)
    return value

  return {
    "inc_marks": arg_bool("inc_marks"),
    "inc_percentage": arg_bool("inc_percentage"),
    "inc_question_marks": arg_bool("inc_question_marks"),
    "inc_comments": arg_bool("inc_comments"),
    "inc_questions": arg_bool("inc_questions"),
    "inc_labels": arg_bool("inc_labels"),
    "centre_number": (args.get("centre_number", "") or "").strip(),
    "margin_tb": arg_float("margin_tb", 15, 5, 50),
    "margin_lr": arg_float("margin_lr", 15, 5, 50),
    "img_pct": arg_float("img_pct", 100, 30, 150),
    "img_crop_pct": arg_float("img_crop_pct", 3, 0, 25),
    "page_break_between": args.get("page_break", "1") == "1",
  }


def render_pdf_options(uid: str) -> str:
  return PDF_OPTIONS_PARTIAL.replace("{uid}", uid)


def _pdf_text(value) -> str:
  if value is None:
    return ""
  return html.escape(str(value), quote=False)


def _question_answer_parts(question: dict) -> tuple[str, str, bool]:
  answer_payload = (
    question.get("answer")
    or question.get("response")
    or question.get("student_answer")
    or question.get("student_response")
    or question.get("answer_data")
  )
  answer_image = question.get("answer_image_url") or _answer_image_url(answer_payload) or ""
  answer_text = question.get("answer_text")
  if answer_text is None:
    answer_text = _answer_text(answer_payload)
  answer_text = answer_text or ""
  if not answer_image:
    answer_image = _extract_image_src(answer_text) or ""
  answer_text = _strip_image_tags(answer_text)
  if not answer_image:
    answer_image = _answer_image_url(answer_text) or ""
  if answer_image and answer_text.strip() == answer_image:
    answer_text = ""
  has_image = bool(question.get("has_image", False) or answer_image or _is_image_only_response(answer_payload))
  is_image_answer = bool(answer_image) or (has_image and not answer_text.strip())
  return answer_text, answer_image, is_image_answer


def _question_prompt_parts(question: dict) -> tuple[str, str]:
  question_text = question.get("question") or ""
  question_image = question.get("question_image_url") or ""
  if not question_image:
    question_image = _extract_image_src(question_text) or ""
  question_text = _strip_image_tags(question_text)
  if not question_image:
    question_image = _answer_image_url(question_text) or ""
  if question_image and question_text.strip() == question_image:
    question_text = ""
  return question_text, question_image


def _question_attempt_progress(attempt: dict) -> tuple[int | None, int | None]:
  questions = (
    attempt.get("questions")
    or attempt.get("question_list")
    or attempt.get("responses")
    or attempt.get("answers")
    or attempt.get("items")
    or attempt.get("quiz_responses")
    or []
  )
  if not questions:
    return None, None

  attempted = 0
  total = 0
  for question in questions:
    if not isinstance(question, dict):
      continue
    total += 1
    answer_text, answer_image, is_image_answer = _question_answer_parts(question)
    if answer_text.strip() or answer_image or is_image_answer:
      attempted += 1

  return attempted, total


def build_merged_pdf_attempts(best_attempts: dict, quiz_codes: list[str], student_email: str = "") -> tuple[list, list[str]]:
  if student_email:
    candidate_pairs = [(student_email, best_attempts.get(student_email, {}))]
  else:
    candidate_pairs = sorted(best_attempts.items())

  eligible_attempts = []
  eligible_emails = []
  for email, score_map in candidate_pairs:
    if not score_map or not all(score_map.get(quiz_code) for quiz_code in quiz_codes):
      continue

    component_attempts = [_normalise_attempt_questions(score_map[quiz_code]) for quiz_code in quiz_codes]
    total_possible = sum((attempt.get("marks_possible") or 0) for attempt in component_attempts)
    total_awarded_values = [attempt.get("marks_awarded") for attempt in component_attempts if attempt.get("marks_awarded") is not None]
    merged_questions = []
    for attempt in component_attempts:
      merged_questions.extend(attempt.get("questions") or [])

    merged_attempt = dict(component_attempts[0])
    merged_attempt.update({
      "student_email": email,
      "marks_awarded": sum(total_awarded_values) if total_awarded_values else None,
      "marks_possible": total_possible or None,
      "percentage": _merged_percentage(component_attempts),
      "questions": merged_questions,
      "_quiz_length_minutes": round(total_possible) if total_possible else None,
      "_display_quiz_code": "",
    })
    eligible_attempts.append(merged_attempt)
    eligible_emails.append(email)

  return eligible_attempts, eligible_emails


def generate_pdf(
    class_code: str,
    quiz_code: str,
    attempts_data: list,
    candidate_map: dict,
    *,
    inc_marks: bool = True,
  inc_percentage: bool = True,
  inc_question_marks: bool = True,
    inc_comments: bool = True,
    inc_questions: bool = True,
    inc_labels: bool = True,
  centre_number: str = "",
    margin_tb: float = 15,
    margin_lr: float = 15,
    img_pct: float = 100,
    img_crop_pct: float = 3.0,
    page_break_between: bool = True,
    document_label: str | None = None,
) -> io.BytesIO:
    buf = io.BytesIO()

    page_w, page_h = A4
    usable_w = page_w - 2 * margin_lr * mm
    usable_h = page_h - 2 * margin_tb * mm
    question_img_h = usable_h * 0.38
    response_img_h = usable_h * 0.46

    doc = SimpleDocTemplate(
      buf,
      pagesize=A4,
      topMargin=margin_tb * mm,
      bottomMargin=margin_tb * mm,
      leftMargin=margin_lr * mm,
      rightMargin=margin_lr * mm,
    )

    style_h1 = ParagraphStyle("H1", fontSize=14, fontName="Helvetica-Bold", spaceAfter=4, textColor=colors.HexColor("#0f3460"))
    style_h3 = ParagraphStyle("H3", fontSize=10, fontName="Helvetica-Bold", spaceAfter=2, textColor=colors.HexColor("#374151"))
    style_body = ParagraphStyle("Body", fontSize=9, fontName="Helvetica", spaceAfter=2, leading=13)
    style_small = ParagraphStyle("Small", fontSize=8, fontName="Helvetica", textColor=colors.HexColor("#6b7280"), spaceAfter=2)
    style_label = ParagraphStyle("Label", fontSize=8, fontName="Helvetica-Bold", textColor=colors.HexColor("#0f3460"))
    style_comment = ParagraphStyle("Cmt", fontSize=8, fontName="Helvetica-Oblique", textColor=colors.HexColor("#374151"), spaceAfter=2, leading=12)

    story = [Paragraph("Evidence Pack", style_h1), HRFlowable(width="100%", thickness=1, color=colors.HexColor("#0f3460"), spaceAfter=6)]

    for idx, attempt in enumerate(attempts_data):
      email = attempt.get("student_email", "")
      candidate = candidate_map.get(email.lower(), {})
      full_name = f"{candidate.get('forename', '')} {candidate.get('surname', '')}".strip() or email
      candidate_no = candidate.get("candidate_no", "—")
      school_code = centre_number or candidate.get("school_code", "—")

      awarded = attempt.get("marks_awarded")
      possible = attempt.get("marks_possible")
      percentage = attempt.get("percentage")
      quiz_length = attempt.get("_quiz_length_minutes") or (round(possible) if possible is not None else "—")

      questions = (
        attempt.get("questions")
        or attempt.get("question_list")
        or attempt.get("responses")
        or attempt.get("answers")
        or attempt.get("items")
        or attempt.get("quiz_responses")
        or []
      )

      header_data = [
        [Paragraph("Candidate name", style_label), Paragraph(_pdf_text(full_name), style_body),
         Paragraph("Centre number", style_label), Paragraph(_pdf_text(school_code), style_body)],
        [Paragraph("Candidate #", style_label), Paragraph(_pdf_text(candidate_no), style_body),
         Paragraph("Quiz length", style_label), Paragraph(_pdf_text(f"~{quiz_length} min"), style_body)],
      ]

      if inc_marks or inc_percentage:
        marks_text = f"{awarded} / {possible}" if inc_marks and awarded is not None else "—"
        pct_text = f"{percentage:.1f}%" if percentage is not None else "—"
        header_data.append([
          Paragraph("Total marks", style_label),
          Paragraph(_pdf_text(marks_text if inc_marks else "—"), style_body),
          Paragraph("Percentage", style_label),
          Paragraph(_pdf_text(pct_text if inc_percentage else "—"), style_body),
        ])

      col_w = usable_w / 4
      table = Table(header_data, colWidths=[col_w * 0.7, col_w * 1.3, col_w * 0.7, col_w * 1.3])
      table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#f0f4ff")),
        ("BOX", (0, 0), (-1, -1), 0.5, colors.HexColor("#c7d2fe")),
        ("INNERGRID", (0, 0), (-1, -1), 0.3, colors.HexColor("#e0e7ff")),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ("LEFTPADDING", (0, 0), (-1, -1), 6),
      ]))
      story.append(KeepTogether([table]))
      story.append(Spacer(1, 6 * mm))

      if not questions:
        story.append(Paragraph(
          "⚠ No question/answer data was returned by the API for this attempt. Visit /debug/attempt?class_code=…&quiz_code=… to inspect the raw response.",
          ParagraphStyle("Warn", fontSize=9, textColor=colors.HexColor("#991b1b"), fontName="Helvetica-Oblique"),
        ))
        story.append(Spacer(1, 4 * mm))

      for q_idx, question in enumerate(questions, 1):
        question_text, question_image_url = _question_prompt_parts(question)
        answer_text, answer_image_url, is_image_answer = _question_answer_parts(question)
        question_marks = question.get("marks")
        question_possible = question.get("maxmarks")
        comment = question.get("comment") or ""

        question_block = []
        question_label = f"Q{q_idx}"
        question_block.append(Paragraph(question_label, style_h3))

        if inc_questions:
          if question_text:
            for line in question_text.split("\n"):
              if line.strip():
                question_block.append(Paragraph(_pdf_text(line), style_body))
          if question_image_url:
            question_image = _build_pdf_image(
              question_image_url,
              max_width=usable_w,
              max_height=question_img_h,
              img_pct=img_pct,
            )
            if question_image:
              question_block.append(question_image)
            else:
              question_block.append(Paragraph("[Question image could not be loaded]", style_small))

        if inc_question_marks:
          max_marks_label = _format_question_max_marks(question_possible)
          if max_marks_label:
            question_block.append(Paragraph(_pdf_text(max_marks_label), style_small))
            question_block.append(Spacer(1, 1.5 * mm))

        if inc_labels:
          question_block.append(Paragraph("Student response:", style_label))
          question_block.append(Spacer(1, 3 * mm))

        if is_image_answer:
          response_image = _build_pdf_image(
            answer_image_url,
            max_width=usable_w,
            max_height=response_img_h,
            img_pct=img_pct,
            crop_top_pct=img_crop_pct,
          )
          if response_image:
            question_block.append(response_image)
          else:
            question_block.append(Paragraph("[Image response could not be loaded]", style_small))
        else:
          if answer_text:
            for line in answer_text.split("\n"):
              question_block.append(Paragraph(_pdf_text(line) or " ", style_body))
          else:
            question_block.append(Paragraph("(no response)", style_small))

        if inc_comments and comment:
          question_block.append(Spacer(1, 2 * mm))
          question_block.append(Paragraph(_pdf_text(f"Examiner comment: {comment}"), style_comment))

        question_block.append(HRFlowable(width="100%", thickness=0.4, color=colors.HexColor("#d1d5db"), spaceAfter=4))
        story.extend(question_block)

      if page_break_between and idx < len(attempts_data) - 1:
        story.append(PageBreak())
      else:
        story.append(Spacer(1, 10 * mm))

    doc.build(story)
    buf.seek(0)
    return buf


# ---------------------------------------------------------------------------
# Flask routes
# ---------------------------------------------------------------------------

@app.route("/")
def index():
    class_code = request.args.get("class_code", "").strip()
    quiz_code  = request.args.get("quiz_code", "").strip()

    data      = None
    attempts  = []
    error     = None
    est_minutes = None

    if class_code and quiz_code:
        try:
            data = fetch_grades(class_code, quiz_code)
            raw  = data.get("attempts", [])

            # Enrich with candidate DB lookup
            rows = []
            for a in sorted(raw, key=lambda x: x.get("student_email", "")):
                email   = a.get("student_email", "unknown")
                cand    = lookup_candidate(email) or {}
                awarded = a.get("marks_awarded")
                possible = a.get("marks_possible")
                fully   = a.get("fully_marked", False)
                unmarked = a.get("questions_unmarked", 0)

                if fully:
                    status = "Marked"
                elif unmarked > 0:
                    status = f"{unmarked} unmarked"
                else:
                    status = "Partial"

                full_name = f"{cand.get('forename','')} {cand.get('surname','')}".strip()
                rows.append({
                    "email":        email,
                    "attempt_id":   a.get("id") or a.get("attempt_id", ""),
                    "candidate_no": cand.get("candidate_no", ""),
                    "full_name":    full_name,
                    "marks_str":    f"{awarded}/{possible}" if awarded is not None else "—/—",
                    "marks_possible": possible,
                    "percentage":   a.get("percentage"),
                    "status":       status,
                })
            attempts = rows

            # Estimate time: max marks possible for first attempt with data
            max_marks = next(
                (r["marks_possible"] for r in rows if r["marks_possible"] is not None), None
            )
            if max_marks is not None:
                est_minutes = max_marks  # 1 mark ≈ 1 minute

        except requests.HTTPError as e:
            body = {}
            try:
                body = e.response.json()
            except Exception:
                pass
            error = f"API error {e.response.status_code}: {body.get('error', str(e))}"
        except requests.RequestException as e:
            error = f"Request failed: {e}"

    return render_template_string(
        INDEX_TEMPLATE,
        class_code=class_code,
        quiz_code=quiz_code,
        data=data,
        attempts=attempts,
        error=error,
        est_minutes=est_minutes,
    )


@app.route("/pdf")
def pdf():
    class_code   = request.args.get("class_code", "").strip()
    quiz_code    = request.args.get("quiz_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()
    pdf_options = _pdf_request_options(request.args)

    if not class_code or not quiz_code:
        return "Missing class_code or quiz_code", 400

    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
    except requests.HTTPError as e:
        return f"API error: {e}", 502
    except requests.RequestException as e:
        return f"Request failed: {e}", 502

    attempts_raw = data.get("attempts", [])
    if student_email:
        attempts_raw = [a for a in attempts_raw if a.get("student_email", "").lower() == student_email]

    enriched = [_normalise_attempt_questions(attempt) for attempt in attempts_raw]

    print(f"[PDF] {len(enriched)} attempt(s). First has {len(enriched[0].get('questions', []))} questions." if enriched else "[PDF] No attempts.")

    candidate_map = _build_candidate_map([a.get("student_email", "") for a in enriched])

    pdf_buf = generate_pdf(
        class_code, quiz_code, enriched, candidate_map,
        **pdf_options,
    )

    filename = f"evidence_{class_code}_{quiz_code}.pdf".replace(" ", "_")
    return send_file(pdf_buf, mimetype="application/pdf",
                     as_attachment=True, download_name=filename)


@app.route("/admin/reimport-candidates")
def reimport_candidates():
    init_db()
    return "Candidates re-imported successfully.", 200


@app.route("/evidence")
def evidence():
    class_code    = request.args.get("class_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()
    target_min    = int(request.args.get("target_min", 50))
    target_max    = int(request.args.get("target_max", 70))
    manual_codes  = request.args.get("quiz_codes", "").strip()
    merge_groups_raw = request.args.get("merge_groups", "").strip()
    months_ago_raw = request.args.get("months_ago", "").strip()
    months_ago    = int(months_ago_raw) if months_ago_raw.isdigit() else None
    spec_code     = request.args.get("spec_code", "").strip()

    ev_results      = []
    all_quizzes     = []
    student_evidence = []
    merged_assessments = []
    error           = None
    quizzes_checked = 0
    merge_groups    = parse_merge_groups(merge_groups_raw, name_prefix="assessment_merge")

    if class_code:
        try:
            infos, raw_by_quiz = discover_quiz_summaries(class_code, manual_codes, months_ago, spec_code)
            quizzes_checked = len(infos)

            explicit_merge_codes = [quiz_code for group in merge_groups for quiz_code in group["quiz_codes"]]
            if explicit_merge_codes:
                raw_by_quiz = ensure_quiz_attempt_groups(class_code, raw_by_quiz, explicit_merge_codes, months_ago)
                existing_codes = {item["quiz_code"] for item in infos}
                for quiz_code in explicit_merge_codes:
                    if quiz_code in existing_codes:
                        continue
                    infos.extend(_summaries_from_groups({quiz_code: raw_by_quiz.get(quiz_code, [])}))
                    existing_codes.add(quiz_code)

            merged_infos, merged_details = build_merged_quiz_summaries(raw_by_quiz, merge_groups)
            merged_assessments = [{**item, "student_rows": merged_details.get(item["quiz_code"], [])} for item in merged_infos]
            all_quizzes = sorted(infos + merged_infos, key=lambda x: x["est_minutes"], reverse=True)
            ev_results = find_best_evidence(all_quizzes, target_min=target_min, target_max=target_max, top_n=3)
            student_evidence = compute_per_student_evidence(raw_by_quiz, target_min, target_max, top_n=3, merge_groups=merge_groups)

            # Enrich with candidate DB info
            db = get_db()
            for s in student_evidence:
                row = db.execute("SELECT * FROM candidates WHERE email=?", (s["email"],)).fetchone()
                if row:
                    row = dict(row)
                    s["candidate_no"] = row.get("candidate_no", "—")
                    s["full_name"] = f"{row.get('forename','')} {row.get('surname','')}".strip()
                else:
                    s["candidate_no"] = "—"
                    s["full_name"] = ""

            for merged in merged_assessments:
                for row in merged["student_rows"]:
                    candidate = db.execute("SELECT * FROM candidates WHERE email=?", (row["email"],)).fetchone()
                    if candidate:
                        candidate = dict(candidate)
                        row["candidate_no"] = candidate.get("candidate_no", "—")
                        row["full_name"] = f"{candidate.get('forename', '')} {candidate.get('surname', '')}".strip()
                    else:
                        row["candidate_no"] = "—"
                        row["full_name"] = ""
        except requests.HTTPError as e:
            body = {}
            try: body = e.response.json()
            except Exception: pass
            error = f"API error {e.response.status_code}: {body.get('error', str(e))}"
        except requests.RequestException as e:
            error = f"Request failed: {e}"
        except Exception as e:
            error = f"Error: {e}"

        if class_code and not error and not all_quizzes:
            error = (
                "No quizzes were detected automatically. "
                "This usually means the attempt records don't include a quiz_code field. "
                f"Check <a href='/debug/attempt?class_code={class_code}&quiz_code=test'>the debug endpoint</a> "
                "to see the raw attempt structure, then enter quiz codes manually above."
            )

    return render_template_string(
        EVIDENCE_TEMPLATE,
        class_code=class_code,
        student_email=student_email,
        target_min=target_min,
        target_max=target_max,
        quiz_codes=manual_codes,
        merge_groups_raw=merge_groups_raw,
        months_ago=months_ago_raw,
        spec_code=spec_code,
        evidence=ev_results,
        all_quizzes=all_quizzes,
        quizzes_checked=quizzes_checked,
        student_evidence=student_evidence,
        merged_assessments=merged_assessments,
        error=error,
        render_pdf_options=render_pdf_options,
        grade_of=grade_suggestion,
        grade_class_of=grade_badge_class,
    )


@app.route("/evidence/planner")
def evidence_planner():
  class_code = request.args.get("class_code", "").strip()
  quiz_codes_raw = request.args.get("quiz_codes", "").strip()
  merge_groups_raw = request.args.get("merge_groups", "").strip()
  selected_candidate_nos = [value.strip() for value in request.args.getlist("selected_candidate") if value.strip()]

  quiz_codes = parse_code_list(quiz_codes_raw)
  evidence_rows = load_existing_evidence_rows()
  candidate_map = lookup_candidates_by_candidate_numbers([row["candidate_no"] for row in evidence_rows])

  students = []
  selected_set = set(selected_candidate_nos)
  for row in evidence_rows:
    candidate = candidate_map.get(row["candidate_no"], {})
    display_name = f"{candidate.get('forename', '')} {candidate.get('surname', '')}".strip() or row["student_name"]
    students.append({
      **row,
      "display_name": display_name,
      "email": candidate.get("email", ""),
      "selected": row["candidate_no"] in selected_set,
    })

  selected_results = []
  error = None
  merge_groups = parse_merge_groups(merge_groups_raw, quiz_codes)

  if class_code or quiz_codes_raw or selected_candidate_nos:
    if not class_code:
      error = "Enter a class code."
    elif not quiz_codes:
      error = "Enter at least one quiz code."
    elif not selected_candidate_nos:
      error = "Select at least one student."
    else:
      try:
        raw_by_quiz = fetch_quiz_attempt_groups(class_code, quiz_codes, include_questions=True)
        student_score_map = build_student_quiz_score_map(raw_by_quiz)
        for student in students:
          if not student["selected"]:
            continue
          email = (student.get("email") or "").lower()
          score_map = student_score_map.get(email, {}) if email else {}
          selected_results.append({
            "candidate_no": student["candidate_no"],
            "display_name": student["display_name"],
            "email": student["email"],
            "existing_items": student["existing_items"],
            "quiz_scores": [score_map.get(quiz_code, {"percentage": None, "minutes": None}) for quiz_code in quiz_codes],
            "merged_scores": build_merged_score_rows(score_map, merge_groups),
          })
      except requests.HTTPError as e:
        body = {}
        try:
          body = e.response.json()
        except Exception:
          pass
        error = f"API error {e.response.status_code}: {body.get('error', str(e))}"
      except requests.RequestException as e:
        error = f"Request failed: {e}"
      except Exception as e:
        error = f"Error: {e}"

  return render_template_string(
    PLANNER_TEMPLATE,
    class_code=class_code,
    quiz_codes=quiz_codes,
    quiz_codes_raw=quiz_codes_raw,
    merge_groups=merge_groups,
    merge_groups_raw=merge_groups_raw,
    students=students,
    selected_results=selected_results,
    error=error,
    grade_of=grade_suggestion,
    grade_class_of=grade_badge_class,
    grade_thresholds=grade_threshold_rows(),
  )


@app.route("/evidence/pdf")
def evidence_pdf():
    """PDF download triggered from the evidence tab — proxies to /pdf logic."""
    class_code    = request.args.get("class_code", "").strip()
    quiz_code     = request.args.get("quiz_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()
    pdf_options = _pdf_request_options(request.args)

    if not class_code or not quiz_code:
        return "Missing class_code or quiz_code", 400

    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
    except requests.HTTPError as e:
        return f"API error: {e}", 502
    except requests.RequestException as e:
        return f"Request failed: {e}", 502

    attempts_raw = data.get("attempts", [])
    if student_email:
        attempts_raw = [a for a in attempts_raw if a.get("student_email", "").lower() == student_email]

    enriched = [_normalise_attempt_questions(attempt) for attempt in attempts_raw]

    candidate_map = _build_candidate_map([a.get("student_email", "") for a in enriched])

    pdf_buf = generate_pdf(
        class_code, quiz_code, enriched, candidate_map,
        **pdf_options,
    )

    filename = f"evidence_{class_code}_{quiz_code}.pdf".replace(" ", "_")
    return send_file(pdf_buf, mimetype="application/pdf",
                     as_attachment=True, download_name=filename)


@app.route("/evidence/pdf/merged")
def evidence_pdf_merged():
    class_code = request.args.get("class_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()
    quiz_codes = parse_code_list(request.args.get("quiz_codes", ""))
    pdf_options = _pdf_request_options(request.args)

    if not class_code or len(quiz_codes) < 2:
        return "Missing class_code or at least two quiz codes", 400

    try:
        raw_by_quiz = fetch_quiz_attempt_groups(class_code, quiz_codes, include_questions=True)
    except requests.HTTPError as e:
        return f"API error: {e}", 502
    except requests.RequestException as e:
        return f"Request failed: {e}", 502

    best_attempts = build_student_best_attempt_map(raw_by_quiz)
    merged_attempts, eligible_emails = build_merged_pdf_attempts(best_attempts, quiz_codes, student_email)

    if not merged_attempts:
        return "No students have a complete merged attempt for those quiz codes", 404

    candidate_map = _build_candidate_map(eligible_emails)
    pdf_buf = generate_pdf(
        class_code,
      "evidence",
        merged_attempts,
        candidate_map,
        **pdf_options,
    )

    merged_name = request.args.get("merged_name", "").strip() or "merged_assessment"
    filename = f"evidence_{class_code}_{merged_name}.pdf".replace(" ", "_")
    return send_file(pdf_buf, mimetype="application/pdf",
                     as_attachment=True, download_name=filename)


@app.route("/debug/all-attempts")
def debug_all_attempts():
    """Show raw keys from unfiltered attempts endpoint. Usage: /debug/all-attempts?class_code=X"""
    import json
    class_code = request.args.get("class_code", "").strip()
    if not class_code:
        return "Pass ?class_code=X", 400
    try:
        attempts = fetch_all_attempts(class_code)
        out = {
            "total_attempts": len(attempts),
            "first_attempt_keys": list(attempts[0].keys()) if attempts else [],
            "first_attempt_sample": attempts[0] if attempts else None,
            "unique_quiz_code_values": list({
                a.get("quiz_code") or a.get("quiz") or a.get("quiz_id") or a.get("quiz_name") or "(none)"
                for a in attempts[:50]
            }),
        }
        # Also show question spec fields from first attempt with questions
        try:
            first_qc = out["unique_quiz_code_values"][0] if out["unique_quiz_code_values"] else None
            if first_qc and first_qc != "(none)":
                qdata = fetch_grades(class_code, first_qc, include_questions=True)
                qattempts = qdata.get("attempts", [])
                if qattempts:
                    qs = (qattempts[0].get("questions") or [])
                    if qs:
                        out["sample_question_keys"] = list(qs[0].keys())
                        out["sample_question_spec_fields"] = {
                            k: qs[0][k] for k in _SPEC_FIELDS if k in qs[0]
                        }
        except Exception:
            pass
    except Exception as e:
        out = {"error": str(e)}
    return app.response_class(json.dumps(out, indent=2, default=str), mimetype="application/json")


@app.route("/debug/attempt")
def debug_attempt():
    """
    Diagnostic route — shows raw API responses so we can discover correct field names.
    Usage: /debug/attempt?class_code=X&quiz_code=Y
    """
    import json
    class_code = request.args.get("class_code", "").strip()
    quiz_code  = request.args.get("quiz_code", "").strip()
    if not class_code or not quiz_code:
        return "Pass ?class_code=X&quiz_code=Y", 400

    out = {}
    try:
        # Without questions
        grades_data = fetch_grades(class_code, quiz_code, include_questions=False)
        attempts    = grades_data.get("attempts", [])
        out["grades_response_keys"] = list(grades_data.keys())

        if attempts:
            first = attempts[0]
            out["first_attempt_keys"]   = list(first.keys())
            out["first_attempt_sample"] = first
        else:
            out["note"] = "No attempts found"
            return app.response_class(json.dumps(out, indent=2, default=str), mimetype="application/json")

        # With include_questions=true
        grades_with_q = fetch_grades(class_code, quiz_code, include_questions=True)
        attempts_with_q = grades_with_q.get("attempts", [])
        if attempts_with_q:
            first_q = attempts_with_q[0]
            out["first_attempt_with_questions_keys"]   = list(first_q.keys())
            out["questions_count"]                     = len(first_q.get("questions", []))
            # Show first question structure only
            qs = first_q.get("questions") or []
            out["first_question_sample"] = qs[0] if qs else None
            out["first_question_keys"]   = list(qs[0].keys()) if qs else []
        else:
            out["note_with_q"] = "No attempts returned when include_questions=true"
    except Exception as e:
        out["error"] = str(e)

    return app.response_class(
        json.dumps(out, indent=2, default=str),
        mimetype="application/json"
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if not os.path.exists(DB_PATH):
        init_db()
    app.run(debug=True)

