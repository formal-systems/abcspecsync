#!/usr/bin/env python3
"""Side-by-side views of the implementation (left) and the TLA+ specification (right).

One view per group of variables and one per action.  Under each pair of fragments a table says
what binds them (the @TLA_ annotation in the code, the construct in the spec) and whether the
two agree.  The agreement is computed here, from the two source files, each time the views are
generated: a change on either side that breaks a binding shows up as a red cross.

    python3 views/make_views.py              writes views/sync-views.html (and .pdf with Chrome)
    python3 views/make_views.py --no-pdf
    python3 views/make_views.py --cpp other.cpp --spec Other.tla --out /tmp/v.html

The script reads the two files with regular expressions.  It is written for this example (one
module, one C++ file, the annotation names used here) and needs only Python 3.9+.
The exit status is 1 when a check fails, so it can also be used as a quick check from a shell.
"""
from __future__ import annotations

import argparse
import datetime
import html
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
ap.add_argument("--spec", type=Path, default=ROOT / "spec" / "LamportMutex.tla")
ap.add_argument("--cpp", type=Path, default=ROOT / "cpp" / "lamport_mutex.cpp")
ap.add_argument("--out", type=Path, default=HERE / "sync-views.html")
ap.add_argument("--no-pdf", action="store_true", help="write the HTML only")
ARGS = ap.parse_args()
SPEC, CPP, OUT_HTML = ARGS.spec.resolve(), ARGS.cpp.resolve(), ARGS.out.resolve()
OUT_PDF = OUT_HTML.with_suffix(".pdf")
CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
MODULE = SPEC.stem

SL = SPEC.read_text().split("\n")      # spec lines, SL[n - 1] is line n
CL = CPP.read_text().split("\n")       # C++ lines

# TLC results recorded for the three models (see ../README.md); shown on the Models view.
RESULTS = {
    "safety": "4,786 distinct states, depth 27, no error (2 s)",
    "live2": "4,786 distinct states, depth 27, no error: EveryRequestGranted holds (4 s)",
    "live": "7,128,781 distinct states, depth 31, no error: EveryRequestGranted holds for three processes "
            "(26 minutes with 8 threads and a 6 GB heap)",
}


# ---------------------------------------------------------------------------------------------
# annotations: @TLA_NAME{key: value, ...} inside comments, the same form in C++ and in TLA+
# ---------------------------------------------------------------------------------------------
def match_brace(s: str, i: int) -> int:
    """s[i] is '{'; the index of the matching '}' (quotes and backticks protect their content)."""
    depth, j, q = 0, i, ""
    while j < len(s):
        ch = s[j]
        if q:
            if ch == "\\" and q == '"':
                j += 1
            elif ch == q:
                q = ""
        elif ch in '"`':
            q = ch
        elif ch in "{[":
            depth += 1
        elif ch in "}]":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    return -1


def split_top(s: str, sep: str = ",") -> list[str]:
    out, depth, q, cur = [], 0, "", []
    for ch in s:
        if q:
            cur.append(ch)
            if ch == q:
                q = ""
            continue
        if ch in '"`':
            q = ch
        elif ch in "{[(":
            depth += 1
        elif ch in "}])":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur))
    return out


def parse_value(v: str):
    v = v.strip()
    if len(v) >= 2 and v[0] == v[-1] and v[0] in '"`':
        return v[1:-1].replace('\\"', '"') if v[0] == '"' else v[1:-1]
    if v.startswith("[") and v.endswith("]"):
        return [parse_value(x) for x in split_top(v[1:-1])]
    return v


class Ann:
    def __init__(self, kind: str, args: dict, line: int, text: str):
        self.kind, self.args, self.line, self.text = kind, args, line, text

    def __getitem__(self, k):
        return self.args.get(k, "")


def scan(lines: list[str], comment: str) -> list[Ann]:
    out = []
    for n, l in enumerate(lines, 1):
        at = l.find(comment) if comment else 0
        for m in re.finditer(r"@(TLA_[A-Z_]+)\{", l):
            if comment and (at < 0 or m.start() < at):
                continue
            end = match_brace(l, m.end() - 1)
            if end < 0:
                continue
            args = {}
            for part in split_top(l[m.end():end]):
                k, _, v = part.partition(":")
                args[k.strip()] = parse_value(v)
            out.append(Ann(m.group(1), args, n, l[m.start():end + 1]))
    return out


TRACE_SPEC = SPEC.parent / f"{MODULE}Trace.tla"
TL = TRACE_SPEC.read_text().split("\n") if TRACE_SPEC.exists() else []     # trace spec lines
TS_REL = f"spec/{TRACE_SPEC.name}"
# the disjuncts of Step in the trace spec: action -> (line, text, number of arguments)
TSTEP: dict[str, tuple[int, str, int]] = {}
for _n, _l in enumerate(TL, 1):
    _m = re.search(r'e\.action = "(\w+)"\s*/\\ (\w+)\(([^)]*)\)', _l)
    if _m and _m.group(1) == _m.group(2):
        TSTEP[_m.group(1)] = (_n, _l.strip().removeprefix("\\/ "), len([x for x in _m.group(3).split(",") if x.strip()]))

CANNS = scan(CL, "//")
SANNS = scan(SL, "")


def canns(kind: str, **match) -> list[Ann]:
    return [a for a in CANNS if a.kind == kind and all(a.args.get(k) == v for k, v in match.items())]


def sanns(kind: str, **match) -> list[Ann]:
    return [a for a in SANNS if a.kind == kind and all(a.args.get(k) == v for k, v in match.items())]


# ---------------------------------------------------------------------------------------------
# the specification
# ---------------------------------------------------------------------------------------------
def tla_code(l: str) -> str:
    """The line without its \\* comment."""
    return l.split("\\*")[0]


DEFS: dict[str, tuple[int, list[str]]] = {}
for _n, _l in enumerate(SL, 1):
    _m = re.match(r"^(\w+)(?:\(([^)]*)\))?\s*==", _l)
    if _m:
        DEFS[_m.group(1)] = (_n, [a.strip() for a in (_m.group(2) or "").split(",") if a.strip()])


def def_span(name: str, with_comment: bool = True) -> tuple[int, int]:
    """Lines of a definition, with the (* comment *) block above it, up to the next unit."""
    start = DEFS[name][0]
    end = start
    while end < len(SL) and (SL[end] == "" or SL[end][0].isspace()):
        end += 1
    while SL[end - 1].strip() == "":
        end -= 1
    if with_comment and start >= 2 and SL[start - 2].rstrip().endswith("*)"):
        s = start - 1
        while s > 1 and not SL[s - 1].lstrip().startswith("(*"):
            s -= 1
        start = s
    return start, end


def decl_block(keyword: str) -> list[tuple[str, int, str]]:
    """Names declared under CONSTANTS or VARIABLES: (name, line, trailing comment)."""
    i = next(n for n, l in enumerate(SL) if l.strip() == keyword)
    out, j = [], i + 1
    while SL[j].strip():
        m = re.match(r"\s+(\w+),?\s*(?:\\\*\s*(.*))?$", SL[j])
        out.append((m.group(1), j + 1, m.group(2) or ""))
        j += 1
    return out


def line_of(pattern: str, lo: int = 1, hi: int | None = None, lines=None) -> int:
    lines = SL if lines is None else lines
    for n in range(lo, (hi or len(lines)) + 1):
        if re.search(pattern, lines[n - 1]):
            return n
    raise KeyError(pattern)


CONSTS = decl_block("CONSTANTS")
VARDECL = decl_block("VARIABLES")
VARS = [v for v, _, _ in VARDECL]
VLINE = {v: n for v, n, _ in VARDECL}
_ns, _ne = def_span("Next", False)
ACTIONS = []
for _l in SL[_ns - 1:_ne]:
    for _m in re.finditer(r"\b(\w+)\(", _l):
        if _m.group(1) in DEFS and _m.group(1) not in ACTIONS:
            ACTIONS.append(_m.group(1))


def conjuncts(name: str, pattern: str) -> dict[str, tuple[int, str]]:
    """Top-level conjuncts `/\\ var <op> expr` of a definition: var -> (line, text)."""
    s, e = def_span(name, False)
    out = {}
    for n in range(s, e + 1):
        m = re.match(r"^\s*/\\ (\w+) " + pattern + r" (.*)$", tla_code(SL[n - 1]))
        if m and m.group(1) in VARS:
            out[m.group(1)] = (n, tla_code(SL[n - 1]).strip()[3:].strip())
    return out


TYPEOK = conjuncts("TypeOK", r"\\in")
INIT = conjuncts("Init", "=")


class Action:
    def __init__(self, name: str):
        self.name = name
        self.line, self.params = DEFS[name]
        s, e = def_span(name, False)
        self.span = (s, e)
        self.guards: list[tuple[int, str]] = []
        self.primed: dict[str, list[int]] = {}
        self.unchanged: list[str] = []
        self.unchanged_line = 0
        for n in range(s + 1, e + 1):
            code = tla_code(SL[n - 1])
            m = re.match(r"^ {4}/\\ (.*)$", code)
            if m:
                t = m.group(1).strip()
                if not (t.startswith("LET") or t.startswith("UNCHANGED") or "'" in t):
                    self.guards.append((n, t))
            for m in re.finditer(r"\b(\w+)'", code):
                if m.group(1) in VARS:
                    self.primed.setdefault(m.group(1), []).append(n)
            m = re.search(r"UNCHANGED\s*<<([^>]*)>>", code)
            if m:
                self.unchanged = [v.strip() for v in m.group(1).split(",")]
                self.unchanged_line = n


ACT = {a: Action(a) for a in ACTIONS}


# ---------------------------------------------------------------------------------------------
# the C++ file
# ---------------------------------------------------------------------------------------------
def cpp_code(l: str) -> str:
    return l.split("//")[0]


def brace_span(start: int) -> tuple[int, int] | None:
    """From line `start`, the line where the first '{' opened there is closed; None for a declaration."""
    depth, seen = 0, False
    for n in range(start, len(CL) + 1):
        code = cpp_code(CL[n - 1])
        for ch in code:
            if ch == "{":
                depth, seen = depth + 1, True
            elif ch == "}":
                depth -= 1
            elif ch == ";" and not seen:
                return None
        if seen and depth == 0:
            return start, n
    return None


CLASSES: dict[str, tuple[int, int]] = {}
for _n, _l in enumerate(CL, 1):
    _m = re.match(r"^(?:class|struct)\s+(\w+)\s*\{", _l)
    if _m:
        CLASSES[_m.group(1)] = brace_span(_n)


class Method:
    def __init__(self, cls: str, name: str, start: int, end: int, params: list[str]):
        self.cls, self.name, self.start, self.end, self.params = cls, name, start, end, params
        self.doc = start
        while self.doc > 1 and CL[self.doc - 2].lstrip().startswith("//"):
            self.doc -= 1
        self.qual = f"{cls}::{name}" if cls else name


METHODS: list[Method] = []


def _find_methods(cls: str, lo: int, hi: int, indent: int):
    n = lo
    while n <= hi:
        l = CL[n - 1]
        m = re.match(rf"^ {{{indent}}}(?:[\w:<>&*,]+\s+)*?[&*]?(\w+)\(([^)]*)\)", l)
        if m and not l.lstrip().startswith("//") and m.group(1) not in ("if", "for", "while", "return"):
            sp = brace_span(n)
            if sp:
                params = [re.findall(r"\w+", p)[-1] for p in m.group(2).split(",") if p.strip()]
                METHODS.append(Method(cls, m.group(1), sp[0], sp[1], params))
                n = sp[1] + 1
                continue
        n += 1


for _c, (_s, _e) in CLASSES.items():
    _find_methods(_c, _s + 1, _e - 1, 4)
_in_class = lambda n: any(s <= n <= e for s, e in CLASSES.values())  # noqa: E731
_n = 1
while _n <= len(CL):
    if not _in_class(_n) and re.match(r"^(?:static\s+)?[\w:<>]+\s+\w+\(", CL[_n - 1]):
        _sp = brace_span(_n)
        if _sp:
            _m = re.match(r"^(?:[\w:<>&*,]+\s+)*?(\w+)\(([^)]*)\)", CL[_n - 1])
            METHODS.append(Method("", _m.group(1), _sp[0], _sp[1],
                                  [re.findall(r"\w+", p)[-1] for p in _m.group(2).split(",") if p.strip()]))
            _n = _sp[1]
    _n += 1


def method(qual: str) -> Method:
    return next(m for m in METHODS if m.qual == qual)


def enclosing(line: int) -> Method | None:
    return next((m for m in METHODS if m.start <= line <= m.end), None)


def next_code_line(line: int) -> int:
    n = line + 1
    while CL[n - 1].lstrip().startswith("//") or not CL[n - 1].strip():
        n += 1
    return n


# fields of class System: every declaration outside a method
class Field:
    def __init__(self, name: str, ctype: str, line: int, static: bool):
        self.name, self.ctype, self.line, self.static = name, ctype, line, static
        self.anns: list[Ann] = []


FIELDS: list[Field] = []
_ss, _se = CLASSES["System"]
for _n in range(_ss + 1, _se):
    if enclosing(_n):
        continue
    _m = re.match(r"^ {4}(static\s+const(?:expr)?\s+)?([\w:<>, ]+?)\s+(\w+)(?:\s*=\s*[^;]+)?;", CL[_n - 1])
    if _m:
        FIELDS.append(Field(_m.group(3), _m.group(2), _n, bool(_m.group(1))))
for _a in CANNS:
    if _a.kind in ("TLA_VAR", "TLA_CONST", "TLA_EXCLUDED", "TLA_HISTORY", "TLA_CHANNEL"):
        _t = next_code_line(_a.line)
        for _f in FIELDS:
            if _f.line == _t:
                _f.anns.append(_a)


def field_ann(f: Field, kind: str) -> Ann | None:
    return next((a for a in f.anns if a.kind == kind), None)


VAR_FIELD = {field_ann(f, "TLA_VAR")["name"]: f for f in FIELDS if field_ann(f, "TLA_VAR")}   # spec variable -> field
FIELD_VAR = {f.name: v for v, f in VAR_FIELD.items()}
CONST_FIELD = {field_ann(f, "TLA_CONST")["name"]: f for f in FIELDS if field_ann(f, "TLA_CONST")}

# which fields a method writes, directly or through the System methods it calls
_F = "|".join(re.escape(f) for f in FIELD_VAR) or "$^"
_WRITE = [re.compile(rf"\b({_F})\b(?:\[[^\]]*\])*\s*(?:\+=|-=|=(?!=))"),
          re.compile(rf"(?:\+\+|--)\s*({_F})\b"),
          re.compile(rf"\b({_F})\b(?:\[[^\]]*\])*\.(?:insert|push_back|push_front|pop_back|pop_front|erase|clear|emplace\w*)\(")]
_SYS = {m.name: m for m in METHODS if m.cls == "System"}
_memo: dict[str, dict[str, list[tuple[int, str]]]] = {}


def writes(m: Method) -> dict[str, list[tuple[int, str]]]:
    """spec variable -> [(line, helper or '')] for the fields written in the method."""
    if m.qual in _memo:
        return _memo[m.qual]
    out: dict[str, list[tuple[int, str]]] = {}
    _memo[m.qual] = out
    for n in range(m.start + 1, m.end + 1):
        code = cpp_code(CL[n - 1])
        for rx in _WRITE:
            for hit in rx.finditer(code):
                e = out.setdefault(FIELD_VAR[hit.group(1)], [])
                if (n, "") not in e:
                    e.append((n, ""))
        for call in re.finditer(r"\b(\w+)\(", code):
            h = _SYS.get(call.group(1))
            if h and h is not m:
                for v in writes(h):
                    e = out.setdefault(v, [])
                    if (n, h.name) not in e:
                        e.append((n, h.name))
    return out


# the code site of every action: the @TLA_ACTION_LOCKED annotation and the method around it
class Site:
    def __init__(self, a: Ann):
        self.ann, self.m = a, enclosing(a.line)
        self.lock_line = next_code_line(a.line)
        lo, hi = self.m.start, self.m.end
        self.guards = [g for g in canns("TLA_GUARD") if lo <= g.line <= hi]
        self.unchanged = [u for u in canns("TLA_UNCHANGED") if lo <= u.line <= hi]


def guard_code(g: Ann) -> int:
    """The line of the statement a guard annotation is about: its own line, or the next statement."""
    return g.line if cpp_code(CL[g.line - 1]).strip() else next_code_line(g.line)


SITE = {a["name"]: Site(a) for a in canns("TLA_ACTION_LOCKED") if enclosing(a.line)}

# ---------------------------------------------------------------------------------------------
# checks: every computed verdict is recorded, the summary is printed at the end
# ---------------------------------------------------------------------------------------------
CHECKS: list[tuple[str, bool, str]] = []
CURRENT = "overview"


def ok(flag: bool, yes: str, no: str = "") -> str:
    CHECKS.append((CURRENT, bool(flag), yes if flag else (no or yes)))
    return f'<span class="ok">✓ {html.escape(yes)}</span>' if flag else f'<span class="bad">✗ {html.escape(no or yes)}</span>'


def note(text: str) -> str:
    """An explanation written by hand: not a check, so it carries no ✓.  `text` is HTML."""
    return f'<span class="note">· {text}</span>'


# ---------------------------------------------------------------------------------------------
# TLA+ -> Unicode, highlighting
# ---------------------------------------------------------------------------------------------
_SYM = [
    (r"<=>", "⇔"), (r"\|->", "↦"), (r"<<", "⟨"), (r">>", "⟩"), (r"~>", "⇝"), (r"=>", "⇒"),
    (r"->", "→"), (r"<-", "←"), (r"/\\", "∧"), (r"\\/", "∨"), (r"<=", "≤"), (r">=", "≥"),
    (r"/=", "≠"), (r"==", "≜"), (r"\[\]", "□"), (r"<>", "◇"),
    (r"\\A\b", "∀"), (r"\\E\b", "∃"), (r"\\in\b", "∈"), (r"\\notin\b", "∉"),
    (r"\\subseteq\b", "⊆"), (r"\\cup\b", "∪"), (r"\\cap\b", "∩"), (r"\\X\b", "×"),
    (r"#", "≠"), (r"~", "¬"), (r"\\(?=\s|\{)", "∖"), (r"'", "′"),
]
_SYM_RE = re.compile("|".join(f"({p})" for p, _ in _SYM))
_SYM_OUT = [s for _, s in _SYM]


def tla_unicode(line: str, state: dict | None = None) -> str:
    """ASCII TLA+ -> Unicode symbols, in formulas only: strings and comments stay as written.
    state['c'] carries a (* comment left open by an earlier line."""
    state = state if state is not None else {"c": False}

    def conv(seg: str, at_start: bool) -> str:
        if at_start:
            seg = re.sub(r"^(\s*)/\\ ", r"\1∧  ", seg)
            seg = re.sub(r"^(\s*)\\/ ", r"\1∨  ", seg)
        return _SYM_RE.sub(lambda m: _SYM_OUT[m.lastindex - 1], seg)

    tok = re.compile(r'\(\*|\\\*|"[^"]*"|`[^`]*`')
    out, i = [], 0
    while i < len(line):
        if state["c"]:
            j = line.find("*)", i)
            if j < 0:
                out.append(line[i:])
                return "".join(out)
            out.append(line[i:j + 2])
            i, state["c"] = j + 2, False
            continue
        m = tok.search(line, i)
        if not m:
            break
        out.append(conv(line[i:m.start()], i == 0))
        if m.group(0) == "(*":
            out.append("(*")
            i, state["c"] = m.end(), True
        elif m.group(0) == "\\*":
            out.append(line[m.start():])
            return "".join(out)
        else:
            out.append(m.group(0))
            i = m.end()
    out.append(conv(line[i:], i == 0))
    return "".join(out)


PALETTE = ["#c2410c", "#1d4ed8", "#047857", "#7e22ce", "#be123c", "#0f766e", "#854d0e"]
COLOR = {v: PALETTE[i % len(PALETTE)] for i, v in enumerate(VARS)}
TLA_KW = {"IF", "THEN", "ELSE", "LET", "IN", "EXCEPT", "UNCHANGED", "CHOOSE", "SUBSET", "UNION",
          "CONSTANTS", "CONSTANT", "VARIABLES", "VARIABLE", "EXTENDS", "ASSUME", "THEOREM", "MODULE",
          "TRUE", "FALSE", "DOMAIN", "ENABLED", "SPECIFICATION", "INVARIANTS", "PROPERTIES", "CHECK_DEADLOCK"}
CPP_KW = {"void", "int", "bool", "for", "if", "else", "return", "const", "static", "class", "struct",
          "public", "private", "auto", "true", "false", "unsigned", "noexcept", "this", "nullptr", "assert", "continue"}


def _span(cls: str, text: str, style: str = "") -> str:
    st = f' style="{style}"' if style else ""
    return f'<span class="{cls}"{st}>{html.escape(text)}</span>'


def _v(name: str, shown: str | None = None) -> str:
    return _span("v", shown or name, f"color:{COLOR[name]}")


def hl_comment(text: str) -> str:
    """A comment: grey italic, except the annotations in it, which keep the look of code."""
    out, i = [], 0
    for m in re.finditer(r"@TLA_[A-Z_]+", text):
        if m.start() < i:
            continue
        end = match_brace(text, m.end()) if text[m.end():m.end() + 1] == "{" else -1
        out.append(f'<span class="c">{html.escape(text[i:m.start()])}</span>' if text[i:m.start()] else "")
        out.append(_span("ann", m.group(0)))
        if end > 0:
            body = html.escape(text[m.end():end + 1])

            def name(q: re.Match) -> str:
                w = q.group(2)
                inner = _v(w) if w in COLOR else _span("act", w) if w in ACT else html.escape(w)
                return q.group(1) + inner + q.group(1)
            body = re.sub(r"(&quot;)(\w+)\1", name, body)
            out.append(f'<span class="annb">{body}</span>')
            i = end + 1
        else:
            i = m.end()
    if text[i:]:
        out.append(f'<span class="c">{html.escape(text[i:])}</span>')
    return "".join(out)


def hl_tla(line: str, state: dict) -> str:
    """Highlight one (already Unicode) TLA+ line; state['c'] tracks an open (* comment."""
    out, i = [], 0
    tok = re.compile(r'\(\*|\\\*.*$|"[^"]*"|\b[A-Za-z_]\w*\b|\d+|.', re.S)
    while i < len(line):
        if state["c"]:
            j = line.find("*)", i)
            seg = line[i:] if j < 0 else line[i:j + 2]
            out.append(hl_comment(seg))
            if j < 0:
                return "".join(out)
            i, state["c"] = j + 2, False
            continue
        m = tok.match(line, i)
        t = m.group(0)
        i = m.end()
        if t == "(*":
            state["c"] = True
            i -= 2
        elif t.startswith("\\*"):
            out.append(hl_comment(t))
        elif t.startswith('"'):
            out.append(_span("s", t))
        elif t in TLA_KW:
            out.append(_span("k", t))
        elif t in COLOR:
            out.append(_v(t))
        elif t in ACT:
            out.append(_span("act", t))
        else:
            out.append(html.escape(t))
    return "".join(out)


def hl_cpp(line: str) -> str:
    code, sep, comment = line.partition("//")
    out = []
    tok = re.compile(r'"(?:[^"\\]|\\.)*"|\b[A-Za-z_]\w*\b|\d+|.', re.S)
    for m in tok.finditer(code):
        t = m.group(0)
        if t.startswith('"'):
            out.append(_span("s", t))
        elif t in FIELD_VAR:
            out.append(_v(FIELD_VAR[t], t))
        elif t in CPP_KW:
            out.append(_span("k", t))
        else:
            out.append(html.escape(t))
    if sep:
        out.append(hl_comment(sep + comment))
    return "".join(out)


def pre_lines(lines: list[str], start: int, end: int, lang: str) -> str:
    st, ust, rows = {"c": False}, {"c": False}, []
    for n in range(start, end + 1):
        body = hl_cpp(lines[n - 1]) if lang == "cpp" else hl_tla(tla_unicode(lines[n - 1], ust), st)
        rows.append(f'<div class="l"><span class="ln">{n}</span>{body}</div>')
    return "<pre>" + "".join(rows) + "</pre>"


# ---------------------------------------------------------------------------------------------
# HTML pieces
# ---------------------------------------------------------------------------------------------
REL_CPP = f"cpp/{CPP.name}"
REL_SPEC = f"spec/{SPEC.name}"


def _where(spans) -> str:
    return ", ".join(f"{a}–{b}" if a != b else str(a) for a, b in spans)


def card(title: str, where: str, body: str) -> str:
    return f'<div class="card"><h3>{html.escape(title)}<span class="where">{html.escape(where)}</span></h3>{body}</div>'


def frag_cpp(title: str, spans: list[tuple[int, int]]) -> str:
    body = '<div class="gap"></div>'.join(pre_lines(CL, a, b, "cpp") for a, b in spans)
    return card(title, f"{REL_CPP} {_where(spans)}", body)


def frag_tla(title: str, spans: list[tuple[int, int]]) -> str:
    body = '<div class="gap"></div>'.join(pre_lines(SL, a, b, "tla") for a, b in spans)
    return card(title, f"{REL_SPEC} {_where(spans)}", body)


def frag_trace(title: str, spans: list[tuple[int, int]]) -> str:
    body = '<div class="gap"></div>'.join(pre_lines(TL, a, b, "tla") for a, b in spans)
    return card(title, f"{TS_REL} {_where(spans)}", body)


def tl_line(pattern: str, lo: int = 1) -> int:
    return line_of(pattern, lo, len(TL), TL)


def tl_def(name: str) -> tuple[int, int]:
    """Lines of a definition of the trace spec, with the comment block above it."""
    start = tl_line(rf"^{name}(\(|\s*==)")
    end = start
    while end < len(TL) and (TL[end] == "" or TL[end][0].isspace()):
        end += 1
    while TL[end - 1].strip() == "":
        end -= 1
    if start >= 2 and TL[start - 2].rstrip().endswith("*)"):
        s = start - 1
        while s > 1 and not TL[s - 1].lstrip().startswith("(*"):
            s -= 1
        start = s
    return start, end


def frag_file(title: str, path: Path) -> str:
    lines = path.read_text().rstrip("\n").split("\n")
    return card(title, f"spec/{path.name}", pre_lines(lines, 1, len(lines), "tla"))


def tla(s: str) -> str:
    return f"<code>{hl_tla(tla_unicode(s), {'c': False})}</code>"


def cpp(s: str) -> str:
    return f"<code>{hl_cpp(s)}</code>"


def code(s: str) -> str:
    return f"<code>{html.escape(s)}</code>"


def ann(a: Ann | None) -> str:
    return f"<code>{hl_comment(a.text)}</code>" if a else "<i>no annotation</i>"


def vlist(names) -> str:
    return ", ".join(_v(v) for v in names) or "—"


def at(n: int) -> str:
    return f'<span class="at">line {n}</span>'


def sync_table(rows: list[tuple],
               heads: tuple[str, str, str] = ("TLA⁺ specification", "C++ and its annotations", "in sync?")) -> str:
    out = [f'<table class="sync"><thead><tr><th style="width:10%"></th><th style="width:33%">{heads[0]}</th>'
           f'<th style="width:35%">{heads[1]}</th><th>{heads[2]}</th></tr></thead>']
    for a, b, c, d in rows:
        if c is None:      # a remark that spans the three columns
            out.append(f'<tr><td class="lbl">{a}</td><td colspan="3">{b}</td></tr>')
        else:
            out.append(f'<tr><td class="lbl">{a}</td><td>{b}</td><td>{c}</td><td>{d}</td></tr>')
    return "".join(out) + "</table>"


VIEWS: list[str] = []
TOC: list[tuple[str, str, str]] = []


def begin(title: str):
    global CURRENT
    CURRENT = title


def add(vid: str, title: str, subtitle: str, left: str, right: str, below: str = ""):
    TOC.append((vid, title, subtitle))
    VIEWS.append(f'<section class="view" id="{vid}"><h1>{html.escape(title)}<a class="up" href="#top">↑ views</a></h1>'
                 f'<div class="sub">{subtitle}</div><div class="cols"><div>{left}</div><div>{right}</div></div>{below}</section>')


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def br(*items: str) -> str:
    return "<br>".join(i for i in items if i)


# ---------------------------------------------------------------------------------------------
# view: module and constants
# ---------------------------------------------------------------------------------------------
begin("Module and constants")
mod = canns("TLA_MODULE")
mod_line = line_of(r"MODULE\s+\w+")
mod_name = re.search(r"MODULE\s+(\w+)", SL[mod_line - 1]).group(1)
main = method("main")
ctor = method("System::System")
sys_line = line_of(r"\bSystem\s+\w+\(", main.start, main.end, CL)
rows = [("module", tla(f"---- MODULE {mod_name} ----") + " " + at(mod_line),
         br(*(ann(a) + " " + at(a.line) for a in mod)) or "<i>no @TLA_MODULE</i>",
         br(ok(len(mod) == 1 and mod[0]["name"] == mod_name, "the file names the module it implements",
               "@TLA_MODULE is missing or names another module"),
            ok(bool(mod) and (CPP.parent / mod[0]["file"]).resolve() == SPEC, "the path leads to the spec",
               "the file: path does not lead to the spec")))]
for cname, cline, ccomment in CONSTS:
    f = CONST_FIELD.get(cname)
    impl = next((a for a in sanns("TLA_IMPL") if a.line == cline), None)
    rows.append((f"constant {cname}", tla(SL[cline - 1].strip()) + " " + at(cline),
                 (ann(field_ann(f, "TLA_CONST")) + "<br>" + cpp(CL[f.line - 1].strip()) + " " + at(f.line)) if f else "<i>no @TLA_CONST</i>",
                 br(ok(f is not None, "bound to one field", f"no field is annotated @TLA_CONST for {cname}"),
                    ok(bool(impl) and f is not None and impl["symbol"] == f.name,
                       f"the spec points back at the same field ({impl['symbol'] if impl else '?'})",
                       "@TLA_IMPL in the spec names another symbol") if impl else "")))
for name in ("P0", "T0"):
    if name in DEFS:
        sv = re.search(r"==\s*(\S+)", SL[DEFS[name][0] - 1]).group(1)
        cl = next((n for n in range(_ss, _se) if re.search(rf"static const(?:expr)? int {name} = ", CL[n - 1])), 0)
        cv = re.search(rf"{name} = (\w+);", CL[cl - 1]).group(1) if cl else "?"
        rows.append((name, tla(tla_code(SL[DEFS[name][0] - 1]).strip()) + " " + at(DEFS[name][0]),
                     (cpp(cpp_code(CL[cl - 1]).strip()) + " " + at(cl)) if cl else "—",
                     ok(sv == cv, f"same value ({sv})", f"{sv} in the spec, {cv} in the code")))
rows.append(("a run", "a behaviour of the spec with <code>N</code> and <code>MaxReq</code> fixed",
             cpp(cpp_code(CL[sys_line - 1]).strip()) + " " + at(sys_line),
             note("the run with arguments <code>3 2</code> is to be compared with the spec where N = 3 and MaxReq = 2; "
                  "the code accepts N from 1 to 5")))
field_lines = sorted(f.line for f in CONST_FIELD.values())
add("module", "Module and constants",
    "Which module the file implements, and the two constants that every model and every run must fix",
    frag_cpp("@TLA_MODULE, @TLA_CONST", [(a.line, a.line) for a in mod] + [(field_lines[0] - 1, field_lines[-1])]
             + [(main.start, sys_line)]),
    frag_tla("MODULE, CONSTANTS, @TLA_IMPL", [(mod_line, mod_line), (line_of(r"^EXTENDS"), DEFS["T0"][0])]),
    sync_table(rows))


# ---------------------------------------------------------------------------------------------
# view: variables
# ---------------------------------------------------------------------------------------------
begin("Variables")
rows = []
for v in VARS:
    f = VAR_FIELD.get(v)
    n_ann = len(canns("TLA_VAR", name=v))
    tok_line, tok = TYPEOK.get(v, (0, ""))
    a = field_ann(f, "TLA_VAR") if f else None
    left = _v(v) + " " + at(VLINE[v]) + "<br>" + (tla(tok) + " " + at(tok_line) if tok else "<i>no TypeOK conjunct</i>")
    right = (br(ann(a), *(ann(x) for x in f.anns if x.kind in ("TLA_HISTORY", "TLA_CHANNEL")))
             + "<br>" + cpp(CL[f.line - 1].strip()) + " " + at(f.line)
             ) if f else "<i>no field is annotated</i>"
    rows.append((f"variable {v}", left, right,
                 br(ok(n_ann == 1, "bound to one field", f"{n_ann} fields are annotated @TLA_VAR for {v}"),
                    ok(bool(tok) and a is not None and norm(a["type"]) == norm(tok.partition("\\in")[2]),
                       "the type is the set that TypeOK gives it",
                       f"the type differs from TypeOK: {a['type'] if a else '?'}" if tok else "no TypeOK conjunct"))))
for a in canns("TLA_VAR"):
    if a["name"] not in VARS:
        rows.append((f"variable {a['name']}", "—", ann(a) + " " + at(a.line), ok(False, "", "the spec has no such variable")))
for f in FIELDS:
    if f.static or field_ann(f, "TLA_VAR") or field_ann(f, "TLA_CONST"):
        continue
    ex = field_ann(f, "TLA_EXCLUDED")
    rows.append((f"field {f.name}", "— not in the spec",
                 (ann(ex) + "<br>" if ex else "") + cpp(CL[f.line - 1].strip()) + " " + at(f.line),
                 ok(ex is not None and bool(ex["reason"]), "excluded on purpose, with a reason",
                    "a field of System without annotation: is it a spec variable, or @TLA_EXCLUDED?")))
rows.append(("to notice", br(
    note("the type in the annotation is TLA⁺, not C++: it says which set the field's value must stay in, and it is the same text as the TypeOK conjunct"),
    note("<code>std::map</code> with the keys 1..n is a function on <code>Proc</code>; <code>std::set</code> is a set (<code>SUBSET</code>); "
         "<code>std::deque</code> is a sequence (<code>Seq</code>); <code>std::pair</code> is a tuple (<code>×</code>); <code>struct Msg</code> is a record"),
    note("the C++ type is wider than the set: <code>std::string pc_</code> could hold any text, <code>int</code> could be negative. "
         "That the fields stay inside the sets is what TypeOK states, and TLC checks it on the spec")), None, None))
first_f, last_f = min(f.line for f in FIELDS if not f.static and f.line > ctor.end + 40), max(f.line for f in FIELDS)
kinds_lo = DEFS["Kinds"][0]
add("variables", "Variables",
    "Every VARIABLE of the spec is one field of System; every other field is excluded on purpose. "
    "The type in the annotation is the set that TypeOK gives the variable",
    frag_cpp("@TLA_VAR, @TLA_EXCLUDED on the fields of System",
             [(f.line - 1, f.line) for f in FIELDS if not f.static and f.line < min(a.line for a in canns("TLA_CONST"))]
             + [(min(a.line for a in canns("TLA_CONST")), last_f)]),
    frag_tla("VARIABLES, TypeOK", [(line_of(r"^VARIABLES"), DEFS["vars"][0]), (kinds_lo, DEFS["Request_"][0]),
                                   def_span("TypeOK", False)]),
    sync_table(rows))

# ---------------------------------------------------------------------------------------------
# view: Init
# ---------------------------------------------------------------------------------------------
begin("Init")
inits = canns("TLA_INIT")
rows = [("initial state", tla("Init ==") + " " + at(DEFS["Init"][0]),
         br(*(ann(a) + " " + at(a.line) for a in inits)) + f"<br>on {code('System::System')}",
         ok(len(inits) == 1 and enclosing(next_code_line(inits[0].line)) is ctor, "one @TLA_INIT, on the constructor",
            "@TLA_INIT must be on the constructor, once"))]
for v in VARS:
    il, it = INIT.get(v, (0, ""))
    f = VAR_FIELD.get(v)
    hits = [n for n in range(ctor.start, ctor.end + 1) if f and re.search(rf"\b{f.name}\b", cpp_code(CL[n - 1]))]
    rows.append((_v(v), (tla(it) + " " + at(il)) if it else "<i>no conjunct in Init</i>",
                 br(*(cpp(cpp_code(CL[n - 1]).strip()) + " " + at(n) for n in hits)) or "<i>not assigned in the constructor</i>",
                 ok(bool(hits) and bool(it), "given its initial value here", "one side does not initialise it")))
run = method("Process::run")
p0 = line_of(r"hold_then_release\(\);", run.start, run.end, CL)
rows.append(("the loop", tla("[p \\in Proc |-> ...]"), cpp("for (int p = 1; p <= n; p++)"),
             note("the loop over 1..n builds the function that the spec writes in one expression")))
rows.append(("who holds first", tla('pc = [p \\in Proc |-> IF p = P0 THEN "held" ELSE "idle"]'),
             cpp(cpp_code(CL[p0 - 1]).strip()) + " " + at(p0),
             note("the state says P0 holds the resource, so the thread of P0 must start by using and releasing it: "
                  "P0 takes <code>Release</code> before its first <code>Request</code>")))
add("init", "Init ⟷ System::System",
    "Assumption A4 of the paper: P0 holds the resource, every queue contains T0:P0, the clocks are above T0",
    frag_cpp("@TLA_INIT on the constructor", [(ctor.doc, ctor.end), (run.start, p0)]),
    frag_tla("Init", [(DEFS["P0"][0], DEFS["T0"][0]), def_span("Init")]),
    sync_table(rows))

# ---------------------------------------------------------------------------------------------
# views: one per action
# ---------------------------------------------------------------------------------------------
RULE = {"Request": "Rule 1", "RecvRequest": "Rule 2", "RecvAck": "Acknowledgement", "Release": "Rule 3",
        "RecvRelease": "Rule 4", "Acquire": "Rule 5"}
SUB = {
    "Request": "P asks for the resource: it timestamps a request, queues it and sends it to every other process",
    "RecvRequest": "P receives a request from Q: it queues the request and answers with a timestamped acknowledgement",
    "RecvAck": "P receives an acknowledgement from Q: only its clock and what it last heard from Q change",
    "Release": "P gives the resource back: it removes its own request and tells every other process",
    "RecvRelease": "P learns that Q released: it removes the request of Q from its queue",
    "Acquire": "P takes the resource, when its request is first in its queue and it has heard from everyone since",
}
EXTRA_TLA = {"Request": ["Broadcast"], "RecvRequest": ["Max"], "RecvAck": ["Max"], "Release": ["Broadcast"],
             "RecvRelease": ["Max"], "Acquire": []}
ORDER = [a for a in ["Request", "RecvRequest", "RecvAck", "Release", "RecvRelease", "Acquire"] if a in ACT] + \
        [a for a in ACTIONS if a not in RULE]
HAND = {   # written by hand, one or two remarks per action
    "Request": [
        "<code>int t = ++clock_[p]</code> is <code>LET t ≜ clock[p] + 1</code> and <code>clock′[p] = t</code> in one statement (IR1); "
        "the same <code>t</code> stamps the queued request and the message (IR2(a))",
        "<code>cv_.notify_all()</code> runs after the step, outside the lock: it changes no spec variable"],
    "RecvRequest": [
        "<code>front()</code> then <code>pop_front()</code> are <code>Head</code> and <code>Tail</code> of <code>chan[q][p]</code>",
        "<code>chan</code> changes in two places on both sides: the request leaves <code>chan[q][p]</code>, the acknowledgement enters <code>chan[p][q]</code>",
        "<code>tick_on_receive</code> is <code>Max(clock[p], m.ts) + 1</code> (IR2(b)); its result is the timestamp of the acknowledgement"],
    "RecvAck": ["what this step leaves in <code>lastTs[p][q]</code> is what condition (ii) of rule 5 reads later"],
    "Release": ["<code>erase_requests_of(p, p)</code> is <code>{r ∈ @ : r[2] ≠ p}</code>: the request of p leaves its own queue",
                "the thread stops using the resource before this step (<code>Process::hold_then_release</code>)"],
    "RecvRelease": ["<code>erase_requests_of(p, q)</code> is <code>{r ∈ @ : r[2] ≠ q}</code>"],
    "Acquire": ["<code>lastGranted</code> is a history variable: no rule reads it, the property <code>GrantOrder</code> does",
                "the guard <code>CanAcquire(p)</code> is one definition in the spec and one function in the code: see the view on rule 5",
                "there is no inner block here: the step ends with the method"],
}


for name in ORDER:
    a = ACT[name]
    site = SITE.get(name)
    sig = f"{name}({', '.join(a.params)})"
    title = f"{RULE.get(name, 'Action')}: {sig} ⟷ " + (site.m.qual if site else "no code")
    begin(title)
    rows = []
    n_sites = len(canns("TLA_ACTION_LOCKED", name=name))
    if not site:
        rows.append(("action", tla(sig) + " " + at(a.line), "<i>no @TLA_ACTION_LOCKED names this action</i>",
                     ok(False, "", "the action has no code site")))
        add(f"a-{name}", title, SUB.get(name, ""), "", frag_tla(sig, [def_span(name)]), sync_table(rows))
        continue
    m = site.m
    ap_ = site.ann["params"] if isinstance(site.ann["params"], list) else []
    rows.append(("action", tla(sig) + " " + at(a.line), ann(site.ann) + " " + at(site.ann.line) + f"<br>in {code(m.qual)}",
                 br(ok(n_sites == 1, "bound to one step of the code", f"{n_sites} steps claim this action"),
                    ok(ap_ == a.params == m.params, f"same parameters ({', '.join(a.params)})",
                       f"parameters differ: spec ({', '.join(a.params)}), annotation ({', '.join(ap_)}), method ({', '.join(m.params)})"))))
    lock_code = cpp_code(CL[site.lock_line - 1]).strip()
    lock_ok = bool(re.search(rf"std::(?:lock_guard|unique_lock|scoped_lock)<[^>]*>\s+\w+\({re.escape(site.ann['lock'])}\)", lock_code))
    rows.append(("atomicity", "one step of <code>Next</code>: all the primed variables change together",
                 cpp(lock_code) + " " + at(site.lock_line),
                 br(ok(lock_ok, f"the step starts by taking {site.ann['lock']}, the lock the annotation names",
                       f"the statement after the annotation does not take {site.ann['lock']}"),
                    note("every other step takes the same lock, so no thread sees this one half done"))))
    # guards: the spec's enabling conjuncts against the @TLA_GUARD names
    cg = {norm(g["name"]): g for g in site.guards}
    for gl, gt in a.guards:
        g = cg.pop(norm(gt), None)
        rows.append(("guard", tla(gt) + " " + at(gl),
                     (ann(g) + "<br>" + cpp(cpp_code(CL[guard_code(g) - 1]).strip()) + " " + at(guard_code(g))) if g else "<i>no @TLA_GUARD with this name</i>",
                     ok(g is not None, "the guard is named by this conjunct", "no guard in the code carries this conjunct")))
    for g in cg.values():
        rows.append(("guard", "<i>no such enabling conjunct</i>", ann(g) + "<br>" + cpp(cpp_code(CL[guard_code(g) - 1]).strip()) + " " + at(guard_code(g)),
                     ok(False, "", "the guard names a conjunct that the action does not have")))
    # effects: one row per variable that either side changes
    w = writes(m)
    for v in VARS:
        if v not in a.primed and v not in w:
            continue
        sp = br(*(tla(tla_code(SL[n - 1]).strip().removeprefix("/\\ ")) + " " + at(n) for n in dict.fromkeys(a.primed.get(v, []))))
        cp = br(*(cpp(cpp_code(CL[n - 1]).strip()) + " " + at(n) + (f" <span class='at'>through {h}</span>" if h else "")
                  for n, h in w.get(v, [])))
        rows.append((_v(v, v + "′"), sp or "<i>not changed by the action</i>", cp or "<i>not written by the method</i>",
                     ok(v in a.primed and v in w, "changed on both sides",
                        f"the code writes {v}, the spec leaves it unchanged" if v in w else f"the spec changes {v}, the code does not write it")))
    un = [v for u in site.unchanged for v in (u["vars"] if isinstance(u["vars"], list) else [])]
    rows.append(("frame", (tla(tla_code(SL[a.unchanged_line - 1]).strip().removeprefix("/\\ ")) + " " + at(a.unchanged_line)) if a.unchanged else "<i>no UNCHANGED</i>",
                 br(*(ann(u) + " " + at(u.line) for u in site.unchanged)) or "<i>no @TLA_UNCHANGED</i>",
                 br(ok(sorted(un) == sorted(a.unchanged), "the same variables are left unchanged",
                       f"frames differ: spec ⟨{', '.join(a.unchanged)}⟩, code ⟨{', '.join(un)}⟩"),
                    ok(sorted(set(a.primed) | set(a.unchanged)) == sorted(VARS) and not set(a.primed) & set(a.unchanged),
                       f"changed ∪ unchanged = the {len(VARS)} variables",
                       "a variable is neither changed nor declared unchanged, or is both"),
                    ok(not set(un) & set(w), "no variable declared unchanged is written",
                       f"declared unchanged but written: {', '.join(sorted(set(un) & set(w)))}"))))
    if TL:
        rec = [n for n in range(m.start, m.end + 1) if re.search(r"\brecord\(", cpp_code(CL[n - 1]))]
        rm = re.search(r'record\("(\w+)"((?:,\s*\w+)*)\)', cpp_code(CL[rec[0] - 1])) if rec else None
        rargs = [x.strip() for x in rm.group(2).split(",") if x.strip()] if rm else []
        last_write = max((n for hits in w.values() for n, _ in hits), default=0)
        closes = bool(rec) and cpp_code(CL[next_code_line(rec[0]) - 1]).strip() == "}"
        ts = TSTEP.get(name)
        rows.append(("trace", (tla(ts[1]) + f" <span class='at'>{TS_REL} line {ts[0]}</span>") if ts else "<i>no disjunct of Step replays this action</i>",
                     (cpp(cpp_code(CL[rec[0] - 1]).strip()) + " " + at(rec[0])) if rec else "<i>the step is not recorded</i>",
                     br(ok(len(rec) == 1 and bool(rm) and rm.group(1) == name and rargs == a.params,
                           "recorded once, under the name of the action, with its parameters",
                           "the step must be recorded once, as record(\"" + name + "\", " + ", ".join(a.params) + ")"),
                        ok(bool(rec) and site.lock_line < rec[0] and rec[0] > last_write and closes,
                           "recorded as the last statement of the step: after every write, with the lock still held",
                           "the record must be the last statement of the atomic step"),
                        ok(bool(ts) and ts[2] == len(a.params), "the trace specification replays it as this action",
                           "the trace specification has no matching disjunct in Step"))))
    if HAND.get(name):
        rows.append(("to notice", br(*(note(h) for h in HAND[name])), None, None))
    spans = [def_span(name)] + [def_span(x) for x in EXTRA_TLA.get(name, []) if x in DEFS]
    add(f"a-{name}", title, SUB.get(name, ""), frag_cpp(f"@TLA_ACTION_LOCKED in {m.qual}", [(m.doc, m.end)]),
        frag_tla(sig, spans), sync_table(rows))

# ---------------------------------------------------------------------------------------------
# view: rule 5, its two conditions and the total order
# ---------------------------------------------------------------------------------------------
begin("Rule 5 conditions")
can, prec, myr, hasr = method("System::can_acquire"), method("precedes"), method("System::my_request"), method("System::has_request")
ca_s, ca_e = def_span("CanAcquire", False)
ci = line_of(r"Precedes\(MyRequest", ca_s, ca_e)
cii = line_of(r"lastTs\[p\]\[q\] >", ca_s, ca_e)
ki = line_of(r"// \(i\)", can.start, can.end, CL)
kii = line_of(r"// \(ii\)", can.start, can.end, CL)
rows = [
    ("order ⇒", tla(tla_code(SL[DEFS["Precedes"][0] - 1])) + " " + at(DEFS["Precedes"][0]),
     cpp("precedes(a, b)") + f" lines {prec.start}–{prec.end}",
     note("the same order: by timestamp, then by process number. Assumption A6 only asks for some fixed order of the processes; "
          "the two sides must pick the same one")),
    ("own request", tla(SL[DEFS["HasRequest"][0] - 1]) + "<br>" + tla(SL[DEFS["MyRequest"][0] - 1]),
     cpp("has_request(p)") + ", " + cpp("my_request(p)") + f" lines {hasr.start}–{myr.end}",
     note("<code>CHOOSE</code> picks an arbitrary request of p; the code returns the first it finds. "
          "They agree because a queue never holds two requests of one process: the invariant <code>OneRequestPerProcess</code>, checked by TLC")),
    ("condition (i)", tla(tla_code(SL[ci - 1]).strip().removeprefix("/\\ ")) + " " + at(ci),
     cpp(cpp_code(CL[ki - 2]).strip()) + "<br>" + cpp(cpp_code(CL[ki - 1]).strip()) + " " + at(ki),
     note("the spec states what holds for every request; the loop returns false at the first request for which it does not: "
          "<code>r ≠ mine ∧ ¬precedes(mine, r)</code> is the negation of the quantified formula")),
    ("condition (ii)", tla(tla_code(SL[cii - 1]).strip().removeprefix("/\\ ")) + " " + at(cii),
     cpp(cpp_code(CL[kii - 2]).strip()) + "<br>" + cpp(cpp_code(CL[kii - 1]).strip()) + " " + at(kii),
     note("again the negation: <code>≤</code> where the spec has <code>&gt;</code>, and <code>q != p</code> for <code>Proc ∖ {p}</code>")),
    ("local test", "<code>CanAcquire(p)</code> reads only " + vlist(["queue", "lastTs"]) + " at index p",
     cpp("can_acquire(p)") + " reads only " + cpp("queue_.at(p)") + " and " + cpp("last_ts_.at(p)"),
     ok(set(re.findall(rf"\b({_F})\b", " ".join(cpp_code(CL[n - 1]) for n in list(range(can.start, can.end + 1))
                                                    + list(range(myr.start, myr.end + 1)) + list(range(hasr.start, hasr.end + 1)))))
        == {VAR_FIELD["queue"].name, VAR_FIELD["lastTs"].name} if {"queue", "lastTs"} <= set(VAR_FIELD) else False,
        "the code reads the same two variables, nothing else", "the code reads other fields than queue_ and last_ts_")),
]
add("rule5", "Rule 5: conditions (i) and (ii), and the total order ⇒",
    "The guard of Acquire: a definition in the spec, a function in the code. Each process decides alone, from what it knows",
    frag_cpp("can_acquire, has_request, my_request, precedes", [(can.doc, can.end), (hasr.start, hasr.end), (myr.start, myr.end), (prec.doc, prec.end)]),
    frag_tla("Precedes, MyRequest, HasRequest, CanAcquire", [def_span("Precedes"), (DEFS["MyRequest"][0] - 1, DEFS["HasRequest"][0]), def_span("CanAcquire")]),
    sync_table(rows))

# ---------------------------------------------------------------------------------------------
# view: clocks, broadcast, channels
# ---------------------------------------------------------------------------------------------
begin("Clocks and channels")
tick, bc, er = method("System::tick_on_receive"), method("System::broadcast"), method("System::erase_requests_of")
msg_s, msg_e = CLASSES["Msg"]
msg_fields = [re.match(r"\s*[\w:]+\s+(\w+);", cpp_code(CL[n - 1])).group(1) for n in range(msg_s + 1, msg_e)
              if re.match(r"\s*[\w:]+\s+(\w+);", cpp_code(CL[n - 1]))]
spec_msg = re.findall(r"(\w+)\s*:", SL[DEFS["Msg"][0] - 1].split("==")[1])
chan_f = VAR_FIELD.get("chan")
chan_ann = field_ann(chan_f, "TLA_CHANNEL") if chan_f else None
all_tick = all("clock" in ACT[x].primed for x in ACTIONS)
all_tick_c = all(x in SITE and "clock" in writes(SITE[x].m) for x in ACTIONS)
rows = [
    ("IR1", "every action has a conjunct " + tla("clock' = [clock EXCEPT ![p] = ...]"),
     cpp("++clock_[p]") + ", " + cpp("clock_[p] += 1") + ", or " + cpp("tick_on_receive(p, m)"),
     br(ok(all_tick, f"clock changes in each of the {len(ACTIONS)} actions", "an action does not advance the clock"),
        ok(all_tick_c, "clock_ is written in each of the methods", "a method does not advance clock_"))),
    ("IR2(a)", tla('[kind |-> "req", ts |-> t, from |-> p]'), cpp('Msg{"req", t, p}'),
     ok(msg_fields == spec_msg, f"the message has the same fields, in the same order ({', '.join(spec_msg)})",
        f"fields differ: spec ({', '.join(spec_msg)}), struct ({', '.join(msg_fields)})")),
    ("IR2(b)", tla("Max(clock[p], m.ts) + 1"), cpp(cpp_code(CL[tick.start]).strip()) + " " + at(tick.start + 1),
     note("the conditional expression is <code>Max</code>, written out")),
    ("A3: send to all", tla(tla_code(SL[DEFS["Broadcast"][0]]).strip()) + " " + at(DEFS["Broadcast"][0] + 1),
     cpp(cpp_code(CL[bc.start]).strip()) + "<br>" + cpp(cpp_code(CL[bc.start + 1]).strip()) + " " + at(bc.start + 2),
     note("the spec builds the new row <code>chan[p]</code> as one function; the loop appends to each queue in turn. "
          "Inside one atomic step the two are the same change")),
    ("A1: FIFO", tla("Head(chan[q][p])") + ", " + tla("Tail(@)") + ", " + tla("Append(@, m)"),
     cpp("chan_[q][p].front()") + ", " + cpp(".pop_front()") + ", " + cpp(".push_back(m)") + "<br>" + ann(chan_ann),
     br(ok(chan_ann is not None and chan_ann["kind"] == "fifo" and "deque" in (chan_f.ctype if chan_f else ""),
           "the channel is declared FIFO and is a queue per pair", "the channel field is not declared as a FIFO queue"),
        note("only the thread of p removes from <code>chan[q][p]</code>, so the head that it has seen is still the head when it takes the step"))),
    ("no loss (A2)", "a message leaves a channel only in a receive action", "a message leaves a queue only in " + cpp("recv_request") + ", " + cpp("recv_ack") + ", " + cpp("recv_release"),
     ok(all("pop_front" not in cpp_code(CL[n - 1]) or (enclosing(n) and enclosing(n).name.startswith("recv_")) for n in range(1, len(CL) + 1)),
        "pop_front appears only in the three receive methods", "a message is removed outside a receive method")),
]
add("clocks", "Clocks (IR1, IR2), broadcast (A3) and FIFO channels (A1)",
    "The helpers that every rule uses: operators in the spec, small functions in the code",
    frag_cpp("Msg, tick_on_receive, broadcast, erase_requests_of", [(msg_s - 2, msg_e), (tick.doc, er.end)]
             + ([(chan_ann.line, chan_f.line)] if chan_ann else [])),
    frag_tla("Msg, Max, Broadcast", [(DEFS["Kinds"][0], DEFS["Request_"][0]), def_span("Max"), def_span("Broadcast")]),
    sync_table(rows))

# ---------------------------------------------------------------------------------------------
# view: Next, processes, fairness
# ---------------------------------------------------------------------------------------------
begin("Next and fairness")
P = CLASSES["Process"]
rows = []
for name in ORDER:
    site = SITE.get(name)
    calls = [n for n in range(P[0], P[1] + 1) if site and re.search(rf"\bsys_\.{site.m.name}\(", cpp_code(CL[n - 1]))]
    rows.append((f"disjunct {name}", tla(f"{name}({', '.join(ACT[name].params)})") + " in " + tla("Next"),
                 br(*(cpp(cpp_code(CL[n - 1]).strip()) + f" <span class='at'>line {n}, in {enclosing(n).qual}</span>" for n in calls))
                 or "<i>never called by a thread</i>",
                 ok(bool(calls), "a thread takes this step", "no thread ever takes this step")))
fs, fe = def_span("FairSpec", False)
wf = sorted(set(re.findall(r"WF_vars\((\w+)\(", " ".join(SL[fs - 1:fe]))))
wfa = canns("TLA_WEAK_FAIRNESS")
proc = canns("TLA_PROCESS")
spawn = line_of(r"emplace_back\(sys", main.start, main.end, CL)
rows += [
    ("∃ p ∈ Proc", tla("\\E p \\in Proc : ..."), br(*(ann(a) + " " + at(a.line) for a in proc), cpp(cpp_code(CL[spawn - 1]).strip()) + " " + at(spawn)),
     br(ok(len(proc) == 1 and proc[0]["set"] == "Proc", "one thread for each element of Proc", "@TLA_PROCESS is missing or names another set"),
        note("which disjunct runs next is chosen by the scheduler and by the random delays: every run is one path of the spec"))),
    ("fairness", tla("WF_vars(...)") + " on " + ", ".join(code(x) for x in wf) + f" <span class='at'>lines {fs}–{fe}</span>",
     br(*(ann(a) for a in wfa)) + f" <span class='at'>lines {min(a.line for a in wfa)}–{max(a.line for a in wfa)}</span>" if wfa else "<i>none</i>",
     br(ok(sorted(a["action"] for a in wfa) == wf, "the same actions are declared fair", "the fair actions differ"),
        note("the annotation records the claim and the argument for it (the text after it in the code); "
             "nothing checks that argument: it is the developer's reasoning about the threads"))),
    ("no fairness", tla("Request(p)") + " is not in <code>FairSpec</code>",
     cpp("for (int round = 1; round <= rounds_; round++)"),
     note("a process is never obliged to ask. The code asks <code>ROUNDS</code> times; <code>reqs[p] &lt; MaxReq</code> is the same bound in the spec")),
    ("stuttering", tla("[][Next]_vars") + ": a step may leave every variable unchanged",
     "waiting on <code>cv_</code>, <code>finished += 1</code>, the log, the <code>Resource</code> counters",
     note("everything the program does outside the six annotated steps changes only excluded state: for the spec, nothing happened")),
]
sud = method("Process::dispatch")
add("next", "Next, processes and fairness",
    "Which thread takes which step, and why every enabled step is eventually taken",
    frag_cpp("@TLA_WEAK_FAIRNESS, @TLA_PROCESS, the loop of one process",
             ([(min(a.line for a in wfa), max(a.line for a in wfa))] if wfa else []) + [(run.doc, run.end), (sud.doc, sud.end)]),
    frag_tla("Next, Spec, FairSpec", [def_span("Next"), def_span("Spec", False), def_span("FairSpec")]),
    sync_table(rows))


# ---------------------------------------------------------------------------------------------
# models (needed by the properties view too)
# ---------------------------------------------------------------------------------------------
def read_cfg(p: Path) -> dict:
    out = {"constants": {}, "spec": "", "invariants": [], "properties": [], "deadlock": ""}
    sect = ""
    for l in p.read_text().split("\n"):
        l = l.split("\\*")[0].rstrip()
        if not l.strip():
            continue
        m = re.match(r"^(CONSTANTS?|SPECIFICATION|INVARIANTS?|PROPERTIES|PROPERTY|CHECK_DEADLOCK)\b\s*(.*)$", l)
        rest = m.group(2) if m else l.strip()
        sect = m.group(1) if m else sect
        if sect.startswith("CONSTANT"):
            for k, v in re.findall(r"(\w+)\s*=\s*(\S+)", rest):
                out["constants"][k] = v
        elif sect == "SPECIFICATION" and rest:
            out["spec"] = rest.strip()
        elif sect.startswith("INVARIANT"):
            out["invariants"] += rest.split()
        elif sect.startswith("PROPERT"):
            out["properties"] += rest.split()
        elif sect == "CHECK_DEADLOCK" and rest:
            out["deadlock"] = rest.strip()
    return out


def for_model(kind: str, model: str) -> list[Ann]:
    return [a for a in sanns(kind) if a["model"] in ("", model)]


MODELS = {a["name"]: a for a in sanns("TLA_MODEL")}
CFG = {m: read_cfg(SPEC.parent / f"MC_{m}.cfg") for m in MODELS if (SPEC.parent / f"MC_{m}.cfg").exists()}

# ---------------------------------------------------------------------------------------------
# view: properties and the oracle
# ---------------------------------------------------------------------------------------------
begin("Properties")
PROPS = []
for c in CFG.values():
    for x in c["invariants"] + c["properties"]:
        if x not in PROPS:
            PROPS.append(x)
PAPER = {"Mutex": "condition I", "GrantOrder": "condition II", "EveryRequestGranted": "condition III",
         "OneRequestPerProcess": "a consequence of A1 (FIFO)", "ChannelTimestampsIncrease": "the Clock Condition, on the wire",
         "HolderHasRequest": "rule 3 is the only way out of the queue", "TypeOK": "the types of the variables"}
rows = []
for x in PROPS:
    inv = canns("TLA_INVARIANT", name=x)
    where = [m for m, c in CFG.items() if x in c["invariants"] + c["properties"]]
    kind = "invariant" if any(x in c["invariants"] for c in CFG.values()) else \
        "liveness" if "~>" in SL[DEFS[x][0] - 1] else "action property"
    rows.append((x, f"{kind}, {PAPER.get(x, '')} " + at(DEFS[x][0]) + "<br>checked by TLC in " + ", ".join(code(m) for m in where),
                 br(*(ann(a) + " " + at(a.line) + "<br>" + cpp(cpp_code(CL[next_code_line(a.line) - 1]).strip()) for a in inv))
                 or "— not evaluated by the code",
                 ok(True, "also evaluated by the running code, at every grant") if inv else
                 note("only the model checker checks it: on every reachable state of the model, not on the states of one run")))
res = CLASSES["Resource"]
ent = method("Resource::enter")
rows.append(("the oracle", "— not in the spec", cpp(cpp_code(CL[ent.start]).strip()) + " " + at(ent.start + 1),
             note("<code>Resource</code> counts the threads that use the resource at the same time. It does not read <code>pc_</code>: "
                  "it would report a violation even if the algorithm's own state were wrong. The exit status is 1 if either check fails")))
acq = SITE["Acquire"].m if "Acquire" in SITE else None
inv_lines = [a.line for a in canns("TLA_INVARIANT")]
add("properties", "Properties and the oracle",
    "What must always hold, who checks it, and on which states",
    frag_cpp("@TLA_INVARIANT, the Resource oracle", ([(min(inv_lines) - 2, min(inv_lines) + 4)] if inv_lines else []) + [(res[0] - 2, res[1])]
             + [(line_of(r"bool ok = ", main.start, main.end, CL), main.end - 1)]),
    frag_tla("the properties", [(DEFS["OneRequestPerProcess"][0] - 2, line_of(r"^THEOREM"))]),
    sync_table(rows, ("TLA⁺ specification", "C++ and its annotations", "who checks it")))

# ---------------------------------------------------------------------------------------------
# view: models
# ---------------------------------------------------------------------------------------------
begin("Models")
rows = []
for mname, ma in MODELS.items():
    c = CFG.get(mname)
    if not c:
        rows.append((f"model {mname}", ann(ma), f"<i>no spec/MC_{mname}.cfg</i>", ok(False, "", "the model has no configuration file"), ""))
        continue
    consts = {a["name"]: a["value"] for a in sanns("TLA_CONST_BIND", model=mname)}
    invs = [a["name"] for a in for_model("TLA_TYPE_OK", mname) + for_model("TLA_INVARIANT", mname)]
    props = [a["name"] for a in for_model("TLA_ACTION_PROPERTY", mname) + for_model("TLA_LEADS_TO", mname)]
    dl = (sanns("TLA_CHECK_DEADLOCK") or [None])[0]
    rows.append((f"model {mname}",
                 ", ".join(f"{k} = {v}" for k, v in consts.items()) + f"<br><code>{ma['specification']}</code><br>"
                 + ", ".join(invs) + "<br>" + ", ".join(props),
                 code(f"spec/MC_{mname}.cfg") + "<br>" + ", ".join(f"{k} = {v}" for k, v in c["constants"].items())
                 + f"<br><code>{c['spec']}</code>",
                 br(ok(consts == c["constants"], "same constants", "constants differ"),
                    ok(ma["specification"] == c["spec"], "same specification", "another specification"),
                    ok(sorted(invs) == sorted(c["invariants"]), f"same {len(invs)} invariants", "invariants differ"),
                    ok(sorted(props) == sorted(c["properties"]), f"same {len(props)} temporal properties", "properties differ"),
                    ok(dl is None or dl["value"].upper() == c["deadlock"].upper(), "same deadlock setting", "deadlock setting differs")),
                 html.escape(RESULTS.get(mname, ""))))
mtab = ['<table class="sync"><thead><tr><th style="width:9%"></th><th style="width:27%">@TLA_MODEL in the spec</th>'
        '<th style="width:16%">configuration file</th><th style="width:22%">in sync?</th><th>TLC result (recorded)</th></tr></thead>']
for r in rows:
    mtab.append("<tr>" + f'<td class="lbl">{r[0]}</td>' + "".join(f"<td>{x}</td>" for x in r[1:]) + "</tr>")
mtab.append("</table>")
mblock = (line_of(r"^\(\* Model-checking configuration"), line_of(r"^\*\)$", line_of(r"^\(\* Model-checking configuration")))
howto = ('<div class="prose"><p><b>Run them.</b> <code>spec/run_tlc.sh</code> runs <code>safety</code> then <code>live2</code> (seconds); '
         '<code>spec/run_tlc.sh live</code> runs the large one. A model fixes the constants, so it is finite; what TLC reports holds for '
         'that model. Timestamps are the mechanism of this algorithm, so every clock value is a different state: three processes with two '
         'requests each exceed 16 million states without finishing, which is why the models stay small.</p></div>')
add("models", "Models: @TLA_MODEL ⟷ the TLC configurations",
    "What TLC checks: which constants, which specification, which properties",
    "".join(frag_file(f"model {m}", SPEC.parent / f"MC_{m}.cfg") for m in CFG) + howto,
    frag_tla("@TLA_MODEL, @TLA_CONST_BIND, @TLA_INVARIANT, ...", [mblock]),
    "".join(mtab))

# ---------------------------------------------------------------------------------------------
# view: trace validation
# ---------------------------------------------------------------------------------------------
if TL:
    begin("Trace validation")
    sj, rec_m = method("System::state_json"), method("System::record")
    hdr = [n for n in range(ctor.start, ctor.end + 1) if "trace_" in cpp_code(CL[n - 1])]
    keys = re.findall(r'\\"(\w+)\\":\[?"', " ".join(CL[sj.start - 1:sj.end]))
    keys = [k for k in keys if k not in ("kind", "ts", "from")]
    ins, ine = tl_def("InState")
    mis, mie = tl_def("Mismatch")
    in_vars = [v for v in VARS if any(re.match(rf"\s*/\\ {v} = ", TL[n - 1]) for n in range(ins, ine + 1))]
    mis_vars = [v for v in VARS if any(f"{v}' = " in TL[n - 1] for n in range(mis, mie + 1))]
    cfg_t = (SPEC.parent / f"{MODULE}Trace.cfg").read_text() if (SPEC.parent / f"{MODULE}Trace.cfg").exists() else ""
    consts_over = dict(re.findall(r"(\w+)\s*<-\s*(\w+)", cfg_t))
    hdr_keys = re.findall(r'\\"(\w+)\\":', " ".join(cpp_code(CL[n - 1]) for n in hdr))
    last_init = max(n for n in range(ctor.start, ctor.end + 1) if re.search(rf"\b({_F})\b", cpp_code(CL[n - 1])) and "trace_" not in CL[n - 1])
    recorded = [x for x in ORDER if x in SITE and any(re.search(rf'record\("{x}"', cpp_code(CL[n - 1])) for n in range(SITE[x].m.start, SITE[x].m.end + 1))]
    sample = SPEC.parent.parent / "traces" / "n3-r2-s1.ndjson"
    sample_card = ""
    if sample.exists():
        sl = sample.read_text().split("\n")
        cut = lambda s: s if len(s) <= 330 else s[:330] + " …"   # noqa: E731
        sample_card = card("the first two lines of a recorded run", "traces/" + sample.name,
                           "<pre>" + "".join(f'<div class="l"><span class="ln">{i}</span>{html.escape(cut(sl[i - 1]))}</div>' for i in (1, 2)) + "</pre>")
    rows = [
        ("first line", tla("TraceInit == l = 0 /\\ Init /\\ InState(Header.state)") + f" <span class='at'>{TS_REL} line {tl_line(r'^TraceInit')}</span>",
         br(*(cpp(cpp_code(CL[n - 1]).strip()) + " " + at(n) for n in hdr)),
         br(ok(bool(hdr) and min(hdr) > last_init, "the initial state is recorded after the constructor has set every field",
               "the first line must be written at the end of the constructor"),
            note("TLC accepts the first line only if it is the <code>Init</code> of the spec: this is the check of <code>@TLA_INIT</code>"))),
        ("constants", tla("N <- TraceN") + ", " + tla("MaxReq <- TraceMaxReq") + f" <span class='at'>spec/{MODULE}Trace.cfg</span>",
         "the first line carries " + ", ".join(code(k) for k in hdr_keys if k != "state"),
         ok(set(consts_over) == {c for c, _, _ in CONSTS} and {c for c, _, _ in CONSTS} <= set(hdr_keys),
            "every constant of the spec takes its value from the trace", "a constant of the spec is not given by the trace")),
        ("one step", tla("Step(e) /\\ Mismatch(e.state) = {}") + f" <span class='at'>{TS_REL} line {tl_line(r'^Replay')}</span>",
         cpp("record(action, p, q)") + f" lines {rec_m.start}–{rec_m.end}",
         br(ok(recorded == ORDER, f"each of the {len(ORDER)} actions records its step", "an action does not record its step"),
            ok(sorted(TSTEP) == sorted(ACTIONS), "the trace specification can replay every action of Next, and nothing else",
               "Step and Next do not list the same actions"),
            note("the actions are those of <code>LamportMutex</code>, used unchanged: a recorded step is accepted only if the specification allows it"))),
        ("the state", "compared variable by variable in " + tla("InState") + " and " + tla("Mismatch"),
         cpp("state_json()") + f" lines {sj.start}–{sj.end}: " + ", ".join(code(k) for k in keys),
         br(ok(keys == VARS, f"the trace holds the {len(VARS)} variables, under their names in the spec", "the recorded state and the variables differ"),
            ok(in_vars == VARS and mis_vars == VARS, "the trace specification compares every one of them", "a variable is not compared"),
            note("this is where <b>values</b> are compared: the clock after <code>++clock_[p]</code> with <code>clock[p] + 1</code>, the queue after "
                 "<code>erase_requests_of</code> with the set in the spec, the messages in every channel"))),
        ("order", "line <code>l + 1</code> is matched from the state reached by line <code>l</code>",
         "every line is written while <code>mu_</code> is held",
         note("one lock makes every step atomic, so the order of the lines is the order of the steps and each recorded state is the state "
              "that one step produced. With several locks the order would have to be recorded another way")),
        ("verdict", tla("Done == l = Len(Events) /\\ UNCHANGED <<l, vars>>") + ", with deadlock checking",
         code("spec/validate_trace.sh") + ": ACCEPTED, or REJECTED at step k with the action and what differs",
         note("a line that cannot be matched leaves TLC without a successor: it reports a deadlock, and the behaviour it prints is the part of the run that the spec accepts")),
        ("recorded results", "", None, None),
    ]
    rows[-1] = ("observed", br(
        note("20 runs with N from 1 to 5 (7 to 230 steps each): ACCEPTED, every one"),
        note("13 copies of a trace with one edit each (a clock off by one, a stale <code>lastTs</code>, a wrong sender, a dropped step, two steps swapped, "
             "another initial holder, …): REJECTED 13 of 13 (<code>tools/tamper_trace.py</code>, step 4 of <code>run_all.sh</code>)"),
        note("the program with a defect (no condition (ii); no <code>lastTs</code> on an acknowledgement; no <code>Max</code> in the clock; no acknowledgement): "
             "it still prints <i>mutual exclusion held</i>, and its trace is REJECTED at a named step")), None, None)
    add("trace", "Trace validation: what the code records, what TLC checks",
        "The check that compares values: is the run that just happened a behaviour of the specification?",
        frag_cpp("the trace: first line, record, state_json", [(min(hdr), max(hdr)), (rec_m.doc, rec_m.end), (sj.doc, sj.end)]) + sample_card,
        frag_trace("LamportMutexTrace: the spec, restricted to the recorded steps",
                   [(tl_line(r"^EXTENDS"), tl_line(r"^VARIABLE l")), tl_def("InState"), tl_def("TraceInit"), tl_def("Step"), tl_def("Replay"),
                    (tl_def("Done")[0], tl_line(r"^TraceSpec"))]),
        sync_table(rows, ("trace specification", "C++", "in sync?")))

# ---------------------------------------------------------------------------------------------
# view: exercises (text; every outcome stated here was observed, see ../README.md)
# ---------------------------------------------------------------------------------------------
EX_LEFT = """<div class="card"><h3>Make the code and its annotations drift<span class="where">regenerate the views after each change</span></h3>
<div class="prose pad">
<p>Work on a copy. After each change run <code>python3 views/make_views.py --no-pdf</code>: it prints the checks that fail, and the view
shows them as <span class="bad">✗</span>. Say first which row you expect to change.</p>
<ol>
<li>In <code>request</code>, remove <code>"lastGranted"</code> from <code>@TLA_UNCHANGED</code>. Which row of the view on rule 1 fails, and why is
a variable that nobody mentions a problem?</li>
<li>In <code>recv_ack</code>, delete the statement <code>last_ts_[p][q] = m.ts;</code>. The view on the acknowledgement now says that the spec
changes <code>lastTs</code> and the code does not. Which condition of rule 5 reads that variable? Now build, record a run and validate it
(<code>LM_TRACE=t.ndjson cpp/lamport_mutex 3 2 1; spec/validate_trace.sh t.ndjson</code>).
<br><i>Observed:</i> the program prints <i>mutual exclusion held</i>; the trace is REJECTED at the first <code>RecvAck</code>: the state differs in <code>lastTs</code>.</li>
<li>In <code>release</code>, change the name of the guard to <code>pc[p] = "waiting"</code> and leave the assert as it is. The view fails; the
program still runs. What does that tell you about what an annotation is?</li>
<li>Add a field <code>int grants_ = 0;</code> to <code>System</code> and increment it in <code>acquire</code>. The view on variables asks a
question. Answer it both ways: as an excluded field, then as a new variable of the spec (what must be added to
<code>TypeOK</code>, <code>Init</code>, and to which actions?).</li>
</ol>
<p>What the views cannot see: whether <code>++clock_[p]</code> computes what <code>clock[p] + 1</code> says. They compare names and sets of
variables, not values. Trace validation compares the values, on the runs that were recorded: exercises 2 and 5 show the difference.</p>
</div></div>"""
EX_RIGHT = """<div class="card"><h3>Make the behaviour wrong<span class="where">tests against the model checker</span></h3>
<div class="prose pad">
<ol start="5">
<li><b>Drop condition (ii) in the code.</b> In <code>can_acquire</code>, remove the loop marked <code>(ii)</code>. Build, run several seeds
(<code>cpp/lamport_mutex 3 2 1</code>, <code>… 3 2 2</code>, <code>… 5 3 1</code>). Predict first: will the oracle report a violation?
<br><i>Observed:</i> nine runs, none reported one.
<br><b>Record one of these runs and validate it.</b>
<br><i>Observed:</i> REJECTED at an <code>Acquire</code>: the specification cannot take that step. The run did nothing wrong that a test could see;
it took a step that the algorithm does not allow.
<br><b>Now the same change in the spec.</b> Remove the conjunct on <code>lastTs</code> from <code>CanAcquire</code> and run
<code>spec/run_tlc.sh safety</code>.
<br><i>Observed:</i> <code>Invariant Mutex is violated</code>, with a behaviour of 7 states, in about a second.
Read the behaviour: which message was still in flight? Why do the runs not show it?</li>
<li><b>Drop the tie-break.</b> In the spec, make <code>Precedes(a, b) ≜ a[1] &lt; b[1]</code>.
<br><i>Observed:</i> <code>safety</code> finds no error (4,771 distinct states); <code>live2</code> reports that a temporal property is violated.
Which property, and what are the two processes waiting for? What does this say about "the tests pass"?</li>
<li><b>Do not acknowledge.</b> In <code>RecvRequest</code>, replace the <code>Append</code> of the acknowledgement by <code>@</code>.
<br><i>Observed:</i> <code>safety</code> finds no error (880 distinct states); <code>live2</code> reports a violation with a behaviour of 5 states.
Mutual exclusion still holds. Is the algorithm still correct?</li>
<li><b>Do not advance the clock on receipt.</b> In <code>RecvRequest</code>, make <code>t ≜ clock[p] + 1</code> (no <code>Max</code>).
<br><i>Observed:</i> <code>safety</code> finds no error; <code>live2</code> reports a violation. Which rule of the clocks (IR1, IR2) was removed,
and which condition of rule 5 can no longer become true?</li>
</ol>
<p>Make the changes of 7 and 8 in the code instead (<code>recv_request</code>, <code>tick_on_receive</code>; the compiler then asks
what the parameter <code>m</code> is for: add <code>(void)m;</code>).
<i>Observed:</i> the program still prints <i>mutual exclusion held</i>; its trace is REJECTED at one of the first receive steps.</p>
<p>In each case, make the same change in the other file as well, and decide: are the code and the spec in sync again? Is the result
still Lamport's algorithm?</p>
</div></div>"""
TOC.append(("exercises", "Exercises: break the sync, then the algorithm", "Predict, observe, explain"))
VIEWS.append('<section class="view" id="exercises"><h1>Exercises: break the sync, then the algorithm<a class="up" href="#top">↑ views</a></h1>'
             '<div class="sub">Predict, observe, explain. The outcomes marked <i>Observed</i> were obtained on this example</div>'
             f'<div class="cols"><div>{EX_LEFT}</div><div>{EX_RIGHT}</div></div></section>')

# ---------------------------------------------------------------------------------------------
# overview
# ---------------------------------------------------------------------------------------------
begin("overview")
KIND_DOC = [
    ("TLA_MODULE", "the file", "the module that the file implements"),
    ("TLA_CONST", "a field", "a CONSTANT of the spec"),
    ("TLA_VAR", "a field", "a VARIABLE of the spec, with its type"),
    ("TLA_EXCLUDED", "a field", "state that is deliberately not in the spec, with the reason"),
    ("TLA_HISTORY", "a field", "a variable kept only so that a property can be stated"),
    ("TLA_INIT", "the constructor", "the initial state, Init"),
    ("TLA_ACTION_LOCKED", "a statement", "one action: from taking the lock to the end of the block is one atomic step"),
    ("TLA_GUARD", "a statement", "one enabling conjunct of that action, named by its text"),
    ("TLA_UNCHANGED", "a statement", "the variables that the action leaves unchanged"),
    ("TLA_INVARIANT", "a statement", "a property of the spec that the code also evaluates"),
    ("TLA_MESSAGE, TLA_CHANNEL", "a struct, a field", "the message record and the queues that carry it"),
    ("TLA_PROCESS, TLA_WEAK_FAIRNESS", "a method, a class", "the threads, and why each action eventually runs"),
]
ann_rows = "".join(
    f"<tr><td>{' '.join(_span('ann', '@' + k.strip()) for k in ks.split(','))}</td><td>{where}</td><td>{what}</td>"
    f"<td>{sum(len(canns(k.strip())) for k in ks.split(','))}</td></tr>" for ks, where, what in KIND_DOC)
bind = []
for v in VARS:
    f = VAR_FIELD.get(v)
    bind.append(("variable", _v(v), VLINE[v], f"field {cpp(f.name)} {at(f.line)}" if f else "—", f is not None))
for cname, cline, _ in CONSTS:
    f = CONST_FIELD.get(cname)
    bind.append(("constant", code(cname), cline, f"field {cpp(f.name)} {at(f.line)}" if f else "—", f is not None))
bind.append(("initial state", code("Init"), DEFS["Init"][0], f"{code('System::System')} {at(ctor.start)}", bool(inits)))
for name in ORDER:
    s = SITE.get(name)
    bind.append(("action", _span("act", name), ACT[name].line, f"{code(s.m.qual)} {at(s.ann.line)}" if s else "—", s is not None))
for a in canns("TLA_INVARIANT"):
    bind.append(("invariant", code(a["name"]), DEFS.get(a["name"], (0,))[0], f"{code(enclosing(a.line).qual)} {at(a.line)}", a["name"] in DEFS))
bind_rows = "".join(f"<tr><td>{k}</td><td>{s}</td><td>{ln}</td><td>{c}</td><td>{ok(good, 'bound', 'not bound')}</td></tr>"
                    for k, s, ln, c, good in bind)
for a in canns("TLA_ACTION_LOCKED"):
    if a["name"] not in ACT:
        bind_rows += (f"<tr><td>action</td><td>—</td><td></td><td>{ann(a)} {at(a.line)}</td>"
                      f"<td>{ok(False, '', 'the spec has no action of this name')}</td></tr>")

n_ok = sum(1 for _, f, _ in CHECKS if f)
n_bad = len(CHECKS) - n_ok
verdict = (f'<span class="ok">✓ {n_ok} of {len(CHECKS)} computed checks agree</span>' if not n_bad else
           f'<span class="bad">✗ {n_bad} of {len(CHECKS)} computed checks fail</span>: '
           + "; ".join(f"{html.escape(v)}: {html.escape(t)}" for v, f, t in CHECKS if not f))
toc = "".join(f'<li><a href="#{vid}">{html.escape(t)}</a><span class="tocsub">{html.escape(s)}</span></li>' for vid, t, s in TOC)
legend_vars = " ".join(_v(v) for v in VARS)
overview = f"""<section class="view" id="top">
<h1>LamportMutex: code ⟷ specification</h1>
<div class="sub">Lamport, <i>Time, Clocks, and the Ordering of Events in a Distributed System</i> (1978), the mutual-exclusion algorithm:
<code>{REL_SPEC}</code> ({len(SL) - 1} lines) and <code>{REL_CPP}</code> ({len(CL) - 1} lines).
Generated {datetime.date.today().isoformat()} by <code>views/make_views.py</code></div>
<div class="cols"><div class="prose">
<h3>How to read the views</h3>
<p>Each view puts the C++ on the left and the TLA⁺ on the right, with the line numbers of the files, and under them a table that says
what binds the two: the annotation in the code, the construct in the spec, and whether they agree.</p>
<ul>
<li><span class="ok">✓</span> and <span class="bad">✗</span> are <b>computed</b> from the two files each time the views are generated.
Change either side so that a binding breaks, generate again, and the row turns red.</li>
<li>A line that starts with <span class="note">·</span> is an explanation <b>written by hand</b>: an argument for the reader, which no tool checked.</li>
<li>The seven state variables keep one colour on both sides: {legend_vars}.
Annotations look like {_span('ann', '@TLA_VAR')}, actions like {_span('act', 'Request')}.</li>
<li>TLA⁺ is printed with its symbols (∧ ∨ ∀ ∃ ∈ ≜ ′ ⟨ ⟩ □ ⇝) where the file has ASCII (<code>/\\ \\/ \\A \\E \\in == ' &lt;&lt; &gt;&gt; [] ~&gt;</code>).</li>
</ul>
<p class="verdict">{verdict}</p>
<h3>The views</h3>
<ol class="toc">{toc}</ol>
<h3>Three checks, and what each one compares</h3>
<ul>
<li><b>These views</b> compare <b>names and sets</b>, on the two files: every variable has a field, every action has a step, the guards
carry the text of the enabling conjuncts, the fields that a step writes are the variables that the action primes, the frame is the same on
both sides. They cannot see whether <code>++clock_[p]</code> computes <code>clock[p] + 1</code>.</li>
<li><b>Trace validation</b> compares <b>values</b>, on the runs that were recorded: the program writes every step and the state it
produced, and TLC accepts the run only if the specification can take the same steps through the same states.</li>
<li><b>Model checking</b> verifies the <b>properties</b> (mutual exclusion, the order of grants, progress) on every behaviour of the
specification, for the constants of a model. It says nothing about the code; the first two checks are what connects it to the code.</li>
</ul>
</div><div>
<div class="card"><h3>The annotations used<span class="where">{len(CANNS)} in {REL_CPP}</span></h3>
<table class="sync flush"><thead><tr><th>annotation</th><th>on</th><th>binds</th><th>count</th></tr></thead>{ann_rows}</table></div>
<div class="card" style="margin-top:10px"><h3>Binding summary<span class="where">spec symbol → code site</span></h3>
<table class="sync flush"><thead><tr><th>kind</th><th>spec symbol</th><th>spec line</th><th>code site</th><th></th></tr></thead>{bind_rows}</table></div>
</div></div></section>"""
# the verdict above was built before the summary rows were checked: rebuild it with every check
n_ok = sum(1 for _, f, _ in CHECKS if f)
n_bad = len(CHECKS) - n_ok
final = (f'<span class="ok">✓ {n_ok} of {len(CHECKS)} computed checks agree</span>' if not n_bad else
         f'<span class="bad">✗ {n_bad} of {len(CHECKS)} computed checks fail</span>: '
         + "; ".join(f"{html.escape(v)}: {html.escape(t)}" for v, f, t in CHECKS if not f))
overview = overview.replace(verdict, final)

CSS = """
:root { --line: #d0d0d0; --soft: #f3f3f1; --ink: #151515; --mute: #5d6066; }
* { box-sizing: border-box; }
html { background: #fff; }
body { font-family: "Helvetica Neue", Helvetica, Arial, sans-serif; font-size: 14px; line-height: 1.45; color: var(--ink);
       margin: 0 auto; padding: 18px 22px 60px; max-width: 1560px; background: #fff; }
.view { padding: 18px 0 30px; border-bottom: 2px solid var(--line); }
.view:last-child { border-bottom: 0; }
h1 { font-size: 22px; margin: 0 0 4px; display: flex; justify-content: space-between; align-items: baseline; gap: 12px; }
h1 .up { font-size: 12px; font-weight: 400; white-space: nowrap; }
h3 { font-size: 15px; margin: 14px 0 6px; }
.sub { color: var(--mute); margin-bottom: 12px; }
.cols { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 18px; align-items: start; }
@media (max-width: 1000px) { .cols { grid-template-columns: minmax(0, 1fr); } }
.card { border: 1px solid var(--line); border-radius: 4px; overflow: hidden; margin-bottom: 10px; }
.card h3 { margin: 0; padding: 5px 9px; background: var(--soft); font-size: 13px; font-weight: 600; border-bottom: 1px solid var(--line);
           display: flex; justify-content: space-between; flex-wrap: wrap; gap: 0 12px; }
.card h3 .where { font-weight: 400; color: var(--mute); font-size: 12px; }
.gap { border-top: 1px dashed var(--line); margin: 0 9px; }
pre { margin: 0; padding: 6px 9px; font: 12px/1.45 Menlo, Consolas, "DejaVu Sans Mono", monospace; overflow-x: auto; }
.l { white-space: pre-wrap; overflow-wrap: anywhere; padding-left: 6ch; text-indent: -6ch; }
.ln { display: inline-block; width: 3.4ch; text-align: right; color: #9a9a9a; margin-right: 1.4ch; user-select: none; }
.c { color: #6b7280; font-style: italic; }
.s { color: #15803d; }
.k { font-weight: 700; color: #1f2937; }
.ann { background: #fff1b8; color: #7c2d12; font-weight: 700; border-radius: 2px; }
.annb { color: #7c2d12; }
.act { background: #dbeafe; color: #1e3a8a; font-weight: 700; border-radius: 2px; }
.v { font-weight: 600; }
.at { color: var(--mute); font-size: 0.86em; white-space: nowrap; }
.sync { margin-top: 12px; border-collapse: collapse; width: 100%; font-size: 13px; }
.sync.flush { margin: 0; }
.sync.flush th:first-child, .sync.flush td:first-child { border-left: 0; }
.sync.flush th:last-child, .sync.flush td:last-child { border-right: 0; }
.sync.flush tr:last-child td { border-bottom: 0; }
.sync.flush thead th { border-top: 0; }
.sync.small { width: auto; margin: 0 0 10px; }
.sync th, .sync td { border: 1px solid var(--line); padding: 4px 8px; vertical-align: top; text-align: left; }
.sync th { background: var(--soft); font-weight: 600; }
.sync td.lbl { font-weight: 600; color: #333; }
.ok { color: #15803d; font-weight: 600; }
.bad { color: #b91c1c; font-weight: 600; }
.note { color: #4b4f56; }
.verdict { font-size: 15px; padding: 8px 10px; background: var(--soft); border-radius: 4px; }
code { font: 12px Menlo, Consolas, "DejaVu Sans Mono", monospace; }
a { color: #1d4ed8; text-decoration: none; }
a:hover { text-decoration: underline; }
p { margin: 0 0 9px; }
.prose ul, .prose ol { margin: 4px 0 10px 22px; padding: 0; }
.prose li { margin: 5px 0; }
.prose.pad { padding: 9px 12px 2px; }
.toc li { margin: 3px 0; }
.tocsub { color: var(--mute); font-size: 12px; margin-left: 8px; }
@page { size: A4 landscape; margin: 7mm 9mm; }
@media print {
  body { font-size: 8.2pt; line-height: 1.35; padding: 0; max-width: none; }
  .view { page-break-after: always; break-after: page; border: 0; padding: 0; }
  .sub { margin-bottom: 2.5mm; } .card { margin-bottom: 2mm; } .sync { margin-top: 2.5mm; }
  pre { padding: 1.2mm 2mm; } .card h3 { padding: 1mm 2mm; }
  .view:last-child { page-break-after: auto; break-after: auto; }
  h1 { font-size: 14pt; } h1 .up { display: none; } h3 { font-size: 9.6pt; }
  .card h3 { font-size: 8.4pt; } .card h3 .where { font-size: 7.6pt; }
  pre { font-size: 6.7pt; line-height: 1.28; overflow: visible; } code { font-size: 6.7pt; }
  .sync { font-size: 7.3pt; } .sync th, .sync td { padding: 0.55mm 1.4mm; }
  .sync tr { page-break-inside: avoid; break-inside: avoid; }
  .verdict { font-size: 9pt; } .tocsub { font-size: 7.4pt; }
  .cols { gap: 5mm; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); }
}
"""

doc = ('<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">'
       f"<title>{MODULE}: code and specification in sync</title><style>{CSS}</style></head><body>{overview}{''.join(VIEWS)}</body></html>")
OUT_HTML.write_text(doc)
print(f"wrote {OUT_HTML} ({len(VIEWS) + 1} views)")
print(f"checks: {n_ok} of {len(CHECKS)} agree" + ("" if not n_bad else f", {n_bad} FAIL"))
for v, f, t in CHECKS:
    if not f:
        print(f"  ✗ {v}: {t}")

if not ARGS.no_pdf:
    chrome = shutil.which("google-chrome") or shutil.which("chromium") or (CHROME if Path(CHROME).exists() else None)
    if chrome:
        r = subprocess.run([chrome, "--headless=new", "--disable-gpu", "--no-pdf-header-footer",
                            f"--print-to-pdf={OUT_PDF}", OUT_HTML.as_uri()], capture_output=True, text=True, timeout=180)
        if OUT_PDF.exists() and r.returncode == 0:
            print(f"wrote {OUT_PDF} ({OUT_PDF.stat().st_size // 1024} KB)")
        else:
            print("no PDF: Chrome failed:", r.stderr.strip().splitlines()[-1] if r.stderr.strip() else r.returncode)
    else:
        print("no PDF: Chrome not found; open the HTML in a browser and print it (A4 landscape)")
sys.exit(1 if n_bad else 0)
