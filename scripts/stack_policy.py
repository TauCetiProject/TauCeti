#!/usr/bin/env python3
"""Bounded, source-only no-stacking enforcement. See scripts/stack-policy.md.

Never check out or execute a PR, interpret its text as commands, or fetch a fork URL.
All mutation is opt-in; JSONL is the audit record (including gaps, never a safety proof).
"""

import argparse
import base64
from collections import defaultdict
from dataclasses import dataclass, asdict, field
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.request import Request, urlopen
from urllib.error import HTTPError


REPO = "TauCetiProject/TauCeti"
BLOCK_LABEL = "stacked-pr"
MAX_PRS = 2000
MAX_COMMITS = 256
MAX_EVIDENCE_COMMITS = 16
MAX_FILES = 128
MAX_HISTORY = 128
MAX_BYTES = 2 * 1024 * 1024
SHA = re.compile(r"[0-9a-f]{40}\Z")


class Gap(RuntimeError):
    """Observation is incomplete; do not close or claim safety."""


class UnsupportedCommit(Gap):
    """No unambiguous individual patch; another commit may still prove inheritance."""


class BudgetGap(Gap):
    """The sweep cannot continue observing within its global budget."""


class ChildGap(Gap):
    """One child's cost limit does not prevent auditing other PRs."""


def emit(**record):
    print(json.dumps(record, sort_keys=True), flush=True)


def run(args, *, data=None, env=None, limit=MAX_BYTES, timeout=90, check=True):
    p = subprocess.run(args, input=data, capture_output=True, env=env, timeout=timeout)
    if len(p.stdout) > limit:
        raise Gap(f"command output exceeds {limit} bytes: {args[0]}")
    if check and p.returncode:
        raise Gap(f"{args[0]} failed ({p.returncode}): {p.stderr[:600].decode(errors='replace')}")
    return p


class API:
    def __init__(self):
        self.token = os.environ.get("GH_TOKEN") or run(["gh", "auth", "token"]).stdout.decode().strip()
        self.calls = 0
        self.bytes = 0
        self.deadline = time.monotonic() + 1200

    def begin_child(self):
        self.child_calls, self.child_bytes = self.calls + 256, self.bytes + 16 * 1024 * 1024
        self.child_deadline = time.monotonic() + 120

    def request(self, url, method="GET", data=None):
        self.calls += 1
        if self.calls > 4000 or self.bytes > 64 * MAX_BYTES or time.monotonic() > self.deadline:
            raise BudgetGap("sweep API/time budget exhausted")
        if hasattr(self, "child_calls") and (self.calls > self.child_calls or time.monotonic() > self.child_deadline):
            raise ChildGap("child API/time budget exhausted")
        req = Request(url, method=method,
                      data=None if data is None else json.dumps(data).encode(),
                      headers={"Authorization": f"Bearer {self.token}",
                               "Accept": "application/vnd.github+json",
                               "X-GitHub-Api-Version": "2022-11-28",
                               "Content-Type": "application/json"})
        try:
            with urlopen(req, timeout=45) as response:
                raw = response.read(min(8 * MAX_BYTES, 64 * MAX_BYTES - self.bytes,
                                        getattr(self, "child_bytes", 64 * MAX_BYTES) - self.bytes) + 1)
        except HTTPError as error:
            if error.code in (403, 429):
                raise BudgetGap("API permission/rate limit refused; sweep stopped") from error
            raise
        self.bytes += len(raw)
        if self.bytes > 64 * MAX_BYTES:
            raise BudgetGap("sweep API byte budget exhausted")
        if self.bytes > getattr(self, "child_bytes", 64 * MAX_BYTES):
            raise ChildGap("child API byte budget exhausted")
        if len(raw) > 8 * MAX_BYTES:
            raise Gap("API response truncated by byte bound")
        return json.loads(raw) if raw else None

    def call(self, path, method="GET", data=None):
        return self.request(f"https://api.github.com/repos/{REPO}/{path}", method, data)

    def pages(self, path, limit):
        found = []
        for page in range(1, limit // 100 + 2):
            data = self.call(f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
            if not isinstance(data, list):
                raise Gap("expected an API array")
            found.extend(data)
            if len(found) > limit:
                raise Gap(f"pagination exceeds {limit} records: {path}")
            if len(data) < 100:
                return found
        raise Gap("incomplete pagination")

    def pr(self, number):
        p = PR.parse(self.call(f"pulls/{number}"))
        if p.state == "open":
            # REST retains head.ref after branch deletion. Ask the canonical PR
            # node for the live headRef; never trust a fork-supplied URL/ref.
            data = self.request("https://api.github.com/graphql", "POST", {
                "query": 'query($number: Int!) { repository(owner: "TauCetiProject", name: "TauCeti") '
                         '{ pullRequest(number: $number) { headRef { target { oid } } } } }',
                "variables": {"number": int(number)},
            })
            if data.get("errors"):
                if any(e.get("type") == "RATE_LIMITED" for e in data["errors"]):
                    raise BudgetGap("GraphQL API rate limit refused; sweep stopped")
                raise Gap("live branch metadata unavailable")
            ref = data["data"]["repository"]["pullRequest"]["headRef"]
            if not ref or ref["target"]["oid"] != p.head:
                raise Gap("head branch deleted, inaccessible or changed")
        return p

    def main(self):
        return oid(self.call("git/ref/heads/main")["object"]["sha"])

    def declared_parents(self, child):
        """Only current GitHub-rendered prose may establish a body-only edge."""
        cache = self.__dict__.setdefault("declarations", {})
        key = child.number, child.head, child.body
        if key not in cache:
            try:
                if not re.search(r"stack|depend|prereq|parent PR|based on|built on|carries", child.body, re.I):
                    cache[key] = set()
                else:
                    data = self.request("https://api.github.com/graphql", "POST", {
                        "query": 'query($number: Int!) { repository(owner: "TauCetiProject", name: "TauCeti") '
                                 '{ pullRequest(number: $number) { body bodyHTML headRefOid } } }',
                        "variables": {"number": child.number},
                    })
                    errors = data.get("errors") or []
                    if any(e.get("type") == "RATE_LIMITED" for e in errors):
                        raise BudgetGap("GraphQL API rate limit refused; sweep stopped")
                    if errors:
                        raise Gap("rendered PR prose unavailable")
                    p = data["data"]["repository"]["pullRequest"]
                    if not p or (p["body"] or "") != child.body or p["headRefOid"] != child.head:
                        raise Gap("rendered PR prose/head identity changed; retry fresh metadata")
                    cache[key] = rendered_parents(p["bodyHTML"])
                    if not cache[key]:
                        emit(declaration_pr=child.number,
                             gap="no complete unqualified rendered parent declaration; body-only inference declined")
            except BudgetGap:
                raise
            except Exception as error:
                cache[key] = Gap(f"unverified rendered PR prose: {error}")
        if isinstance(cache[key], Gap):
            raise cache[key]
        return cache[key]


def oid(value):
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise Gap("missing/invalid commit identity")
    return value


@dataclass(frozen=True)
class PR:
    number: int
    state: str
    head: str
    base: str
    branch: str
    head_repo: str
    body: str
    draft: bool
    base_head: str = ""
    blocked: bool = field(default=False, compare=False)
    landing_claim: bool = False
    author_id: int = 0

    @classmethod
    def parse(cls, p):
        if p["base"]["repo"]["full_name"] != REPO:
            raise Gap("PR belongs to another repository")
        h = p["head"]
        if not h.get("repo"):
            raise Gap(f"#{p['number']}: deleted head repository")
        return cls(int(p["number"]), p["state"], oid(h["sha"]), p["base"]["ref"],
                   h["ref"], h["repo"]["full_name"], p.get("body") or "", bool(p["draft"]),
                   oid(p["base"]["sha"]), any(l.get("name") == BLOCK_LABEL for l in p.get("labels", [])),
                   p.get("merged_at") is not None or bool(re.match(r"^\[Merged by Bors\] - ",
                                                                  p.get("title") or "", re.I)),
                   int((p.get("user") or {}).get("id") or 0)
                   if (p.get("user") or {}).get("login") != "ghost" else 0)


def event_targets(event, prs):
    """Focus events; reserve full source sweeps for schedules/manual dispatches."""
    if event.get("pull_request"):
        return {int(event["pull_request"]["number"])}
    wake = event.get("workflow_run")
    if not wake:
        return None
    head = oid(wake.get("head_sha"))
    associated = set()
    for linked in wake.get("pull_requests") or []:
        base = (linked.get("base") or {}).get("repo") or {}
        if ((base.get("full_name") == REPO or base.get("url") == f"https://api.github.com/repos/{REPO}")
                and (linked.get("head") or {}).get("sha") == head):
            associated.add(int(linked["number"]))
    # Wake completions can arrive out of push order and replace a newer pending
    # wake. Recompute the current branch's PRs, rather than declining its changed
    # head. This stays focused and never fetches a fork URL.
    repo = (wake.get("head_repository") or {}).get("full_name")
    branch = wake.get("head_branch")
    matched = {p.number for p in prs if p.base != "main"
               and p.head_repo == repo and p.branch == branch}
    if associated or matched:
        return associated | matched
    raise Gap("wake has no associated PR/current canonical PR identity match")


def rendered_prose_parents(body):
    """Candidate identities from filtered rendered paragraphs, never raw Markdown."""
    result = set()
    for line in body.splitlines():
        for sentence in re.split(r"(?<=[.!?])\s+", line):
            if re.search(r"\b(not|no|none|never|previously|formerly|historically|was|used to|isn't|isn’t)\b", sentence, re.I):
                continue
            claim = re.search(
                r"\bstack(?:ed|s|ing)?\s+on\b|"
                r"(?:^\s*(?:[-*]\s*)?|\bthis (?:PR|branch) (?:is )?)"
                r"(?:depends? on|based on|built on|carries (?:unmerged |prerequisite )?commits from)\b|"
                r"\b(?:prerequisites?|dependencies|parent PR)\s*:", sentence, re.I)
            if claim:
                if not re.fullmatch(
                        r"\s*(?:[-*]\s*)?(?:this (?:PR|branch|pull request) (?:is )?)?",
                        sentence[:claim.start()], re.I):
                    continue
                # Identities must belong to this particular declaration. Other
                # sentences may discuss superseded source or mathematical uses.
                tail = sentence[claim.end():]
                first = re.match(r"\s*(?:PR\s*|pull request\s*)?[\[(\s]*#([1-9]\d*)\b", tail, re.I)
                if not first:
                    continue
                declared = {int(first[1])}
                tail = tail[first.end():]
                # Only a contiguous reference list belongs to this declaration.
                # Later clauses (e.g. supersedes #N) cannot acquire parenthood.
                while match := re.match(r"[\s,\[\]()&+]*(?:and\s+)?#([1-9]\d*)\b", tail, re.I):
                    declared.add(int(match[1]))
                    tail = tail[match.end():]
                # A body-only declaration must be complete, rather than a
                # question, condition or fragment followed by qualifying prose.
                if re.fullmatch(r"[\s\])]*\.?\s*", tail):
                    result.update(declared)
    return result


class RenderedProse(HTMLParser):
    """Read HTML as data; never execute/fetch it or infer code from Markdown."""
    excluded = {"pre", "code", "blockquote", "q", "kbd", "samp", "tt", "var",
                "script", "style", "textarea", "template", "del", "s", "strike"}
    blocks = {"p", "div", "li", "hr", "ul", "ol", "table", "tr", "td", "th",
              "h1", "h2", "h3", "h4", "h5", "h6", "details", "summary"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.hidden = defaultdict(int)
        self.anchors = []
        self.prose, self.quoting = [], []

    def boundary(self):
        self.prose.append("\x1e")
        self.quoting.append("\n")

    def opaque(self):
        # Excluding inline markup must not manufacture a fresh sentence start.
        self.prose.append(" [excluded] ")

    def handle_starttag(self, tag, attrs):
        if tag in self.excluded:
            self.hidden[tag] += 1
            self.opaque()
        elif tag == "a":
            canonical = False
            if not any(self.hidden.values()):
                href = dict(attrs).get("href") or ""
                if href.startswith("/"):
                    href = "https://github.com" + href
                match = re.fullmatch(r"https://github\.com/([^/]+/[^/]+)/(?:pull|issues)/([1-9]\d*)(?:[/?#].*)?", href)
                if match and match[1].lower() == REPO.lower():
                    self.prose.append(f" #{match[2]} ")
                    canonical = True
            self.anchors.append(not canonical)
            if not canonical:
                self.opaque()
            self.hidden[tag] += 1  # Link labels cannot manufacture declarations.
        elif tag in self.blocks:
            self.boundary()
        elif tag == "br":
            self.prose.append(" ")

    def handle_endtag(self, tag):
        if tag == "a" and self.anchors:
            self.hidden[tag] -= 1
            if self.anchors.pop():
                self.opaque()
        elif self.hidden[tag]:
            self.hidden[tag] -= 1
            self.opaque()
        elif tag in self.blocks:
            self.boundary()

    def handle_data(self, data):
        data = data.replace("\x1e", " ")
        # Suppressed markup cannot declare parents, but it may veto a claim.
        # In particular, formatting a negative link label as code must not
        # erase its negation. This deliberately favors conservative misses.
        self.quoting.append(data)
        if not any(self.hidden.values()):
            self.prose.append(data)


def rendered_parents(html):
    """Extract candidate PR identities from canonical GitHub-rendered HTML.

    Code/quotation/retracted elements and link labels cannot declare parents; soft wraps
    and inline exclusions do not create sentence starts. Literal quoted prose
    or explicit example/historical context conservatively returns an empty set.
    Missing/non-string/oversized input is
    a Gap, distinct from declined inference. Metadata identity must be checked
    by the caller; even returned identities require independent source proof.
    """
    if not isinstance(html, str) or len(html.encode()) > MAX_BYTES:
        raise Gap("rendered PR prose missing or exceeds byte bound")
    parser = RenderedProse()
    parser.feed(html)
    parser.close()
    # Literal quotation can span paragraphs/inline markup. Conservatively decline
    # body-only inference in such prose; exact ancestry/base evidence still works.
    visible = "".join(parser.quoting)
    if re.search(r'''["“”‘’«»‹›„‟「」『』]|(?<!\w)'|'(?!\w)''', visible):
        return set()
    if "`" in visible or "<!--" in visible:
        return set()
    if "?" in visible or re.search(r"\b(?:if|when|in case|unless|would|could|should|might|maybe|perhaps|hypothetical\w*)\b", visible, re.I):
        return set()
    if re.search(r"\b(?:examples?|for reference|not|no|none|never|previously|formerly|historically|was|used to|isn't|isn’t|supersed\w*)\b", visible, re.I):
        return set()
    paragraphs = [" ".join(p.split()) for p in "".join(parser.prose).split("\x1e")]
    return rendered_prose_parents("\n".join(paragraphs))


class Source:
    """Disposable bare object/index store. PR refs always come from the canonical repo."""
    def __init__(self, directory, api, main, alternates=None, remote=None):
        self.root = Path(directory)
        self.api = api
        self.main = main
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null",
                        GIT_TERMINAL_PROMPT="0", GIT_NO_REPLACE_OBJECTS="1",
                        GIT_NO_LAZY_FETCH="1", GIT_LITERAL_PATHSPECS="1")
        run(["git", "init", "--bare", "--template=", str(self.root)], env=self.env)
        if alternates:
            (self.root / "objects/info/alternates").write_text(str(Path(alternates).resolve()) + "\n")
        self.git("remote", "add", "origin", remote or f"https://github.com/{REPO}.git")
        self.commits_cache = {}
        self.patch_cache = {}
        self.landed_cache = {}
        self.tree_cache = {}
        self.blobs_checked = set()
        self.parent_patch_cache = {}
        self.zero_cache = {}
        self.index = str(self.root / "policy-index")
        self.started = time.monotonic()
        self.deadline = self.started + 1200
        self.calls = 0

    def begin_child(self):
        self.child_calls = self.calls + 2500
        self.child_deadline = time.monotonic() + 120

    def git(self, *args, data=None, check=True, limit=MAX_BYTES):
        if hasattr(self, "deadline"):
            self.calls += 1
            if self.calls > 30000 or time.monotonic() > self.deadline:
                raise BudgetGap("source operation/time budget exhausted")
            if hasattr(self, "child_calls") and (self.calls > self.child_calls or time.monotonic() > self.child_deadline):
                raise ChildGap("child source operation/time budget exhausted")
        return run(["git", "--git-dir", str(self.root), *args], data=data,
                   env={**self.env, "GIT_INDEX_FILE": self.index} if hasattr(self, "index") else self.env,
                   check=check, limit=limit)

    def fetch(self, prs):
        self.git("fetch", "--no-tags", "--filter=blob:none", "origin", self.main)
        main_history = set(self.git("rev-list", "--max-count=64001", self.main,
                                    limit=4 * MAX_BYTES).stdout.decode().splitlines())
        if len(main_history) > 64000:
            raise Gap("main history exceeds graph bound")
        for start in range(0, len(prs), 100):
            batch = prs[start:start + 100]
            try:
                self.git("fetch", "--no-tags", "--filter=blob:none", f"--depth={MAX_COMMITS}", "origin",
                         *(f"+refs/pull/{p.number}/head:refs/policy/{p.number}" for p in batch))
            except (BudgetGap, ChildGap):
                raise
            except (Gap, subprocess.TimeoutExpired):
                for p in batch:
                    try:
                        self.git("fetch", "--no-tags", "--filter=blob:none", f"--depth={MAX_COMMITS}",
                                 "origin", f"+refs/pull/{p.number}/head:refs/policy/{p.number}")
                    except BudgetGap:
                        raise
                    except (Gap, subprocess.TimeoutExpired):
                        self.commits_cache[p.head] = None
        shallow = self.root / "shallow"
        if shallow.exists():
            # The trusted checkout supplies complete main history. Depth-limited
            # PR fetches must not hide a formerly-main ancestor from exclusion.
            remaining = set(shallow.read_text().splitlines()) - main_history
            if remaining:
                shallow.write_text("\n".join(sorted(remaining)) + "\n")
            else:
                shallow.unlink()
        # No implicit network fetches when reading source. Missing blobs are fetched
        # through the byte-budgeted API and verified by object identity below.
        self.git("config", "remote.origin.promisor", "false")
        for p in prs:
            if p.head in self.commits_cache:
                continue
            actual = self.git("rev-parse", f"refs/policy/{p.number}", check=False).stdout.decode().strip()
            if actual != p.head:
                self.commits_cache[p.head] = None

    def commits(self, head):
        if head not in self.commits_cache:
            rows = self.git("rev-list", f"--max-count={MAX_COMMITS + 1}", head,
                            "--not", self.main).stdout.decode().splitlines()
            shallow = self.root / "shallow"
            if len(rows) > MAX_COMMITS or (shallow.exists() and set(rows) & set(shallow.read_text().splitlines())):
                raise Gap("non-main history exceeds bound or reaches shallow boundary")
            self.commits_cache[head] = set(rows)
        if self.commits_cache[head] is None:
            raise Gap("head changed while fetching")
        return self.commits_cache[head]

    def tree(self, revision, paths):
        key = revision, tuple(paths)
        if key not in self.tree_cache:
            rows = self.git("ls-tree", "-rz", revision, "--", *paths).stdout.split(b"\0")
            self.tree_cache[key] = {r.split(b"\t", 1)[0].split()[2].decode() for r in rows if r}
        return self.tree_cache[key]

    def blobs(self, objects):
        for sha in sorted(objects):
            if sha in self.blobs_checked:
                continue
            exists = self.git("cat-file", "-e", sha, check=False)
            if exists.returncode == 0:
                size = int(self.git("cat-file", "-s", sha).stdout)
                if size > MAX_BYTES // 2:
                    raise Gap("source blob exceeds byte bound")
                self.blobs_checked.add(sha)
                continue
            data = self.api.call(f"git/blobs/{oid(sha)}")
            if data.get("encoding") != "base64" or data["size"] > MAX_BYTES // 2:
                raise Gap("source blob exceeds bound or unsupported encoding")
            raw = base64.b64decode(data["content"], validate=False)
            if len(raw) != data["size"]:
                raise Gap("incomplete source blob")
            actual = self.git("hash-object", "-w", "--stdin", data=raw).stdout.decode().strip()
            if actual != sha:
                raise Gap("source object identity mismatch")
            self.blobs_checked.add(sha)

    def patch(self, parent):
        if parent.head in self.parent_patch_cache:
            return self.parent_patch_cache[parent.head]
        bases = self.git("merge-base", "--all", self.main, parent.head).stdout.decode().splitlines()
        if len(bases) != 1:
            raise Gap("ambiguous parent fork point")
        self.parent_patch_cache[parent.head] = self.patch_between(bases[0], parent.head)
        return self.parent_patch_cache[parent.head]

    def commit_patch(self, commit):
        parents = self.git("rev-list", "--parents", "-n", "1", commit).stdout.decode().split()
        if len(parents) != 2:
            raise UnsupportedCommit("commit patch requires exactly one parent")
        return self.patch_between(parents[1], commit)

    def patch_between(self, base, head):
        key = base, head
        if key not in self.patch_cache:
            paths = self.git("diff", "--no-renames", "--name-only", "-z", base, head).stdout.split(b"\0")
            paths = [p.decode() for p in paths if p]
            if len(paths) > MAX_FILES:
                raise Gap("parent diff exceeds file bound")
            if not paths:
                return base, [], b""
            self.blobs(self.tree(base, paths) | self.tree(head, paths))
            patch = self.git("diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--binary",
                             "--full-index", base, head).stdout
            self.patch_cache[key] = (base, paths, patch)
        return self.patch_cache[key]

    def contains(self, revision, paths, patch, *, zero=False):
        self.blobs(self.tree(revision, paths))
        self.git("read-tree", revision)
        p = self.git("apply", "--cached", "--reverse", "--check", "--whitespace=nowarn",
                     *( ["--unidiff-zero"] if zero else []), "-",
                     data=patch, check=False)
        if p.returncode not in (0, 1):
            raise Gap("cannot test reverse patch application")
        return p.returncode == 0

    def zero_patch(self, base, head):
        if (base, head) not in self.zero_cache:
            self.zero_cache[base, head] = self.git(
                "diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--binary",
                "--full-index", "--unified=0", base, head).stdout
        return self.zero_cache[base, head]

    def landed(self, parent, base, paths, patch, *, head=None):
        key = base, hashlib.sha256(patch).hexdigest()
        if key not in self.landed_cache:
            zero = self.zero_patch(base, head or parent.head)
            # Scan actual main source history, not mergedAt/state/title. Include
            # combined bors squash commits and subsequently modified/reverted files.
            rows = self.git("log", "--first-parent", f"--max-count={MAX_HISTORY + 1}", "--format=%H",
                            f"{base}..{self.main}", "--", *paths).stdout.decode().splitlines()
            possible = None
            for revision in dict.fromkeys([self.main, *rows[:MAX_HISTORY]]):
                if self.contains(revision, paths, patch):
                    self.landed_cache[key] = revision
                    break
                if possible is None and self.contains(revision, paths, zero, zero=True):
                    possible = revision
            else:
                if possible:
                    error = Gap(f"possible landed content after context drift at {possible}; no closure")
                    self.landed_cache[key] = error
                    raise error
                if len(rows) > MAX_HISTORY:
                    raise Gap("main's relevant source history exceeds squash-equivalence bound")
                self.landed_cache[key] = None
        if isinstance(self.landed_cache[key], Gap):
            raise self.landed_cache[key]
        return self.landed_cache[key]

    def present_at_fork(self, child, base, paths, patch, head):
        forks = self.git("merge-base", "--all", self.main, child.head).stdout.decode().splitlines()
        if len(forks) != 1:
            raise Gap("ambiguous child fork point")
        zero = self.zero_patch(base, head)
        return self.contains(forks[0], paths, patch) or self.contains(forks[0], paths, zero, zero=True)


@dataclass(frozen=True)
class Evidence:
    parent: int
    parent_head: str
    child_head: str
    main: str
    kind: str
    commit: str
    patch_sha256: str
    patch_base: str = ""


class Detector:
    def __init__(self, api, source, prs):
        self.api, self.source = api, source
        self.prs = {p.number: p for p in prs}
        self.index = defaultdict(set)
        self.gaps = {}
        for p in prs:
            try:
                # Closed parents are scoped to the child explicitly naming
                # them. Their discovery by another child must not alter this PR.
                if p.state == "open":
                    for commit in source.commits(p.head):
                        self.index[commit].add(p.number)
            except (BudgetGap, ChildGap):
                raise
            except Gap as e:
                self.gaps[p.number] = str(e)

    def candidates(self, child):
        if self.api is None:
            raise Gap("verified PR prose provider unavailable")
        explicit = self.api.declared_parents(child) - {child.number}
        numbers = set(explicit)
        for commit in self.source.commits(child.head):
            numbers.update(self.index[commit])
        for p in list(self.prs.values()):
            if p.state == "open" and p.head_repo == REPO and child.base == p.branch and child.number != p.number:
                numbers.add(p.number)
        if len(numbers) > 64:
            raise Gap("parent candidate bound exceeded")
        return sorted(numbers - {child.number}), explicit

    def detect(self, child):
        if child.number in self.gaps:
            raise Gap(self.gaps[child.number])
        commits = self.source.commits(child.head)
        candidates, explicit = self.candidates(child)
        reasons = []
        gaps = []
        for number in candidates:
            try:
                parent = self.prs.get(number)
                if parent is None:
                    raise Gap("explicit parent absent from bounded index")
                if parent.head == child.head:
                    reasons.append(f"#{number}: identical head; duplicate identity is not a stack proof")
                    continue
                parent_commits = self.source.commits(parent.head)
                if not parent_commits:
                    reasons.append(f"#{number}: head already on main")
                    continue
                if child.head in parent_commits:
                    # A dependent contains its prerequisite's commits too. Do
                    # not reverse the edge and close the standalone prerequisite.
                    reasons.append(f"#{number}: descendant of this child, not a parent")
                    continue
                shared = sorted(commits & parent_commits)
                canonical_base = (parent.state == "open" and parent.head_repo == REPO
                                  and child.base == parent.branch)
                relationship = number in explicit or canonical_base
                if not shared and not relationship:
                    continue
                graph_direction = parent.head in commits or canonical_base
                if not relationship:
                    if not graph_direction:
                        raise Gap("shared ancestry without a confirmed direction/complete parent delta")
                # A stale PR-number reference does not bind a future parent head.
                # A different principal can copy this child's prefix into that PR.
                # Only a current canonical base choice bypasses provenance guards.
                provenance_gap = None
                if not canonical_base:
                    if parent.head_repo != child.head_repo:
                        provenance_gap = "cross-repository parent provenance unproved; possible copied prefix"
                    elif not child.author_id or parent.author_id != child.author_id:
                        provenance_gap = "parent has unknown/different author; possible third-party branch PR"
                if not relationship and provenance_gap:
                    raise Gap(provenance_gap)
                base, paths, patch = self.source.patch(parent)
                if not patch:
                    reasons.append(f"#{number}: empty parent delta")
                aggregate_retained = bool(patch and self.source.contains(child.head, paths, patch))
                # A descendant can edit part of the parent's aggregate diff while
                # retaining another complete, individually unlanded commit. Check
                # exact commit patches, with the same main-history exclusion.
                if not graph_direction and not aggregate_retained:
                    raise Gap("body-only direction without complete current parent content")
                landed = self.source.landed(parent, base, paths, patch) if patch else None
                if landed:
                    reasons.append(f"#{number}: aggregate source equivalent landed at {landed}")
                # Body-only links can establish whole-parent patch identity for
                # a cherry-pick/rebase. They cannot attribute a shared precursor
                # commit to a dependent PR whose own current work is absent.
                eligible = parent_commits if graph_direction else {parent.head}
                ordered = sorted(eligible - {parent.head})
                if parent.head in eligible:
                    ordered.insert(0, parent.head)
                unsupported = False
                for commit in ordered[:MAX_EVIDENCE_COMMITS]:
                    try:
                        cb, cp, delta = self.source.commit_patch(commit)
                    except UnsupportedCommit:
                        unsupported = True
                        continue
                    if (delta and self.source.contains(child.head, cp, delta)
                            and not self.source.landed(parent, cb, cp, delta, head=commit)):
                        if commit not in commits and self.source.present_at_fork(child, cb, cp, delta, commit):
                            raise Gap("matched content already present at child's main fork point; base drift")
                        if parent.state == "closed" and parent.landing_claim:
                            raise Gap("closed parent reports landing but exact source equivalence is unproved")
                        kind = ("retained-unmerged-commit" if commit in commits
                                else "explicit-parent-commit-content")
                        if aggregate_retained:
                            kind = ("ancestor-head" if commit == parent.head and commit in commits
                                    else "shared-unmerged-commit" if commit in commits
                                    else "explicit-parent-content")
                        if provenance_gap:
                            raise Gap(provenance_gap)
                        return Evidence(number, parent.head, child.head, self.source.main,
                                        kind, commit, hashlib.sha256(delta).hexdigest(), cb), reasons
                if len(ordered) > MAX_EVIDENCE_COMMITS:
                    raise Gap("retained-commit evidence search exceeds 16-commit bound")
                if unsupported:
                    raise Gap("individual merge/root commit unsupported; no alternative retained commit proof")
                reasons.append(f"#{number}: no complete unlanded parent delta/commit retained")
            except (BudgetGap, ChildGap):
                raise
            except (Gap, KeyError, ValueError) as e:
                gaps.append(f"#{number}: {e}")
        if gaps:
            raise Gap("; ".join(gaps))
        return None, reasons


def unchanged(api, child, parent, main):
    """Fresh identities/body/base/state before EACH externally visible mutation."""
    return api.pr(parent.number) == parent and api.pr(child.number) == child and api.main() == main


def comment_text(evidence, parent_state="open"):
    e = evidence
    detail = (f"[{e.kind} `{e.commit}`](https://github.com/{REPO}/commit/{e.commit}); " if e.commit else "")
    next_step = ("The prerequisite PR is closed without this source landing. Remove the inherited work, "
                 "or resubmit the prerequisite separately and wait for it to land. " if parent_state == "closed"
                 else "Wait for the prerequisite to land. ")
    return (
        f"<!-- tauceti-no-stack:v1 child={e.child_head} -->\n"
        f"Stacked PRs are not allowed in Tau Ceti. This PR includes unmerged work from #{e.parent}: "
        f"{detail}the source patch from `{e.patch_base}` to `{e.commit}` "
        f"(parent PR's current head: [`{e.parent_head}`](https://github.com/{REPO}/commit/{e.parent_head})) "
        f"is reverse-applicable to child `{e.child_head}`, but not to the inspected main source history "
        f"ending at `{e.main}` (patch SHA-256 `{e.patch_sha256}`).\n\n"
        f"{next_step}Rebase onto current main so the diff contains only "
        "this PR's own changes and reopen or submit it as a standalone PR. Closing this PR under the "
        "no-stacking policy if the final identity check still matches; its branch is preserved. "
        "Drafts and keep/hold/human labels do not exempt stacks."
    )


def enforce(api, child, parent, evidence, actor):
    body = comment_text(evidence, parent.state)
    preserve_gap = child.head_repo == REPO and child.landing_claim
    if preserve_gap:
        body += " Automatic closure is declined because this repository head has a bors merged-title marker; branch preservation requires investigation."
    marker = body.splitlines()[0]
    comments = api.pages(f"issues/{child.number}/comments", 1000)
    # Trust only our installation/account's exact marker; candidate authors cannot
    # suppress the explanation by posting an imitation comment.
    existing = next((c for c in comments if c["user"]["login"] == actor
                     and c["body"].startswith(marker + "\nStacked PRs are not allowed in Tau Ceti.")), None)
    if not unchanged(api, child, parent, evidence.main):
        raise Gap("identities changed before comment; retry with fresh observations")
    if not existing:
        api.call(f"issues/{child.number}/comments", "POST", {"body": body})
    elif existing["body"] != body:
        # A previous attempt may have declined closure on a race. Keep one
        # explanation for this child head while updating its current evidence.
        api.call(f"issues/comments/{int(existing['id'])}", "PATCH", {"body": body})
    if not unchanged(api, child, parent, evidence.main):
        raise Gap("identities changed before close; explanation retained, closure declined")
    if preserve_gap:
        raise Gap("repository-head bors marker: branch preservation unproved, closure declined")
    # PATCH closes without deleting the branch. GitHub emits pull_request.closed;
    # bors's existing handler cancels batch/try work just as bors r- does.
    api.call(f"pulls/{child.number}", "PATCH", {"state": "closed"})


def block(api, child):
    """Only confirmed stacks affect admission; no recurring per-head status writes."""
    if not getattr(api, "label_ready", False):
        try:
            api.call(f"labels/{BLOCK_LABEL}")
        except HTTPError as error:
            if error.code != 404:
                raise
            api.call("labels", "POST", {"name": BLOCK_LABEL, "color": "b60205",
                                        "description": "Confirmed unmerged prerequisite work; bors admission blocked"})
        api.label_ready = True
    current = api.pages(f"issues/{child.number}/labels", 1000)
    if not any(l["name"] == BLOCK_LABEL for l in current):
        api.call(f"issues/{child.number}/labels", "POST", {"labels": [BLOCK_LABEL]})
    if not any(l["name"] == BLOCK_LABEL for l in api.pages(f"issues/{child.number}/labels", 1000)):
        raise Gap("bors blocking label was not applied; closure declined")


def owns_block(api, child, actor):
    events = [e for e in api.pages(f"issues/{child.number}/events", 1000)
              if e.get("event") == "labeled" and e.get("label", {}).get("name") == BLOCK_LABEL]
    return bool(events and max(events, key=lambda e: int(e["id"])).get("actor", {}).get("login") == actor)


def membership(data, child):
    """Read-only verification; a successful GitHub close alone proves no withdrawal."""
    if (not isinstance(data, dict) or data.get("schema") != "tauceti-bors.observation/v1"
            or data.get("repo") != REPO or data.get("base") != "main"
            or not isinstance(data.get("batches"), list) or not isinstance(data.get("held"), list)
            or data.get("batch_ids") != [b.get("id") for b in data["batches"]]):
        raise Gap("incomplete bors membership observation")
    active = []
    for member in [*data["held"], *(m for b in data["batches"] for m in b.get("members", []))]:
        if (not isinstance(member, dict) or type(member.get("pr")) is not int
                or not isinstance(member.get("head_sha"), str) or not SHA.fullmatch(member["head_sha"])):
            raise Gap("incomplete bors member identity")
    for batch in data["batches"]:
        if batch.get("state") not in {"waiting", "running"} or not isinstance(batch.get("members"), list):
            raise Gap("incomplete bors batch membership")
        if any(m.get("pr") == child.number and m.get("head_sha") == child.head for m in batch["members"]):
            active.append(batch["id"])
    held = any(m.get("pr") == child.number and m.get("head_sha") == child.head for m in data["held"])
    return {"batches": active, "held": held}


def verify_withdrawal(child, before, observe, sleep=time.sleep):
    """Six bounded observations after close, allowing webhook delivery latency."""
    for attempt in range(6):
        after = membership(observe(), child)
        emit(pr=child.number, head=child.head, bors_before=before, bors_after=after,
             withdrawal="observed" if before and (before["batches"] or before["held"])
             and not (after["batches"] or after["held"]) else "not-proved")
        if not (after["batches"] or after["held"]):
            return
        if attempt < 5:
            sleep(5)
    raise Gap("closed child still admitted in bors; withdrawal pending, inspect close webhook/reconciliation")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--pr", type=int, default=0)
    ap.add_argument("--report", type=Path)
    ap.add_argument("--github-event", type=Path)
    args = ap.parse_args()
    if args.pr < 0:
        raise Gap("invalid PR number")
    if args.report:
        # Never accept an API/PR-supplied report path.
        sys.stdout = args.report.open("w")
    api = API()
    event = json.loads(args.github_event.read_text()) if args.github_event else {}
    prs = []
    metadata_gaps = set()
    incomplete_index = False
    for raw in api.pages("pulls?state=open&sort=created&direction=asc", MAX_PRS):
        try:
            prs.append(PR.parse(raw))
        except (Gap, KeyError, ValueError) as error:
            number = raw.get("number")
            emit(index_pr=number, classification="unknown", gap=str(error))
            metadata_gaps.add(number)
            incomplete_index = True
    main_sha = api.main()
    targets = {args.pr} if args.pr else event_targets(event, prs)
    selected = [p for p in prs if targets is None or p.number in targets]
    if targets is not None and not selected:
        if incomplete_index:
            raise Gap("requested/event PR metadata unavailable in the bounded index")
        emit(classification="superseded", reason="target absent from complete open index", selected=0)
        return False
    selected.sort(key=lambda p: p.number, reverse=True)
    emit(scope="backlog" if targets is None else "focused", selected=[p.number for p in selected])
    # Resolve closed explicit parents once, before fetching/indexing. A closed PR
    # can still contain unlanded prerequisite work. Never assume closure = landing.
    indexed = {p.number for p in prs}
    references = set()
    for child in selected:
        try:
            references.update(api.declared_parents(child))
        except BudgetGap:
            raise
        except Gap as error:
            emit(declaration_pr=child.number, classification="unknown", gap=str(error))
    references -= indexed
    for number in sorted(references, reverse=True)[64:]:
        emit(index_pr=number, classification="unknown", gap="closed-parent lookup budget exceeded")
    for number in sorted(references, reverse=True)[:64]:
        try:
            prs.append(api.pr(number))
        except BudgetGap:
            raise
        except Exception as e:
            # A prose #reference may name an issue, a deleted fork, or an
            # inaccessible parent. Preserve the per-child gap, not a fake PR.
            emit(index_pr=number, classification="unknown", gap=f"explicit parent metadata: {e}")
    actor = os.environ.get("STACK_ACTOR", "")
    if args.apply and not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*(?:\[bot\])?", actor):
        raise Gap("STACK_ACTOR is required to authenticate idempotency comments")
    common = run(["git", "rev-parse", "--git-common-dir"]).stdout.decode().strip()
    failures, unknowns = 0, len(metadata_gaps if targets is None else targets & metadata_gaps)
    with tempfile.TemporaryDirectory(prefix="no-stack-") as directory:
        source = Source(directory, api, main_sha, Path(common) / "objects")
        source.fetch(prs)
        detector = Detector(api, source, prs)
        for number, gap in sorted(detector.gaps.items()):
            emit(index_pr=number, head=detector.prs[number].head,
                 main=main_sha, classification="unknown", gap=gap)
        for child in selected:
            mutation_started = False
            try:
                api.begin_child()
                source.begin_child()
                evidence, reasons = detector.detect(child)
                api.begin_child()
                source.begin_child()
                emit(pr=child.number, head=child.head, main=main_sha,
                     classification="confirmed-stack" if evidence else "no-confirmed-stack",
                     evidence=asdict(evidence) if evidence else None, reasons=reasons,
                     child_repository=child.head_repo, child_author_id=child.author_id,
                     parent_repository=detector.prs[evidence.parent].head_repo if evidence else None,
                     parent_author_id=detector.prs[evidence.parent].author_id if evidence else None)
                if evidence and not args.apply:
                    if not unchanged(api, child, detector.prs[evidence.parent], main_sha):
                        raise Gap("dry-run preflight identities changed; no mutation")
                    emit(pr=child.number, preflight="current child/parent/main identities and live branches verified")
                if args.apply:
                    if evidence:
                        parent = detector.prs[evidence.parent]
                        if not unchanged(api, child, parent, main_sha):
                            raise Gap("identities changed before blocking label")
                        from bors_observation import observation
                        before = None
                        try:
                            before = membership(observation(), child)
                            emit(pr=child.number, head=child.head, bors_before=before)
                        except Exception as error:
                            emit(pr=child.number, bors_gap=str(error))
                        if not unchanged(api, child, parent, main_sha):
                            raise Gap("identities changed during bors observation")
                        mutation_started = True
                        block(api, child)
                        enforce(api, child, parent, evidence, actor)
                        emit(pr=child.number, mutation="closed", withdrawal="pull_request.closed webhook")
                        verify_withdrawal(child, before, observation)
                    elif child.blocked:
                        if incomplete_index or detector.gaps:
                            raise Gap("incomplete parent index; retaining blocking label")
                        if not owns_block(api, child, actor):
                            raise Gap("blocking label is not policy-owned; retaining it")
                        if api.main() != main_sha or api.pr(child.number) != child:
                            raise Gap("identities changed before removing obsolete stack label")
                        mutation_started = True
                        api.call(f"issues/{child.number}/labels/{BLOCK_LABEL}", "DELETE")
                        emit(pr=child.number, mutation="obsolete blocking label removed")
            except BudgetGap:
                raise
            except Exception as e:
                unknowns += 1
                failures += int(mutation_started)
                emit(pr=child.number, head=child.head, main=main_sha, classification="unknown", gap=str(e))
        emit(summary=True, selected=len(selected), failures=failures, unknowns=unknowns, api_calls=api.calls,
             api_bytes=api.bytes, git_operations=source.calls,
             elapsed_seconds=round(time.monotonic() - source.started, 3), mode="apply" if args.apply else "dry-run")
    return bool(failures)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        emit(classification="unknown", gap=str(error))
        sys.exit(1)
