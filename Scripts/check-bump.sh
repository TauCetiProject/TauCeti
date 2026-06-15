#!/usr/bin/env bash
# check-bump.sh — validate that a PR's proposed Lake-pin / toolchain change is a
# safe, machine-checkable *forward* bump, and nothing else.
#
# This is the trust anchor that lets a PR touching `lake-manifest.json` and/or
# `lean-toolchain` (but NOT the lakefile) be built and auto-merged without a human:
# the worry is a PR that re-points a dependency at a malicious fork/commit or a
# malicious toolchain and then gets auto-built. We reduce the whole manifest to a
# deterministic function of one validated fact — "mathlib moved forward on the
# branch nominated in lakefile.toml" — and require the toolchain to move forward
# and match mathlib's:
#
#   1. lakefile.toml / lakefile.lean are byte-identical to base (lakefile edits
#      stay human-owned; they change which branch/dep is even nominated).
#   2. The nominated require (mathlib) keeps its url + inputRev (master), and its
#      new rev is a *descendant of the old rev* AND *on inputRev's history* — a
#      genuine forward move on the nominated branch (via the GitHub compare API).
#   3. Every other git pin equals mathlib's OWN lake-manifest at the new rev, so
#      transitive deps can't be re-pointed independently of the trusted mathlib.
#   4. lean-toolchain moves monotonically forward on the leanprover/lean4 channel
#      AND equals mathlib's lean-toolchain at the new rev.
#
# It does NO build and runs NONE of the PR's code — only reads/parses two text
# files and queries the trusted upstream via `gh api`. Usage:
#
#   check-bump.sh <base_dir> <pr_dir>
#
# where each dir holds the repo's lean-toolchain, lake-manifest.json, lakefile.toml
# (and optionally lakefile.lean). Exit 0 = safe forward bump (or no pin change);
# exit 1 = not auto-mergeable (route to a human). Reasons are printed.
set -uo pipefail

BASE="${1:?usage: check-bump.sh <base_dir> <pr_dir>}"
PR="${2:?usage: check-bump.sh <base_dir> <pr_dir>}"

fail() { echo "::error::bump-guard: $*"; echo "BUMP-GUARD: FAIL — $*"; exit 1; }
ok()   { echo "BUMP-GUARD: PASS — $*"; exit 0; }

# --- 1. lakefile is human-owned: it must not change ---------------------------
for f in lakefile.toml lakefile.lean; do
  b="$BASE/$f"; p="$PR/$f"
  # Treat an absent file the same on both sides; a file appearing/vanishing is a change.
  [ -f "$b" ] || b=/dev/null
  [ -f "$p" ] || p=/dev/null
  if ! diff -q "$b" "$p" >/dev/null 2>&1; then
    fail "$f differs from base — lakefile edits are human-owned and never auto-merge"
  fi
done

# --- helpers ------------------------------------------------------------------
# Emit "name<TAB>url<TAB>rev<TAB>inputRev" for every git package in a manifest.
manifest_git() {
  python3 - "$1" <<'PY'
import json,sys
m=json.load(open(sys.argv[1]))
for p in m.get("packages",[]):
    if p.get("type")=="git":
        print("\t".join([p.get("name",""),
                         (p.get("url") or "").rstrip("/").removesuffix(".git"),
                         p.get("rev",""), p.get("inputRev") or ""]))
PY
}
# owner/repo slug from a github url
slug() { sed -E 's#^https?://github.com/##; s#/$##; s#\.git$##' <<<"$1"; }

BASE_GIT="$(manifest_git "$BASE/lake-manifest.json")" || fail "cannot parse base lake-manifest.json"
PR_GIT="$(manifest_git "$PR/lake-manifest.json")"     || fail "cannot parse PR lake-manifest.json"

# --- locate mathlib in both manifests -----------------------------------------
ml_base="$(awk -F'\t' '$1=="mathlib"{print; exit}' <<<"$BASE_GIT")"
ml_pr="$(awk   -F'\t' '$1=="mathlib"{print; exit}' <<<"$PR_GIT")"
[ -n "$ml_base" ] || fail "no mathlib git package in base manifest"
[ -n "$ml_pr" ]   || fail "no mathlib git package in PR manifest"
IFS=$'\t' read -r _ ML_URL_B ML_REV_B ML_IR_B <<<"$ml_base"
IFS=$'\t' read -r _ ML_URL_P ML_REV_P ML_IR_P <<<"$ml_pr"

[ "$ML_URL_B" = "$ML_URL_P" ] || fail "mathlib url changed ($ML_URL_B -> $ML_URL_P) — repo swap is human-owned"
[ "$ML_IR_B"  = "$ML_IR_P"  ] || fail "mathlib inputRev (nominated branch) changed ($ML_IR_B -> $ML_IR_P) — human-owned"
ML_SLUG="$(slug "$ML_URL_P")"

# --- 2. mathlib moved forward on the nominated branch -------------------------
if [ "$ML_REV_B" = "$ML_REV_P" ]; then
  # mathlib pin unchanged: then NOTHING in the manifest may change (the rest is derived from it).
  if [ "$BASE_GIT" != "$PR_GIT" ]; then
    fail "mathlib rev unchanged but other manifest pins changed — not a derived bump"
  fi
  echo "bump-guard: mathlib pin unchanged."
else
  st_fwd="$(gh api "repos/$ML_SLUG/compare/$ML_REV_B...$ML_REV_P" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $ML_SLUG $ML_REV_B...$ML_REV_P"
  case "$st_fwd" in
    ahead) : ;;  # new strictly descends from old — forward
    *) fail "mathlib rev is not a forward move from base (compare status: ${st_fwd:-unknown}); old=$ML_REV_B new=$ML_REV_P" ;;
  esac
  st_branch="$(gh api "repos/$ML_SLUG/compare/$ML_REV_P...$ML_IR_P" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $ML_SLUG $ML_REV_P...$ML_IR_P"
  case "$st_branch" in
    ahead|identical) : ;;  # the nominated branch tip is at-or-ahead of new — new is on its history
    *) fail "mathlib new rev $ML_REV_P is not on branch '$ML_IR_P' (compare status: ${st_branch:-unknown})" ;;
  esac
  echo "bump-guard: mathlib $ML_REV_B -> $ML_REV_P is a forward move on '$ML_IR_P'."
fi

# --- 3. every other pin equals mathlib's own manifest at the new rev ----------
ML_MANIFEST="$(gh api "repos/$ML_SLUG/contents/lake-manifest.json?ref=$ML_REV_P" --jq '.content' 2>/dev/null | base64 -d)" \
  || fail "cannot fetch mathlib lake-manifest.json at $ML_REV_P"
ML_GIT="$(manifest_git <(printf '%s' "$ML_MANIFEST"))" || fail "cannot parse mathlib manifest at $ML_REV_P"

while IFS=$'\t' read -r name url rev inputrev; do
  [ -z "$name" ] && continue
  [ "$name" = "mathlib" ] && continue
  ml_line="$(awk -F'\t' -v n="$name" '$1==n{print; exit}' <<<"$ML_GIT")"
  [ -n "$ml_line" ] || fail "PR pins git dep '$name' that mathlib@$ML_REV_P does not depend on"
  IFS=$'\t' read -r _ m_url m_rev _ <<<"$ml_line"
  [ "$url" = "$m_url" ] || fail "dep '$name' url ($url) != mathlib's ($m_url) — not a derived pin"
  [ "$rev" = "$m_rev" ] || fail "dep '$name' rev ($rev) != mathlib@$ML_REV_P's ($m_rev) — not a derived pin"
done <<<"$PR_GIT"
echo "bump-guard: all transitive pins match mathlib@$ML_REV_P."

# --- 4. toolchain: monotonic forward AND consistent with mathlib --------------
TC_B="$(tr -d '[:space:]' <"$BASE/lean-toolchain" 2>/dev/null)"
TC_P="$(tr -d '[:space:]' <"$PR/lean-toolchain" 2>/dev/null)"
[ -n "$TC_B" ] || fail "cannot read base lean-toolchain"
[ -n "$TC_P" ] || fail "cannot read PR lean-toolchain"

if [ "$TC_B" != "$TC_P" ]; then
  python3 - "$TC_B" "$TC_P" <<'PY' || exit 1
import re,sys
def parse(t):
    m=re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", t)
    if not m: sys.exit(f"BUMP-GUARD: FAIL — toolchain '{t}' is not a leanprover/lean4 vX.Y.Z[-rcN] release")
    x,y,z,rc=m.groups()
    # a final release outranks any rc of the same X.Y.Z
    return (int(x),int(y),int(z), int(rc) if rc is not None else float("inf"))
b,p=parse(sys.argv[1]),parse(sys.argv[2])
if p < b: sys.exit(f"BUMP-GUARD: FAIL — toolchain moved backward ({sys.argv[1]} -> {sys.argv[2]})")
PY
fi

ML_TC="$(gh api "repos/$ML_SLUG/contents/lean-toolchain?ref=$ML_REV_P" --jq '.content' 2>/dev/null | base64 -d | tr -d '[:space:]')" \
  || fail "cannot fetch mathlib lean-toolchain at $ML_REV_P"
[ "$TC_P" = "$ML_TC" ] || fail "PR lean-toolchain ($TC_P) != mathlib@$ML_REV_P's ($ML_TC)"
echo "bump-guard: toolchain $TC_B -> $TC_P is forward and matches mathlib@$ML_REV_P."

ok "forward-only bump validated (mathlib on '$ML_IR_P', derived transitive pins, toolchain consistent)"
