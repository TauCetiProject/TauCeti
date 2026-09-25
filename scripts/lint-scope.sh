#!/usr/bin/env bash
# lint-scope.sh OUT_DIR — decide what the environment lint (scripts/lint-env.sh) covers.
#
# Environment lint normally checks only the TauCeti modules a change touches: not the modules
# they import, and not the modules that import them. A change can still break lint elsewhere (a
# new simp lemma can take an existing one out of simp normal form); the daily full lint
# (.github/workflows/lint-full.yml) catches that and opens a repair PR on `lint-repair/main`.
#
# The whole library is linted when any PR in scope carries the `full-lint` label or is a repair PR
# (head branch `lint-repair/...`), or when the PRs in scope cannot be determined.
#
# Inputs (environment):
#   GH_TOKEN, REPO   GitHub API access and the repository
#   EVENT            pull_request_target | workflow_dispatch | merge_group | push
#   NUM              the PR number (pull_request_target, workflow_dispatch)
#   BASE, HEAD       commit SHAs whose diff is the change (merge_group, push)
# Output: if scoped, OUT_DIR/modules.txt lists the changed TauCeti modules (possibly none) and
# `LINT_ONLY_MODULES=OUT_DIR/modules.txt` is appended to $GITHUB_ENV; if not,
# `LINT_ONLY_MODULES=` is. It reads only GitHub API metadata, never candidate files.
set -euo pipefail

OUT_DIR="${1:?usage: lint-scope.sh OUT_DIR}"
mkdir -p "$OUT_DIR"
LIST="$OUT_DIR/modules.txt"
rm -f "$LIST"
: "${GITHUB_ENV:?GITHUB_ENV is required}"

full() {
  echo "lint-scope: linting the whole library: $1"
  echo "LINT_ONLY_MODULES=" >> "$GITHUB_ENV"
  exit 0
}

case "$EVENT" in
  pull_request_target|workflow_dispatch)
    [[ "${NUM:-}" =~ ^[0-9]+$ ]] || full "no PR number"
    prs="$NUM"
    files=$(gh api --paginate "repos/$REPO/pulls/$NUM/files?per_page=100" \
      --jq '.[] | [.status, .filename] | @tsv')
    ;;
  merge_group|push)
    [[ "${BASE:-}" =~ ^[0-9a-f]{40}$ && ! "$BASE" =~ ^0+$ ]] || full "no base commit"
    [[ "${HEAD:-}" =~ ^[0-9a-f]{40}$ ]] || full "no head commit"
    compare=$(gh api "repos/$REPO/compare/$BASE...$HEAD")
    # Each PR lands as one squashed commit titled `... (#N)`.
    prs=$(jq -r '.commits[].commit.message | split("\n")[0]' <<<"$compare" \
      | sed -nE 's/.*\(#([0-9]+)\)$/\1/p' | sort -u)
    ncommits=$(jq '.commits | length' <<<"$compare")
    nprs=$(grep -c . <<<"$prs" || true)
    [ "$nprs" -eq "$ncommits" ] || full "$ncommits commit(s) but $nprs PR number(s) in their titles"
    [ "$(jq '.files | length' <<<"$compare")" -lt 300 ] || full "the compare API's 300-file cap"
    files=$(jq -r '.files[] | [.status, .filename] | @tsv' <<<"$compare")
    ;;
  *) full "event $EVENT" ;;
esac

for pr in $prs; do
  info=$(gh api "repos/$REPO/pulls/$pr" --jq '[.head.ref, ([.labels[].name] | join(","))] | @tsv')
  IFS=$'\t' read -r head_ref labels <<<"$info"
  case "$head_ref" in lint-repair/*) full "#$pr is a lint repair PR ($head_ref)" ;; esac
  case ",$labels," in *,full-lint,*) full "#$pr is labelled full-lint" ;; esac
done

module_re="^TauCeti(/[A-Za-z_][A-Za-z0-9_']*)+\.lean$"
: > "$LIST"
while IFS=$'\t' read -r status file; do
  [ -n "${file:-}" ] || continue
  [ "$status" = removed ] && continue
  [[ "$file" =~ $module_re ]] || continue
  module="${file%.lean}"
  printf '%s\n' "${module//\//.}" >> "$LIST"
done <<<"$files"
LC_ALL=C sort -u -o "$LIST" "$LIST"
echo "lint-scope: linting the $(grep -c . "$LIST" || true) changed TauCeti module(s):"
sed 's/^/  /' "$LIST"
echo "LINT_ONLY_MODULES=$LIST" >> "$GITHUB_ENV"
