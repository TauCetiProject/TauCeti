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
#   EVENT            pull_request_target | workflow_dispatch | merge_group | repository_dispatch | push
#   NUM              the PR number (pull_request_target, workflow_dispatch)
#   BASE, HEAD       commit SHAs whose three-dot diff is the change: for a PR its base commit and
#                    the exact head being built, so the scope is bound to that immutable commit
#   HEAD_REPO        for a PR, the head repository (owner/name), which may be a fork
#   SCOPE_REPO       exact candidate checkout, with its .git/objects available locally
# Output: if scoped, OUT_DIR/modules.txt lists the changed TauCeti modules (possibly none) and
# `LINT_ONLY_MODULES=OUT_DIR/modules.txt` is appended to $GITHUB_ENV; if not,
# `LINT_ONLY_MODULES=` is. OUT_DIR/unmatched.txt lists every changed `.lean` file that is not one of
# those modules (the root file, a name outside the module pattern such as a non-ASCII one): the lint
# can ignore them, but a check that must see every changed declaration (the axiom audit) cannot, and
# falls back to the whole library when this file is non-empty. It reads GitHub metadata and
# immutable local Git objects through trusted tooling; never candidate code or Git configuration.
set -euo pipefail

OUT_DIR="${1:?usage: lint-scope.sh OUT_DIR}"
mkdir -p "$OUT_DIR"
LIST="$OUT_DIR/modules.txt"
UNMATCHED="$OUT_DIR/unmatched.txt"
rm -f "$LIST" "$UNMATCHED"
: "${GITHUB_ENV:?GITHUB_ENV is required}"

full() {
  echo "lint-scope: linting the whole library: $1"
  echo "LINT_ONLY_MODULES=" >> "$GITHUB_ENV"
  exit 0
}

case "$EVENT" in
  pull_request_target|workflow_dispatch)
    [[ "${NUM:-}" =~ ^[0-9]+$ ]] || full "no PR number"
    [[ "${BASE:-}" =~ ^[0-9a-f]{40}$ ]] || full "no base commit"
    [[ "${HEAD:-}" =~ ^[0-9a-f]{40}$ ]] || full "no head commit"
    [[ "${HEAD_REPO:-}" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] || full "no head repository"
    prs="$NUM"
    # Compare the exact commits being built, not the PR's current file list, which can describe a
    # different head (a push while queued) or base (a retarget).
    if ! compare=$(gh api "repos/$REPO/compare/$BASE...${HEAD_REPO%%/*}:$HEAD"); then
      full "the immutable compare metadata is unavailable"
    fi
    ;;
  merge_group|repository_dispatch|push)
    [[ "${BASE:-}" =~ ^[0-9a-f]{40}$ && ! "$BASE" =~ ^0+$ ]] || full "no base commit"
    [[ "${HEAD:-}" =~ ^[0-9a-f]{40}$ ]] || full "no head commit"
    if ! compare=$(gh api "repos/$REPO/compare/$BASE...$HEAD"); then
      full "the immutable compare metadata is unavailable"
    fi
    # GitHub merge groups and bors staging both use one squash commit per PR,
    # titled `... (#N)`. The trusted workflow validates bors staging and its
    # immutable base/head before calling this script. Unknown titles stay full lint.
    prs=$(jq -r '.commits[].commit.message | split("\n")[0]' <<<"$compare" \
      | sed -nE 's/.*\(#([0-9]+)\)$/\1/p' | sort -u)
    ncommits=$(jq '.commits | length' <<<"$compare")
    [ "$(jq '.total_commits' <<<"$compare")" = "$ncommits" ] || full "the compare API truncated the commit list"
    nprs=$(grep -c . <<<"$prs" || true)
    [ "$nprs" -eq "$ncommits" ] || full "$ncommits commit(s) but $nprs PR number(s) in their titles"
    ;;
  *) full "event $EVENT" ;;
esac

for pr in $prs; do
  if ! info=$(gh api "repos/$REPO/pulls/$pr" --jq '[.head.ref, ([.labels[].name] | join(","))] | @tsv'); then
    full "PR #$pr lint policy metadata is unavailable"
  fi
  IFS=$'\t' read -r head_ref labels <<<"$info"
  case "$head_ref" in lint-repair/*) full "#$pr is a lint repair PR ($head_ref)" ;; esac
  case ",$labels," in *,full-lint,*) full "#$pr is labelled full-lint" ;; esac
done

# GitHub's file list stops at 300 entries; use only its immutable merge-base
# metadata. The full local tree diff has no such cap. Do not consult live PR files.
merge_base=$(jq -r '.merge_base_commit.sha // empty' <<<"$compare")
[[ "$merge_base" =~ ^[0-9a-f]{40}$ ]] || full "no exact merge base"
[ -n "${SCOPE_REPO:-}" ] || full "no local candidate checkout"
tool_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
if ! python3 "$tool_dir/lint_scope_files.py" "$SCOPE_REPO" "$merge_base" "$HEAD" \
    > "$OUT_DIR/files.nul"; then
  full "the immutable local diff is unavailable"
fi

module_re="^TauCeti(/[A-Za-z_][A-Za-z0-9_']*)+\.lean$"
: > "$LIST"
: > "$UNMATCHED"
while IFS= read -r -d '' file; do
  # A deleted file has nothing left to lint or audit, so it is not listed. What its deletion can do
  # to other files is covered elsewhere: a module that imported it changes too (or the build
  # fails), so it is listed; and a namespace-owning type it declared is seen by the dot-notation
  # lint, which compares ownership against the merge base (`--base-source-root`) and lints every
  # file when ownership differs.
  if ! [[ "$file" =~ $module_re ]]; then
    [[ "$file" == *.lean ]] && printf '%s\n' "$file" >> "$UNMATCHED"
    continue
  fi
  module="${file%.lean}"
  printf '%s\n' "${module//\//.}" >> "$LIST"
done < "$OUT_DIR/files.nul"
LC_ALL=C sort -u -o "$LIST" "$LIST"
echo "lint-scope: linting the $(grep -c . "$LIST" || true) changed TauCeti module(s):"
sed 's/^/  /' "$LIST"
echo "LINT_ONLY_MODULES=$LIST" >> "$GITHUB_ENV"
