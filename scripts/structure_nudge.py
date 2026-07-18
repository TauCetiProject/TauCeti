#!/usr/bin/env python3
"""Advisory-only directory-structure nudge for PRs.

For each ``.lean`` file a PR **adds** under ``TauCeti/``, inspect the CamelCase
prefixes of its basename and report, as one advisory PR comment:

* an existing subdirectory the file could join (``Dir/Prefix/`` already exists);
* any sibling sharing a CamelCase prefix with it, at token boundaries: two files
  sharing a prefix are already a directory, so ``Dir/Prefix.lean`` plus
  ``Dir/PrefixBar.lean`` triggers, in either order, as do two extensions. Per
  the placement guidance, the same PR creates ``Dir/Prefix/``, with
  ``Prefix.lean`` becoming ``Prefix/Basic.lean`` (or ``Prefix/Defs.lean`` when
  definitions-only) and each ``PrefixBar.lean`` becoming ``Prefix/Bar.lean``,
  and places the new file there: move as you add.

This check is advisory by construction: findings exit ``0``, every failure is
downgraded to a ``::warning::`` annotation and exit ``0``, and the workflow step
that runs it is ``continue-on-error``. It must never feed the ``build`` commit
status.

Tokenizer (the formal spec; see the tests for the fixture set): a basename splits
into the tokens matched left to right by

    [A-Z]{2,}(?![a-z]) | [A-Z][a-z0-9]* | [a-z0-9]+

that is, a maximal acronym run (two or more capitals) not followed by a
lowercase letter, a capitalized
word with optional trailing digits, or a bare lowercase/digit run. Examples:
``JHolomorphic`` -> ``J·Holomorphic``, ``NNReal`` -> ``NN·Real``, ``L2Norm`` ->
``L2·Norm``, ``pAdic`` -> ``p·Adic``, ``CStarAlgebra`` -> ``C·Star·Algebra``.

The candidate report deliberately does NOT auto-select the longest matching
prefix: every qualifying prefix is listed with its evidence, and choosing the
right family boundary is left to humans and the placement rubric.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

MARKER = "<!--structure:nudge-->"
TRACKING_ISSUE = "https://github.com/TauCetiProject/TauCeti/issues/987"

_TOKEN_RE = re.compile(r"[A-Z]{2,}(?![a-z])|[A-Z][a-z0-9]*|[a-z0-9]+")


def tokenize(base: str) -> list[str]:
    """Split a file basename (no extension) into CamelCase tokens."""
    return _TOKEN_RE.findall(base)


def _boundary_extends(base: str, prefix_tokens: list[str]) -> bool:
    """Does `base` tokenize to a strict extension of `prefix_tokens`?"""
    toks = tokenize(base)
    k = len(prefix_tokens)
    return len(toks) > k and toks[:k] == prefix_tokens


def candidates_for(path: str, tree: set[str]) -> list[dict]:
    """Structure candidates for one added file against a tree of repo paths.

    `path` is repo-relative (``TauCeti/Dir/Name.lean``); `tree` contains every
    ``.lean`` path that exists alongside it (the base branch plus any other
    files added by the same PR, but not `path` itself).
    """
    p = pathlib.PurePosixPath(path)
    if p.suffix != ".lean" or not str(p).startswith("TauCeti/"):
        return []
    d = str(p.parent)
    base = p.stem
    toks = tokenize(base)
    sib_stems = {pathlib.PurePosixPath(t).stem for t in tree
                 if str(pathlib.PurePosixPath(t).parent) == d and t != path}
    out: list[dict] = []
    # k < len(toks): the added file extends the prefix (it is a `FooBar.lean`).
    # k == len(toks): the added file IS the prefix of existing extensions (it
    # is the `Foo.lean` of an existing `Foo*` family).
    for k in range(1, len(toks) + 1):
        prefix = "".join(toks[:k])
        subdir = any(t.startswith(f"{d}/{prefix}/") for t in tree)
        anchor = k < len(toks) and f"{d}/{prefix}.lean" in tree
        family = sorted(s for s in sib_stems if _boundary_extends(s, toks[:k]))
        if k == len(toks) and not (family or subdir):
            continue  # a bare name extending nothing is just a file
        if subdir or anchor or family:
            out.append({
                "prefix": prefix, "dir": d, "subdir": subdir, "anchor": anchor,
                "family_size": len(family), "examples": family[:3],
                "is_prefix_of_family": k == len(toks),
            })
    return out


def render_comment(head_sha: str, findings: dict[str, list[dict]]) -> str:
    lines = [MARKER, f"**Structure nudge** (advisory; analyzed head `{head_sha}`)", ""]
    lines.append(
        "This never blocks anything. It flags added files that belong in a topic "
        "subdirectory: two files sharing a CamelCase prefix are already a directory.")
    lines.append("")
    for path, cands in sorted(findings.items()):
        lines.append(f"* `{path}`")
        for c in cands:
            loc = f"`{c['dir']}/{c['prefix']}/`"
            if c["subdir"]:
                lines.append(f"  * `{c['prefix']}`: the subdirectory {loc} already "
                             "exists; place the file there.")
                continue
            ex = ", ".join(f"`{e}`" for e in c["examples"])
            if c["is_prefix_of_family"]:
                lines.append(
                    f"  * `{c['prefix']}`: existing files extend this name ({ex}); per "
                    f"the placement guidance, move as you add: in this PR create "
                    f"{loc} (each `{c['prefix']}Bar.lean` becomes `{c['prefix']}/Bar.lean`) "
                    f"and place this file there as `{c['prefix']}/Basic.lean` or "
                    f"`{c['prefix']}/Defs.lean`.")
            else:
                have = (f"`{c['prefix']}.lean`" + (f", {ex}" if ex else "")) if c["anchor"] else ex
                lines.append(
                    f"  * `{c['prefix']}`: shares the `{c['prefix']}` prefix with {have}; "
                    f"per the placement guidance, move as you add: in this PR create "
                    f"{loc} (`{c['prefix']}.lean` becomes `{c['prefix']}/Basic.lean` "
                    f"or `{c['prefix']}/Defs.lean`; each `{c['prefix']}Bar.lean` becomes "
                    f"`{c['prefix']}/Bar.lean`) and place this file there.")
    lines.append("")
    lines.append(f"Policy and context: {TRACKING_ISSUE}.")
    return "\n".join(lines)


def _gh_json(args: list[str]):
    return json.loads(subprocess.run(["gh"] + args, check=True,
                                     capture_output=True, text=True).stdout)


def _local_tree() -> set[str]:
    out = subprocess.run(["git", "ls-files", "TauCeti/**/*.lean", "TauCeti/*.lean"],
                         check=True, capture_output=True, text=True).stdout
    return {l for l in out.splitlines() if l.endswith(".lean")}


def run_pr(repo: str, pr: int, apply: bool) -> int:
    info = _gh_json(["api", f"repos/{repo}/pulls/{pr}",
                     "--jq", "{head: .head.sha}"])
    files = _gh_json(["api", "--paginate", f"repos/{repo}/pulls/{pr}/files?per_page=100",
                      "--jq", "[.[] | select(.status == \"added\") | .filename]"])
    added = [f for f in files if f.endswith(".lean") and f.startswith("TauCeti/")]
    tree = _local_tree() | set(added)
    findings = {}
    for f in added:
        cands = candidates_for(f, tree - {f})
        if cands:
            findings[f] = cands
    if not findings:
        print(f"structure-nudge: PR #{pr}: no findings")
        # An earlier comment may be stale (files since removed from the diff):
        # leave it in place; it names the head SHA it analyzed.
        return 0
    body = render_comment(info["head"], findings)
    if not apply:
        print(body)
        return 0
    comments = _gh_json(["api", "--paginate",
                         f"repos/{repo}/issues/{pr}/comments?per_page=100",
                         "--jq", "[.[] | {id: .id, body: .body}]"])
    prev = next((c["id"] for c in comments if MARKER in (c["body"] or "")), None)
    if prev is not None:
        subprocess.run(["gh", "api", "-X", "PATCH",
                        f"repos/{repo}/issues/comments/{prev}", "-f", f"body={body}"],
                       check=True, capture_output=True, text=True)
        print(f"structure-nudge: PR #{pr}: updated comment {prev}")
    else:
        subprocess.run(["gh", "api", f"repos/{repo}/issues/{pr}/comments",
                        "-f", f"body={body}"],
                       check=True, capture_output=True, text=True)
        print(f"structure-nudge: PR #{pr}: posted comment")
    return 0


def run_tree_dry_run() -> int:
    """Treat every existing file as freshly added: the whole-tree false-positive
    surface, checked in as a reviewable snapshot (regenerate with this flag)."""
    tree = _local_tree()
    n = 0
    for f in sorted(tree):
        cands = candidates_for(f, tree - {f})
        for c in cands:
            n += 1
            ev = ("subdir" if c["subdir"] else "") + ("+anchor" if c["anchor"] else "") \
                + (f"+family({c['family_size']})" if c["family_size"] else "") \
                + ("+isprefix" if c["is_prefix_of_family"] else "")
            print(f"{f}: {c['prefix']} [{ev.lstrip('+')}]")
    print(f"-- {n} candidate line(s) over {len(tree)} files")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Advisory structure nudge for PRs.")
    ap.add_argument("--repo", default="TauCetiProject/TauCeti")
    ap.add_argument("--pr", type=int, help="analyze a single PR")
    ap.add_argument("--apply", action="store_true",
                    help="post/update the advisory comment (otherwise print it)")
    ap.add_argument("--tree-dry-run", action="store_true",
                    help="report over every existing file (snapshot mode)")
    args = ap.parse_args(argv)
    try:
        if args.tree_dry_run:
            return run_tree_dry_run()
        if args.pr is None:
            ap.error("--pr or --tree-dry-run required")
        return run_pr(args.repo, args.pr, args.apply)
    except Exception as e:  # advisory: never fail the job
        print(f"::warning::structure-nudge failed harmlessly: {e}")
        return 0


if __name__ == "__main__":
    sys.exit(main())
