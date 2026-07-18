#!/usr/bin/env python3
"""Advisory-only directory-structure nudge for PRs.

For each ``.lean`` file a PR **adds** under ``TauCeti/``, inspect the CamelCase
prefixes of its basename and report, as one advisory PR comment:

* an existing subdirectory the file could join (``Dir/Prefix/`` already exists);
* an existing flat filename family it extends: at least ``ADVISORY_MIN`` sibling
  files ``Dir/Prefix*.lean`` (token-boundary matched; an anchor module
  ``Dir/Prefix.lean`` is reported as supplementary evidence, never as a trigger
  by itself, since anchor-beside-extensions is the repo's blessed convention).
  Per the placement guidance, the expected response is a preliminary PR that
  relocates the family into its subdirectory, with the new file then added
  there.

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

ADVISORY_MIN = 4  # flat-family size that earns a mention; advisory only, tunable
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
    for k in range(1, len(toks)):  # nonempty remainder only: never the bare prefix
        prefix = "".join(toks[:k])
        subdir = any(t.startswith(f"{d}/{prefix}/") for t in tree)
        anchor = f"{d}/{prefix}.lean" in tree
        family = sorted(s for s in sib_stems if _boundary_extends(s, toks[:k]))
        # An anchor alone is the repo's blessed `Foo.lean`-beside-extensions
        # convention and is NOT a trigger; it is reported only as supplementary
        # evidence when a real trigger (subdirectory or family) fires.
        if subdir or len(family) >= ADVISORY_MIN:
            out.append({
                "prefix": prefix, "dir": d, "subdir": subdir, "anchor": anchor,
                "family_size": len(family), "examples": family[:3],
            })
    return out


def render_comment(head_sha: str, findings: dict[str, list[dict]]) -> str:
    lines = [MARKER, f"**Structure nudge** (advisory; analyzed head `{head_sha}`)", ""]
    lines.append(
        "This never blocks anything: ignore it freely when the flat name is right. "
        "It flags added files whose names sit next to an existing subdirectory or "
        "extend an existing flat filename family.")
    lines.append("")
    for path, cands in sorted(findings.items()):
        lines.append(f"* `{path}`")
        for c in cands:
            ev = []
            if c["subdir"]:
                ev.append(f"an existing subdirectory `{c['dir']}/{c['prefix']}/` "
                          "covers this topic; consider placing the file there")
            if c["anchor"]:
                ev.append(f"an anchor module `{c['dir']}/{c['prefix']}.lean` exists")
            if c["family_size"] >= ADVISORY_MIN:
                ex = ", ".join(f"`{e}`" for e in c["examples"])
                ev.append(f"{c['family_size']} sibling files share the `{c['prefix']}` "
                          f"prefix (e.g. {ex}); per the placement guidance, relocate "
                          f"first: a preliminary PR moving the family into "
                          f"`{c['dir']}/{c['prefix']}/` (keep any anchor in place, imports "
                          "only), then add this file there")
            lines.append(f"  * `{c['prefix']}`: " + "; ".join(ev) + ".")
    lines.append("")
    lines.append(f"Context and the current relocation queue: {TRACKING_ISSUE}.")
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
                + (f"+family({c['family_size']})" if c["family_size"] >= ADVISORY_MIN else "")
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
