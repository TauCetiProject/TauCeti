"""Whole-manifest check for a Mathlib bump, used by scripts/check-bump.sh (step 3).

check-bump.sh has already established that the PR's mathlib entry moves `rev` forward on the
nominated branch. This module checks that nothing ELSE in the PR's lake-manifest.json differs from
what that one fact determines:

* every top-level field (`name`, `packagesDir`, `lakeDir`, `fixedToolchain`, ...) equals the base
  manifest's, with the same set of keys, and the format `version` equals mathlib@new's (Lake decodes
  entries according to `version`, and the entries are mathlib@new's);
* the mathlib entry equals the base's mathlib entry in every field except `rev`;
* every other entry equals the same-named entry of mathlib's own manifest at the new rev in every
  field, except that `inherited` is `true` (Lake marks a dependency's dependencies as inherited
  when it writes a downstream manifest), and the two package sets are the same.

Comparing whole entries matters: Lake also reads `subDir`, `configFile`, `manifestFile` and
`scope` from these entries, and `packagesDir`/`lakeDir` from the top level, before any sandbox
runs. A four-field comparison would let a bump that passes every other check change them.

Usage: bump_manifest.py <pr-manifest> <mathlib-manifest-at-new-rev> <base-manifest>
Prints OK and exits 0, or prints the first problem and exits 1.
"""

import json
import re
import sys


def same(a, b) -> bool:
    """JSON equality that distinguishes types (Python's `==` has `True == 1` and `0 == False`)."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def differing(a: dict, b: dict, skip=()) -> list[str]:
    return [k for k in sorted(set(a) | set(b), key=str)
            if k not in skip and not same(a.get(k, ...), b.get(k, ...))]


def problems(pr: dict, ml: dict, base: dict) -> list[str]:
    out: list[str] = []
    for name, m in (("PR", pr), ("mathlib", ml), ("base", base)):
        if not isinstance(m, dict) or not isinstance(m.get("packages"), list):
            return [f"{name} manifest is not an object with a `packages` list"]
        if not all(isinstance(p, dict) for p in m["packages"]):
            return [f"{name} manifest has a package entry that is not an object"]
        names = [p.get("name") for p in m["packages"]]
        if not all(isinstance(n, str) and n for n in names):
            return [f"{name} manifest has a package without a string name"]
        dups = sorted({n for n in names if names.count(n) > 1})
        if dups:
            return [f"duplicate package names in {name} manifest: {dups}"]

    # `version` is the manifest format. Lake decodes every entry according to it, and the entries
    # are mathlib@new's, so it must be mathlib@new's. Every other top-level field equals base.
    changed = differing(pr, base, skip=("packages", "version"))
    if changed:
        out.append(f"top-level manifest fields differ from base: {changed}")
    if "version" not in pr or not same(pr.get("version"), ml.get("version")):
        out.append(f"manifest version {pr.get('version')!r} is not mathlib@new's "
                   f"({ml.get('version')!r})")

    for p in pr["packages"]:
        if p.get("type") != "git":
            out.append(f"PR pins non-git package {p.get('name')!r} (type {p.get('type')!r})")
        if not re.fullmatch(r"[0-9a-f]{40}", str(p.get("rev") or "")):
            out.append(f"PR dep {p.get('name')!r} rev is not a 40-hex commit SHA")
    if out:
        return out

    pr_by = {p["name"]: p for p in pr["packages"]}
    base_ml = [p for p in base["packages"] if p.get("name") == "mathlib"]
    if "mathlib" not in pr_by or len(base_ml) != 1:
        return out + ["expected exactly one `mathlib` package in both the PR and base manifests"]
    changed = differing(pr_by["mathlib"], base_ml[0], skip=("rev",))
    if changed:
        out.append(f"the mathlib entry changes fields other than `rev`: {changed}")

    deps = {n: p for n, p in pr_by.items() if n != "mathlib"}
    ml_by = {p.get("name"): p for p in ml["packages"]}
    only_pr, only_ml = sorted(set(deps) - set(ml_by)), sorted(set(ml_by) - set(deps))
    if only_pr:
        out.append(f"PR pins deps mathlib@new does not depend on: {only_pr}")
    if only_ml:
        out.append(f"PR is missing deps mathlib@new depends on: {only_ml}")
    for n in sorted(set(deps) & set(ml_by)):
        changed = differing(deps[n], dict(ml_by[n], inherited=True))
        if changed:
            out.append(f"dep {n!r} does not match mathlib@new's entry (fields {changed})")
    return out


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print(__doc__.strip().splitlines()[-3])
        return 2
    try:
        pr, ml, base = (json.load(open(path)) for path in argv[1:])
    except Exception as e:
        print(f"cannot parse manifest: {e}")
        return 1
    try:
        found = problems(pr, ml, base)
    except Exception as e:  # malformed input must fail closed with a message, not a traceback
        print(f"cannot validate manifest: {type(e).__name__}: {e}")
        return 1
    if found:
        print(found[0])
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
