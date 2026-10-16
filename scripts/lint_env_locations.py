#!/usr/bin/env python3
"""Optional retry hints joined to the already validated NEW lint report.

No authority over lint status/baselines/nonces. Environment metadata and all
candidate process output remain untrusted. Failures produce explicit unknowns.
"""
import json
import re
import sys
from pathlib import Path

ORIGINS = "LINT-ENV-ORIGINS "
LOCATIONS = "LINT-ENV-LOCATIONS "
MAX_RECORDS = 128
MAX_LINE = 1024 * 1024
MODULE = re.compile(r"TauCeti(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate_key")
        result[key] = value
    return result


def source_location(record, root, modules):
    """Resolve only an exact imported module origin, never a declaration name."""
    if "unknown" in record:
        return {"unknown": "unsupported_origin"}
    module = record.get("module")
    line, column = record.get("line"), record.get("column")
    if (not isinstance(module, str) or not MODULE.fullmatch(module)
            or module not in modules or type(line) is not int or type(column) is not int
            or not 1 <= line <= 10_000_000 or not 1 <= column <= 10_000_000):
        return {"unknown": "invalid_origin"}
    path = module.replace(".", "/") + ".lean"
    if len(path) > 512:
        return {"unknown": "unsupported_path"}
    source = root / path
    # Do not follow symlinked components or accept paths outside the project.
    if any(p.is_symlink() for p in [source, *source.parents] if p != root.parent):
        return {"unknown": "invalid_path"}
    try:
        if not source.is_file() or not source.resolve().is_relative_to(root.resolve()):
            return {"unknown": "invalid_path"}
        # A range outside the candidate source is not a usable location. Source
        # contents are not searched for declaration names or ownership guesses.
        with source.open(encoding="utf-8") as stream:
            text = stream.read(MAX_LINE + 1)
        if len(text) > MAX_LINE:
            return {"unknown": "source_limit"}
        lines = text.splitlines()
        if line <= len(lines) and column <= len(lines[line - 1]) + 1:
            return {"path": path, "line": line, "column": column}
    except (OSError, UnicodeError):
        pass
    return {"unknown": "invalid_range"}


def locations(output, new, modules, root, expected):
    pairs = [line.split(" ", 1) for line in new.splitlines()]
    if len(pairs) > MAX_RECORDS:
        return {"version": 1, "complete": False, "findings": [], "unknown": "record_limit"}
    records = None
    try:
        envelopes = [line[len(ORIGINS):] for line in output.splitlines()
                     if line.startswith(ORIGINS)]
        if len(envelopes) != 1 or len(envelopes[0].encode()) > MAX_LINE:
            raise ValueError("ambiguous_or_large")
        envelope = json.loads(envelopes[0], object_pairs_hook=unique_object)
        records = envelope["records"]
        if (type(envelope.get("version")) is not int or envelope["version"] != 1
                or envelope.get("truncated") is not False
                or type(envelope.get("total")) is not int or envelope["total"] != expected
                or not isinstance(records, list) or len(records) != expected
                or len(records) > MAX_RECORDS or not all(isinstance(r, dict) for r in records)):
            records = None
    except (ValueError, KeyError, TypeError):
        records = None
    findings = []
    for linter, name in pairs:
        finding = {"linter": linter[:128], "declaration": name[:1024]}
        matches = [] if records is None else [r for r in records
                   if r.get("linter") == linter and r.get("report_name") == name]
        if len(matches) != 1:
            finding["unknown"] = "missing_or_ambiguous_record"
        else:
            record = matches[0]
            declaration = record.get("declaration")
            if not isinstance(declaration, str) or not 1 <= len(declaration) <= 1024:
                finding["unknown"] = "unsupported_name"
            else:
                finding["declaration"] = declaration
                finding.update(source_location(record, root, set(modules.splitlines())))
        findings.append(finding)
    return {"version": 1, "complete": True, "findings": findings}


def main():
    output, new, modules, root, expected = sys.argv[1:]
    try:
        result = locations(Path(output).read_text(), Path(new).read_text(),
                           Path(modules).read_text(), Path(root), int(expected))
    except (OSError, UnicodeError, ValueError, TypeError):
        result = {"version": 1, "complete": False, "findings": [], "unknown": "unavailable"}
    print(LOCATIONS + json.dumps(result, ensure_ascii=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
