"""Origin validation and the existing shell audit's independent verdict boundary."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

SCRIPTS = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("locations", SCRIPTS / "lint_env_locations.py")
locations = importlib.util.module_from_spec(spec)
spec.loader.exec_module(locations)


class LocationsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "TauCeti").mkdir()
        (self.root / "TauCeti/Probe.lean").write_text("theorem Probe := trivial\n")
        self.record = dict(linter="simpNF", declaration="TauCeti.Probe", report_name="TauCeti.Probe",
                           module="TauCeti.Probe", line=1, column=9)

    def emit(self, records=None, new="simpNF TauCeti.Probe\n", **changes):
        records = [self.record] if records is None else records
        envelope = dict(version=1, total=len(records), truncated=False, records=records)
        envelope.update(changes)
        output = locations.ORIGINS + json.dumps(envelope)
        return locations.locations(output, new, "TauCeti.Probe\n", self.root, len(records))

    def test_only_validated_new_pairs_get_locations(self):
        other = {**self.record, "declaration": "TauCeti.Old", "report_name": "TauCeti.Old"}
        result = self.emit([self.record, other])
        self.assertEqual(result["findings"], [dict(linter="simpNF", declaration="TauCeti.Probe",
                          path="TauCeti/Probe.lean", line=1, column=9)])
        self.assertEqual(self.emit(new="")["findings"], [])

    def test_escaped_unicode_names_do_not_determine_source(self):
        for name in ["TauCeti.λ雪", 'TauCeti.«quoted.name»', 'TauCeti.«a\\b"c»']:
            with self.subTest(name=name):
                record = {**self.record, "declaration": name, "report_name": name}
                result = self.emit([record], f"simpNF {name}\n")
                self.assertEqual(result["findings"][0]["path"], "TauCeti/Probe.lean")
                self.assertEqual(result["findings"][0]["declaration"], name)

    def test_private_generated_missing_ambiguous_or_unsupported_stay_unknown(self):
        for reason in ["private_or_generated", "missing_origin", "missing_range", "unsupported_module"]:
            result = self.emit([{**self.record, "unknown": reason}])
            self.assertNotIn("path", result["findings"][0])
        self.assertNotIn("path", self.emit([self.record, self.record])["findings"][0])
        self.assertNotIn("path", self.emit([{"unknown": "unsupported_name"}])["findings"][0])

    def test_external_traversal_missing_source_symlink_and_bad_ranges(self):
        for change in [dict(module="Mathlib.Probe"), dict(module="TauCeti.Other"),
                       dict(module="TauCeti...Probe"), dict(module="TauCeti./Probe"),
                       dict(line=0), dict(line=True), dict(line=2), dict(column=9999)]:
            self.assertNotIn("path", self.emit([{**self.record, **change}])["findings"][0])
        source = self.root / "TauCeti/Probe.lean"
        source.unlink()
        self.assertNotIn("path", self.emit()["findings"][0])
        source.symlink_to(SCRIPTS / "LintEnvDriver.lean")
        self.assertNotIn("path", self.emit()["findings"][0])

    def test_forged_duplicate_malformed_truncated_and_oversized_evidence(self):
        valid = locations.ORIGINS + json.dumps(dict(version=1, total=1, truncated=False,
                                                    records=[self.record]))
        for output in ["", valid + "\n" + valid, locations.ORIGINS + "{", valid[:-5],
                       valid.replace('"version": 1', '"version": 1, "version": 1'),
                       locations.ORIGINS + "x" * (locations.MAX_LINE + 1)]:
            result = locations.locations(output, "simpNF TauCeti.Probe\n", "TauCeti.Probe\n",
                                         self.root, 1)
            self.assertNotIn("path", result["findings"][0])
        self.assertNotIn("path", self.emit(truncated=True)["findings"][0])
        self.assertNotIn("path", self.emit(total=2)["findings"][0])
        self.assertNotIn("path", self.emit(version=True)["findings"][0])
        self.assertFalse(self.emit(new="simpNF TauCeti.Probe\n" * 129)["complete"])


class AuditVerdictTest(unittest.TestCase):
    """Run the real shell parser/ratchets; substitute only Lean process output."""
    def audit(self, mode="failure", baseline="", origins="normal"):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "TauCeti").mkdir()
            (root / "TauCeti/Probe.lean").write_text("theorem Probe := trivial\n")
            trusted = root / "trusted"
            trusted.mkdir()
            for filename in ["lint-env.sh", "source-modules.sh", "lint_env_locations.py"]:
                (trusted / filename).symlink_to(SCRIPTS / filename)
            (trusted / "lint-baseline.txt").write_text(baseline)
            (trusted / "lint-nolints-allowlist.txt").write_text("")
            binary = root / "bin"
            binary.mkdir()
            lake = binary / "lake"
            lake.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
                import os, pathlib, re, sys
                if sys.argv[2] != 'lean':
                    os.execv(sys.argv[2], sys.argv[2:])
                source = pathlib.Path(sys.argv[-1]).read_text()
                marker = re.search(r'DOCSCAN-COMPLETE-[a-f0-9]+', source)[0]
                linter = re.search(r'LINTERSET-COMPLETE-[a-f0-9]+', source)[0]
                names = ['TauCeti.GridDiagram.OSet', 'TauCeti.Isotopy',
                         'TauCeti.AlgebraicGeometry.WeilDivisor.coeff']
                names += [f'TauCeti.documented{i}' for i in range(497)]
                print('LINTERSET base ' + linter)
                for name in names:
                    print('DOCSCAN-ALL ' + name + ' documented')
                print('DOCSCAN-SUMMARY scanned=500 documented=500 undocumented=0 nolints=0 ' + marker)
                '''))
            lake.chmod(0o755)
            driver = binary / "driver"
            driver.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
                import json, os, pathlib, sys
                tag, marker, modules, *linters = sys.argv[1:]
                failed = os.environ['FIXTURE_MODE'] != 'pass'
                envelope = dict(version=1, total=int(failed), truncated=False, records=[])
                if failed:
                    envelope['records'] = [dict(linter='simpNF', declaration='TauCeti.Probe',
                        report_name='TauCeti.Probe', module='TauCeti.Probe', line=1, column=9)]
                record = 'LINT-ENV-ORIGINS ' + json.dumps(envelope)
                if os.environ['FIXTURE_ORIGINS'] == 'duplicate':
                    print(record)
                print(record if os.environ['FIXTURE_ORIGINS'] != 'malformed' else 'LINT-ENV-ORIGINS {')
                header = f'-- Found {int(failed)} errors in 1 declarations (plus 0 automatically generated ones) in TauCeti with {len(linters)} linters'
                print((tag + ':1:0: error: ' if failed else '') + header)
                if failed:
                    print('/- The `simpNF` linter reports: -/')
                    print('#check @TauCeti.Probe /- Left-hand side simplifies -/')
                if os.environ['FIXTURE_MODE'] == 'forged_header':
                    print(header)
                if os.environ['FIXTURE_MODE'] != 'missing_nonce':
                    print(pathlib.Path(marker).read_text().strip())
                sys.exit(int(failed))
                '''))
            driver.chmod(0o755)
            result = subprocess.run(["bash", str(trusted / "lint-env.sh")], text=True,
                capture_output=True, env={**os.environ, "PATH": f"{binary}:{os.environ['PATH']}",
                "TAUCETI_PROJECT_ROOT": str(root), "TAUCETI_TRUSTED_SCRIPTS": str(trusted),
                "WATCHDOG_TOOLCHAIN": "", "LINT_ONLY_MODULES": "",
                "LINT_DRIVER_EXE": str(driver), "FIXTURE_MODE": mode, "FIXTURE_ORIGINS": origins})
            return result

    def test_pass_baseline_and_ratchet_verdicts_unchanged(self):
        for mode, baseline, expected in [("pass", "", 0), ("failure", "simpNF TauCeti.Probe\n", 0),
                                         ("pass", "simpNF TauCeti.Old\n", 0)]:
            result = self.audit(mode, baseline)
            self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            self.assertNotIn(locations.LOCATIONS, result.stdout)
            if "Old" in baseline:
                self.assertIn("RATCHET", result.stdout)

    def test_new_failure_gets_hint_but_invalid_origins_cannot_change_verdict(self):
        for origin in ["normal", "duplicate", "malformed"]:
            result = self.audit(origins=origin)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("1 new violation(s)", result.stdout)
            line = next(l for l in result.stdout.splitlines() if l.startswith(locations.LOCATIONS))
            finding = json.loads(line[len(locations.LOCATIONS):])["findings"][0]
            self.assertEqual("path" in finding, origin == "normal")

    def test_nonce_and_report_forgery_fail_before_locations(self):
        for mode in ["missing_nonce", "forged_header"]:
            result = self.audit(mode)
            self.assertEqual(result.returncode, 1)
            self.assertNotIn(locations.LOCATIONS, result.stdout)
            self.assertIn("driver/linter failure", result.stdout)


if __name__ == "__main__":
    unittest.main()
