"""Tests for scripts/bump_manifest.py, the whole-manifest check in check-bump.sh step 3."""

import copy
import unittest

from bump_manifest import problems

REV_OLD, REV_NEW = "a" * 40, "b" * 40


def dep(name, rev, inherited, **extra):
    entry = {"url": f"https://github.com/example/{name}", "type": "git", "subDir": None,
             "scope": "leanprover-community", "rev": rev, "name": name,
             "manifestFile": "lake-manifest.json", "inputRev": "main",
             "inherited": inherited, "configFile": "lakefile.toml"}
    entry.update(extra)
    return entry


def mathlib(rev):
    return {"url": "https://github.com/leanprover-community/mathlib4", "type": "git",
            "subDir": None, "scope": "", "rev": rev, "name": "mathlib",
            "manifestFile": "lake-manifest.json", "inputRev": "master", "inherited": False,
            "configFile": "lakefile.lean"}


def top(name, **extra):
    m = {"version": "1.2.0", "packagesDir": ".lake/packages", "name": name, "lakeDir": ".lake",
         "fixedToolchain": name == "mathlib"}
    m.update(extra)
    return m


def fixture():
    ml = dict(top("mathlib"), packages=[dep("batteries", "c" * 40, False),
                                        dep("Cli", "d" * 40, True)])
    base = dict(top("TauCeti"), packages=[mathlib(REV_OLD), dep("batteries", "e" * 40, True),
                                          dep("Cli", "f" * 40, True)])
    pr = dict(top("TauCeti"), packages=[mathlib(REV_NEW), dep("batteries", "c" * 40, True),
                                        dep("Cli", "d" * 40, True)])
    return pr, ml, base


class BumpManifestTest(unittest.TestCase):
    def assertRejected(self, pr, ml, base, fragment):
        found = problems(pr, ml, base)
        self.assertTrue(found, "expected a problem, got none")
        self.assertIn(fragment, " ".join(found))

    def test_genuine_bump_passes(self):
        self.assertEqual(problems(*fixture()), [])

    def test_manifest_format_version_may_follow_mathlib(self):
        pr, ml, base = fixture()
        ml["version"] = pr["version"] = "1.3.0"
        self.assertEqual(problems(pr, ml, base), [])
        pr["version"] = "9.9.9"
        self.assertRejected(pr, ml, base, "manifest version")

    def test_dependency_fields_beyond_the_old_four_are_compared(self):
        for field, value in (("subDir", "../../TauCeti"), ("configFile", "evil.lean"),
                             ("manifestFile", "../x.json"), ("scope", "someone-else")):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr["packages"][1][field] = value
                self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_dependency_must_be_inherited(self):
        pr, ml, base = fixture()
        pr["packages"][1]["inherited"] = False
        self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_extra_or_missing_dependency_fields_are_rejected(self):
        pr, ml, base = fixture()
        pr["packages"][2]["extra"] = 1
        self.assertRejected(pr, ml, base, "does not match mathlib@new")
        pr, ml, base = fixture()
        del pr["packages"][2]["scope"]
        self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_mathlib_entry_may_change_only_rev(self):
        for field, value in (("subDir", "x"), ("configFile", "lakefile.toml"),
                             ("manifestFile", "m.json"), ("scope", "s"), ("inherited", True),
                             ("url", "https://github.com/evil/mathlib4"), ("inputRev", "evil")):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr["packages"][0][field] = value
                self.assertRejected(pr, ml, base, "mathlib entry changes fields other than `rev`")

    def test_top_level_fields_must_equal_base(self):
        for field, value in (("packagesDir", "TauCeti/pkgs"), ("lakeDir", "TauCeti/lake"),
                             ("fixedToolchain", True), ("name", "other"), ("newField", 1)):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr[field] = value
                self.assertRejected(pr, ml, base, "top-level manifest fields differ from base")

    def test_package_set_must_match_mathlib(self):
        pr, ml, base = fixture()
        pr["packages"].append(dep("extra", "9" * 40, True))
        self.assertRejected(pr, ml, base, "does not depend on")
        pr, ml, base = fixture()
        del pr["packages"][2]
        self.assertRejected(pr, ml, base, "is missing deps")

    def test_shape_checks(self):
        pr, ml, base = fixture()
        pr["packages"].append(copy.deepcopy(pr["packages"][1]))
        self.assertRejected(pr, ml, base, "duplicate package names")
        pr, ml, base = fixture()
        pr["packages"][1]["type"] = "path"
        self.assertRejected(pr, ml, base, "non-git package")
        pr, ml, base = fixture()
        pr["packages"][1]["rev"] = "main"
        self.assertRejected(pr, ml, base, "40-hex")


if __name__ == "__main__":
    unittest.main()
