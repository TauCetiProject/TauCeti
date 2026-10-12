"""Regression checks for how the environment-lint driver is built and handed to the sandbox.

The driver runs trusted code inside the PR sandbox, so it must be built only from trusted inputs:
on the host, before any candidate code runs, without reading the Lake artifact cache, and mounted
read-only. See scripts/build-lint-driver.sh and scripts/lint-env.sh.
"""

import pathlib
import re
import unittest

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUILD = (ROOT / "scripts" / "build-lint-driver.sh").read_text()
LINT_ENV = (ROOT / "scripts" / "lint-env.sh").read_text()
SANDBOX = (ROOT / "scripts" / "sandbox-build.sh").read_text()
PR_BUILD_TEXT = (ROOT / ".github" / "workflows" / "pr-build.yml").read_text()
PR_BUILD = yaml.safe_load(PR_BUILD_TEXT)


def steps():
    """The steps of the job that runs the sandboxed build."""
    (job,) = [j for j in PR_BUILD["jobs"].values()
              if any("Build exact candidate under bwrap" in s.get("name", "")
                     for s in j.get("steps", []))]
    return job["steps"]


def index_of(name_fragment):
    found = [i for i, s in enumerate(steps()) if name_fragment in s.get("name", "")]
    assert len(found) == 1, f"expected one step named like {name_fragment!r}, got {found}"
    return found[0]


class BuildLintDriverTest(unittest.TestCase):
    def test_build_ignores_the_lake_artifact_cache(self):
        build = BUILD[BUILD.index("(cd \"$WS\" && env"):]
        settings = build.split("lake build")[0]
        for setting in ("LAKE_CACHE_DIR= ", "LAKE_ARTIFACT_CACHE=false",
                        "LAKE_RESTORE_ARTIFACTS=false", "LAKE_NO_CACHE=true",
                        "-u ELAN_TOOLCHAIN", "-u LAKE_CONFIG", "-u LEAN_PATH",
                        "-u LEAN_SRC_PATH", "-u LAKE_PKG_URL_MAP"):
            self.assertIn(setting, settings)
        # Unsetting LAKE_CACHE_DIR would fall back to a global cache instead of disabling it.
        self.assertNotIn("-u LAKE_CACHE_DIR", settings)

    def test_driver_is_built_on_the_host_before_the_sandboxed_build(self):
        driver = index_of("Build the trusted environment-lint driver")
        sandbox = index_of("Build exact candidate under bwrap")
        self.assertLess(driver, sandbox)
        self.assertIn("gate/scripts/build-lint-driver.sh", steps()[driver]["run"])
        self.assertIn("gate/scripts/LintEnvDriver.lean", steps()[driver]["run"])

    def test_driver_is_mounted_read_only_and_passed_to_the_sandbox(self):
        run = steps()[index_of("Build exact candidate under bwrap")]["run"]
        self.assertIn('--ro-bind "$LINT_DRIVER_DIR" "$LINT_DRIVER_DIR"', run)
        self.assertNotRegex(run, r'--bind "\$LINT_DRIVER_DIR"')
        self.assertIn('--setenv LINT_DRIVER_EXE "$LINT_DRIVER_DIR/lint-env-driver"', run)

    def test_sandbox_never_compiles_a_driver(self):
        self.assertIn('test -x "${LINT_DRIVER_EXE:?', SANDBOX)
        self.assertRegex(
            LINT_ENV,
            re.compile(r'elif \[ -n "\$\{WATCHDOG_TOOLCHAIN:-\}" \]; then\n\s+fail ', re.M))

    def test_timeout_is_resolved_before_lake_env(self):
        self.assertIn('TIMEOUT_BIN="$(command -v timeout)"', LINT_ENV)
        self.assertNotIn("lake env timeout", LINT_ENV)


if __name__ == "__main__":
    unittest.main()
