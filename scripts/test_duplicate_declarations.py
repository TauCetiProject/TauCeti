#!/usr/bin/env python3
"""Compile real independent Lean modules, then exercise the declaration audit."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts/Axioms.lean"
LEAN = os.environ.get("LEAN", "lean")


class DuplicateDeclarationsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tooling = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.tooling.cleanup)
        cls.tools = Path(cls.tooling.name)
        (cls.tools / "scripts").mkdir()
        compile_env = os.environ.copy()
        compile_env["LEAN_PATH"] = str(cls.tools)
        built = subprocess.run(
            [LEAN, "-o", str(cls.tools / "scripts/Axioms.olean"), str(DRIVER)],
            cwd=ROOT, env=compile_env, text=True, capture_output=True,
        )
        if built.returncode:
            raise RuntimeError(built.stdout + built.stderr)
        cls.native = os.environ.get("AUDIT_DRIVER_EXE")
        if not cls.native:
            built = subprocess.run(
                ["bash", str(ROOT / "scripts/build-audit-driver.sh"), str(ROOT),
                 str(ROOT / "scripts"), str(cls.tools)], text=True, capture_output=True,
            )
            if built.returncode:
                raise RuntimeError(built.stdout + built.stderr)
            cls.native = str(cls.tools / "audit-driver")

    def fixture(self, modules, *, missing=None, missing_part=None, full=False, scope=None,
                repeat=1, lifetime=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "TauCeti").mkdir()
            env = os.environ.copy()
            env.pop("AXIOMS_ONLY_MODULES", None)
            env.pop("AUDIT_PHASES_FILE", None)
            # Fixtures need only Lean's sysroot; never pick up real TauCeti artifacts.
            env["LEAN_PATH"] = os.pathsep.join((tmp, str(self.tools)))
            sources = {"TauCeti": "module\npublic theorem fixtureRoot : True := True.intro\n", **modules}
            for module, body in sources.items():
                path = root / (module.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(body)
                built = subprocess.run(
                    [LEAN, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=root, env=env, text=True, capture_output=True,
                )
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            if missing:
                (root / (missing.replace(".", "/") + ".olean")).unlink()
            if missing_part:
                (root / (missing_part.replace(".", "/") + ".olean.private")).unlink()
            if scope is not None:
                (root / "scope.txt").write_text(scope)
                env["AXIOMS_ONLY_MODULES"] = str(root / "scope.txt")
            args = [] if full else ["--duplicates-only"]
            def run_checks(command, flags, with_module_system):
                result = subprocess.run([*command, *flags], cwd=root, env=env,
                                        text=True, capture_output=True)
                if with_module_system and result.returncode == 0:
                    module_result = subprocess.run(
                        [LEAN, "--run", str(ROOT / "scripts/ModuleSystem.lean")],
                        cwd=root, env=env, text=True, capture_output=True,
                    )
                    result = subprocess.CompletedProcess(
                        result.args, module_result.returncode,
                        result.stdout + module_result.stdout,
                        result.stderr + module_result.stderr,
                    )
                return result
            result = run_checks([LEAN, "--run", str(DRIVER)], args, full)

            for _ in range(repeat):
                shared = run_checks([self.native], args, full)
                self.assertEqual(shared.returncode, result.returncode,
                                 "native/interpreted mismatch:\n" + shared.stdout + shared.stderr)
                self.assertEqual(shared.stdout, result.stdout)
                self.assertEqual(shared.stderr, result.stderr)
            if lifetime:
                harness = root / "Lifetime.lean"
                harness.write_text(
                    "import scripts.Axioms\n#eval do\n"
                    "  for _ in [:3] do\n"
                    "    let status ← main []\n"
                    f"    unless status == {result.returncode} do\n"
                    '      throw <| IO.userError "wrong audit status"\n'
                )
                repeated = subprocess.run([LEAN, str(harness)], cwd=root, env=env,
                                          text=True, capture_output=True)
                self.assertEqual(repeated.returncode, 0, repeated.stdout + repeated.stderr)
                self.assertEqual(repeated.stdout.count("phase audit-import"), 3)
                self.assertEqual((repeated.stdout + repeated.stderr).count("use disallowed axioms:"),
                                 0 if result.returncode == 0 else 3)
            if not full:
                complete = run_checks([self.native], [], True)
                self.assertEqual(complete.returncode, result.returncode,
                                 "combined audit mismatch:\n" + complete.stdout + complete.stderr)
            return result

    def assert_collision(self, result, name="Collision", first="TauCeti.A", second="TauCeti.B"):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(name, result.stderr)
        self.assertIn(first, result.stderr)
        self.assertIn(second, result.stderr)

    def test_identical_independent_definitions_and_empty_root(self):
        self.assert_collision(self.fixture({
            "TauCeti.A": "module\npublic def Collision := 7\n",
            "TauCeti.B": "module\npublic def Collision := 7\n",
        }))

    def test_different_definitions(self):
        self.assert_collision(self.fixture({
            "TauCeti.A": "module\npublic def Collision := 7\n",
            "TauCeti.B": "module\npublic def Collision := true\n",
        }))

    def test_compatible_theorems_even_when_joint_import_succeeds(self):
        self.assert_collision(self.fixture({
            "TauCeti.A": "module\npublic theorem Collision : True := True.intro\n",
            "TauCeti.B": "module\npublic theorem Collision : True := by trivial\n",
            "TauCeti.Both": "module\npublic import TauCeti.A\npublic import TauCeti.B\n",
        }))

    def test_lazy_equations_are_allowed(self):
        result = self.fixture({
            "TauCeti.Base": "module\n@[expose] public def f : Nat → Nat | 0 => 0 | n+1 => n\n",
            "TauCeti.A": "module\npublic import TauCeti.Base\n"
                         "public theorem testA : f 0 = 0 := by simp only [f]\n",
            "TauCeti.B": "module\npublic import TauCeti.Base\n"
                         "public theorem testB : f 0 = 0 := by simp only [f]\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_user_theorem_with_reserved_looking_name_is_not_exempt(self):
        self.assert_collision(self.fixture({
            "TauCeti.A": "module\npublic theorem f.eq_1 : True := True.intro\n",
            "TauCeti.B": "module\npublic theorem f.eq_1 : True := True.intro\n",
            "TauCeti.Base": "module\n@[expose] public def f : Nat → Nat | 0 => 0 | n+1 => n\n",
        }), "f.eq_1")

    def test_nonexported_definitions_are_module_private(self):
        result = self.fixture({
            "TauCeti.A": "module\ndef Collision := 7\n",
            "TauCeti.B": "module\ndef Collision := 7\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_generated_declarations(self):
        result = self.fixture({
            "TauCeti.A": "module\npublic structure Collision where\n  x : Nat\n",
            "TauCeti.B": "module\npublic structure Collision where\n  x : Nat\n",
        })
        self.assert_collision(result, "Collision.")

    def test_local_instance_is_not_a_private_declaration(self):
        self.assert_collision(self.fixture({
            "TauCeti.A": "module\npublic section\nlocal instance Collision : Nonempty Nat := ⟨0⟩\n",
            "TauCeti.B": "module\npublic section\nlocal instance Collision : Nonempty Nat := ⟨0⟩\n",
        }))

    def test_private_helpers_and_namespaces_and_quoted_identifiers(self):
        result = self.fixture({
            "TauCeti.A": 'module\nprivate def helper := 1\npublic def A.item := 1\n'
                         'public def «A.B» := 1\n',
            "TauCeti.B": 'module\nprivate def helper := 1\npublic def B.item := 1\n'
                         'public def A.B := 1\n',
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_diamond_imports(self):
        result = self.fixture({
            "TauCeti.Base": "module\npublic def Unique := 1\n",
            "TauCeti.A": "module\npublic import TauCeti.Base\n",
            "TauCeti.B": "module\npublic import TauCeti.Base\n",
            "TauCeti.Diamond": "module\npublic import TauCeti.A\npublic import TauCeti.B\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_dependency_collision(self):
        self.assert_collision(self.fixture({
            "Dependency": "module\npublic def Collision := 1\n",
            "TauCeti.A": "module\npublic import Dependency\n",
            "TauCeti.B": "module\npublic def Collision := 1\n",
        }), first="Dependency")

    def test_dependency_only_collision_is_out_of_scope(self):
        result = self.fixture({
            "DependencyA": "module\npublic theorem Collision : True := True.intro\n",
            "DependencyB": "module\npublic theorem Collision : True := True.intro\n",
            "TauCeti.A": "module\npublic import DependencyA\n",
            "TauCeti.B": "module\npublic import DependencyB\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_compatible_collision_with_multiple_dependencies(self):
        # These equal theorems survive Lean's importer. Only the ownership audit catches
        # the local collision, including when two dependencies already share the name.
        self.assert_collision(self.fixture({
            "DependencyA": "module\npublic theorem Collision : True := True.intro\n",
            "DependencyB": "module\npublic theorem Collision : True := True.intro\n",
            "TauCeti.Own": "module\npublic theorem Collision : True := True.intro\n",
            "TauCeti.A": "module\npublic import DependencyA\n",
            "TauCeti.B": "module\npublic import DependencyB\n",
        }), first="Dependency", second="TauCeti.Own")

    def test_missing_artifacts_fail_closed(self):
        for options in ({"missing": "TauCeti.A"}, {"missing_part": "TauCeti.A"}):
            with self.subTest(options=options):
                result = self.fixture({"TauCeti.A": "module\npublic def Unique := 1\n"}, **options)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("audit-driver:", result.stderr)

    def test_empty_source_tree_fails_closed(self):
        result = self.fixture({})
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)


    def test_full_audit_allowed_axioms_private_and_orphans(self):
        result = self.fixture({
            "TauCeti.Orphan": "module\nprivate theorem hidden : True := True.intro\n"
                             "public theorem ext (a b : Prop) (h : a ↔ b) : a = b := propext h\n"
                             "public noncomputable def chosen : Nat := Classical.choice inferInstance\n"
                             "public theorem sound : Quot.mk Nat.le 0 = Quot.mk Nat.le 1 :=\n"
                             "  Quot.sound (Nat.zero_le 1)\n",
        }, full=True, repeat=3)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("axioms: audited", result.stdout)
        self.assertIn("module-system: all 2", result.stdout)

    def test_full_audit_every_disallowed_axiom_fixture(self):
        bodies = {
            "custom": ("module\npublic axiom counterfeit : False\n", "counterfeit"),
            "sorry": ("module\npublic theorem bad : False := by sorry\n", "sorryAx"),
            "admit": ("module\npublic theorem bad : False := by admit\n", "sorryAx"),
            "private": ("module\nprivate axiom hidden : False\n"
                        "private theorem bad : False := hidden\n", "hidden"),
            "opaque": ("module\npublic opaque bad : False := by sorry\n", "sorryAx"),
            "native_decide": ("module\npublic import Lean\n"
                              "public theorem bad : 1 = 1 := by native_decide\n",
                              "native_decide.ax_"),
            "ofReduceBool": ("module\npublic axiom Lean.ofReduceBool : False\n",
                             "Lean.ofReduceBool"),
            "ofReduceNat": ("module\npublic axiom Lean.ofReduceNat : False\n",
                            "Lean.ofReduceNat"),
            "trustCompiler": ("module\npublic axiom Lean.trustCompiler : False\n",
                              "Lean.trustCompiler"),
            "axiom_in_type": ("module\npublic axiom badType : Prop\n"
                              "public axiom bad : badType\n", "badType"),
        }
        for kind, (body, axiom) in bodies.items():
            with self.subTest(kind=kind):
                result = self.fixture({"TauCeti.Orphan": body}, full=True, repeat=2)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("axioms:", result.stderr)
                self.assertIn(axiom, result.stderr)
                self.assertNotIn("phase audit-module-system", result.stdout)

    def test_disallowed_axiom_from_dependency(self):
        result = self.fixture({
            "Dependency": "module\npublic axiom counterfeit : False\n",
            "TauCeti.Orphan": "module\npublic import Dependency\n"
                             "public theorem bad : False := counterfeit\n",
        }, full=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("bad → [counterfeit]", result.stderr)

    def test_scope_includes_unchanged_importers(self):
        result = self.fixture({
            "TauCeti.Base": "module\npublic axiom counterfeit : False\n",
            "TauCeti.Importer": "module\npublic import TauCeti.Base\n"
                               "public theorem bad : False := counterfeit\n",
        }, full=True, scope="TauCeti.Base\n")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("bad → [counterfeit]", result.stderr)

    def test_scope_does_not_scope_ownership_or_module_flags(self):
        result = self.fixture({"TauCeti.Orphan": "def unique := 1\n"},
                              full=True, scope="TauCeti.Missing\n")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("module-system:", result.stderr)
        self.assertIn("TauCeti.Orphan", result.stderr)

    def test_root_module_system_flag(self):
        result = self.fixture({"TauCeti": "theorem fixtureRoot : True := True.intro\n",
                               "TauCeti.Orphan": "module\npublic def unique := 1\n"}, full=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("module-system:", result.stderr)
        self.assertIn("  TauCeti\n", result.stderr)

    def test_zero_declarations_fails_closed(self):
        result = self.fixture({"TauCeti": "module\n", "TauCeti.Orphan": "module\n"}, full=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("axioms: audited 0", result.stderr)

    def test_initializers_do_not_execute(self):
        result = self.fixture({"TauCeti.Orphan": "module\npublic import Lean\n"
                              "initialize IO.eprintln \"INITIALIZER-RAN\"\n"
                              "public theorem unique : True := True.intro\n"}, full=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("INITIALIZER-RAN", result.stdout + result.stderr)

    def test_environment_teardown_and_loaded_name_lifetime(self):
        # Repeat imports in one runtime, on success and on rendered private-name errors.
        for body in ("module\npublic theorem good : True := True.intro\n",
                     "module\nprivate axiom hidden : False\n"
                     "private theorem bad : False := hidden\n"):
            with self.subTest(body=body):
                self.fixture({"TauCeti.Orphan": body}, full=True, lifetime=True)

    def test_usage_exit_code(self):
        result = subprocess.run([self.native, "--bogus"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("usage:", result.stderr)

if __name__ == "__main__":
    unittest.main()
