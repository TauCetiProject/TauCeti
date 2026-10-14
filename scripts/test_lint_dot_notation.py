#!/usr/bin/env python3
"""Regression tests for ``scripts/lint-dot-notation.py``."""

from __future__ import annotations

import contextlib
import io
import pathlib
import tempfile
import unittest

import lean_source as lint


def findings(source: str, namespaces: set[str] | None = None):
    return lint.find_violations({pathlib.Path("TauCeti/Test.lean"): source}, namespaces or {"Foo"})


class DotNotationLintTests(unittest.TestCase):
    def test_named_section_does_not_corrupt_namespace_stack(self):
        source = """\
public section
namespace TauCeti
namespace Foo
def before (x : Foo) := x
section Chain
def inside (x : Foo) := x
end Chain
def after (x : Foo) := x
mutual
def mutualOne (x : Foo) := x
def mutualTwo (x : Foo) := x
end
def afterMutual (x : Foo) := x
end Foo
end TauCeti
end
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         [f"TauCeti.Foo.{name}" for name in
                          ("before", "inside", "after", "mutualOne", "mutualTwo", "afterMutual")])

    def test_attribute_anonymous_instance_and_modifiers_are_detected(self):
        source = """\
namespace TauCeti
namespace Foo
@[expose] def attributed : Foo → Foo := fun x => x
@[simp,
  expose] theorem multilineAttribute (x : Foo) : True := True.intro
instance (x : Foo) : Inhabited Foo := ⟨x⟩
instance (priority := 100) (x : Foo) : Inhabited Foo := ⟨x⟩
nonrec def nonrecursive (x : Foo) := x
scoped instance namedInstance (x : Foo) : Inhabited Foo := ⟨x⟩
local instance localInstance (x : Foo) : Inhabited Foo := ⟨x⟩
partial def partialDefinition (x : Foo) := x
unsafe def unsafeDefinition (x : Foo) := x
def implicitOnly {x : Foo} := x
def connective (x : Foo × Foo) := x
class ClassDeclaration (x : Foo) : Prop where
  property : True
structure StructureDeclaration (x : Foo) where
  field : True
end Foo
end TauCeti
"""
        result = findings(source)
        names = [finding.declaration for finding in result]
        self.assertEqual(len(result), 11)
        self.assertEqual(sum("<anonymous instance " in name for name in names), 2)
        for expected in ("attributed", "multilineAttribute", "nonrecursive", "namedInstance",
                         "localInstance", "partialDefinition", "unsafeDefinition",
                         "ClassDeclaration", "StructureDeclaration"):
            self.assertIn(f"TauCeti.Foo.{expected}", names)

    def test_root_declaration_is_not_flagged(self):
        source = """\
namespace TauCeti
namespace Foo
def _root_.Foo.correct (x : Foo) := x
def misplaced (x : Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.misplaced"])

    def test_function_valued_binders_are_not_receivers(self):
        source = """\
namespace TauCeti
namespace Foo
def returnsFoo : Foo := by
  exact (default : Foo)
def takesFunction (f : Foo → Foo) := f
def takesFoo (x : Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.takesFoo"])

    def test_returned_bundled_tensor_map_is_not_a_receiver(self):
        source = """\
namespace TauCeti.Algebra.TensorProduct
variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]
noncomputable def mulBaseChange :
    (L ⊗[K] A) ⊗[K] (L ⊗[K] B) →ₐ[L] L ⊗[K] (A ⊗[K] B) :=
  (baseChangeTensorAlgEquiv K L A B).symm.toAlgHom.comp
    (Algebra.TensorProduct.mapOfCompatibleSMul L K L _ _)
def tensorReceiver (x : L ⊗[K] A) := x
def functionReceiver : L ⊗[K] A → M := f
def asciiFunctionReceiver : L ⊗[K] A -> M := f
end TauCeti.Algebra.TensorProduct
"""
        self.assertEqual([finding.declaration for finding in findings(source, {"TensorProduct"})],
                         ["TauCeti.Algebra.TensorProduct." + name for name in
                          ("tensorReceiver", "functionReceiver", "asciiFunctionReceiver")])

    def test_returned_bundled_map_arrows_are_not_function_arrows(self):
        for arrow in ("→ₐ[R]", "→ₐc[R]", "→ₗ[R]", "→ₗc[R]", "→ₛₗ[σ]", "→L[𝕜]",
                      "→SL[σ]", "→L⋆[𝕜]", "→ₗ⋆[R]", "→ₛₗᵢ[σ]", "→ₗ.[R]",
                      "→ₗ⁅R⁆", "→+*", "→*", "→+", "→o", "→ₐc", "→ₗc",
                      "→+o", "→*o", "→*₀", "→*₀o", "→+*o", "→+*ᵍ"):
            source = f"""\
namespace TauCeti.Foo
def returnedMap : Foo {arrow} B := f
def compactReturnedMap : Foo{arrow}B := f
def outerFunction : Foo → A {arrow} B := f
def outerAsciiFunction : Foo -> A {arrow} B := f
end TauCeti.Foo
"""
            with self.subTest(arrow=arrow):
                self.assertEqual([finding.declaration for finding in findings(source)],
                                 ["TauCeti.Foo.outerFunction", "TauCeti.Foo.outerAsciiFunction"])

    def test_longer_bundled_arrows_use_their_own_receiver_namespace(self):
        cases = (
            ("→+o", "OrderAddMonoidHom", ("AddMonoidHom",)),
            ("→*o", "OrderMonoidHom", ("MonoidHom",)),
            ("→*₀", "MonoidWithZeroHom", ("MonoidHom",)),
            ("→*₀o", "OrderMonoidWithZeroHom", ("MonoidHom", "MonoidWithZeroHom")),
            ("→+*o", "OrderRingHom", ("AddMonoidHom", "RingHom")),
            ("→+*ᵍ", "GradedRingHom", ("AddMonoidHom", "RingHom")),
        )
        for arrow, owner, shorter_owners in cases:
            for separator in (" ", ""):
                # A compact target can begin with the suffix of a longer registered token:
                # for example, A→+other lexes as A →+o ther, not A →+ other.
                binder_type = f"A{separator}{arrow}{separator}ther"
                source = f"""\
namespace TauCeti.{owner}
def actualReceiver (f : {binder_type}) := f
end TauCeti.{owner}
"""
                for shorter in shorter_owners:
                    source += f"""\
namespace TauCeti.{shorter}
def differentReceiver (f : {binder_type}) := f
end TauCeti.{shorter}
"""
                with self.subTest(arrow=arrow, separator=separator):
                    self.assertEqual(
                        [finding.declaration for finding in
                         findings(source, {owner, *shorter_owners})],
                        [f"TauCeti.{owner}.actualReceiver"],
                    )

    def test_longer_bundled_maps_do_not_claim_sort_ownership(self):
        for arrow in ("→+o", "→*o", "→*₀", "→*₀o", "→+*o", "→+*ᵍ"):
            source = f"""\
namespace TauCeti
def Foo : Type u {arrow} A := f
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
            with self.subTest(arrow=arrow):
                self.assertEqual([finding.declaration for finding in findings(source)],
                                 ["TauCeti.Foo.stillMisplaced"])

    def test_plain_arrows_next_to_identifier_prefixes_remain_function_arrows(self):
        source = """\
namespace TauCeti.Foo
def noSpaces : Foo→Foo := f
def asciiNoSpaces : Foo->Foo := f
def linearPrefix : Foo →LinearMap := f
def scalarPrefix : Foo →Scalar := f
def orderTypePrefix : Foo →OrderHom := f
end TauCeti.Foo
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo." + name for name in
                          ("noSpaces", "asciiNoSpaces", "linearPrefix", "scalarPrefix",
                           "orderTypePrefix")])

    def test_returned_bundled_map_does_not_claim_sort_ownership(self):
        source = """\
namespace TauCeti
def Foo : Type u →ₐ[R] A := f
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.stillMisplaced"])

    def test_notation_receivers_and_dotted_subtypes(self):
        source = """\
namespace TauCeti
namespace ContinuousLinearMap
def notationReceiver (T : E →L[𝕜] F) := T
def dottedSubtype (hT : ContinuousLinearMap.IsFredholm T) := hT
end ContinuousLinearMap
namespace LinearMap
def linearMapReceiver (f : M →ₗ[R] N) := f
end LinearMap
namespace Equiv
def equivReceiver (e : α ≃ β) := e
def longerNotationIsNotEquiv (e : α ≃L[𝕜] β) := e
end Equiv
namespace ContinuousMap
def continuousMapReceiver (f : C(X, Y)) := f
def continuousMapValuedFunction (f : C(X, Y) → Z) := f
end ContinuousMap
namespace ContinuousMultilinearMap
def multilinearReceiver (f : E [×n]→L[𝕜] F) := f
def multilinearValuedFunction (f : (E [×n]→L[𝕜] F) → Z) := f
end ContinuousMultilinearMap
namespace RingHom
def ringHomReceiver (f : R →+* S) := f
end RingHom
namespace AlgEquiv
def algEquivReceiver (e : A ≃ₐ[R] B) := e
end AlgEquiv
namespace LinearIsometryEquiv
def linearIsometryEquivReceiver (e : E ≃ₗᵢ[𝕜] F) := e
end LinearIsometryEquiv
namespace Homeomorph
def homeomorphReceiver (e : X ≃ₜ Y) := e
def longerHomeomorphNotation (e : G ≃ₜ* H) := e
end Homeomorph
namespace Diffeomorph
def withCornersReceiver (e : M ≃ₘ^n⟮I, J⟯ N) := e
def withCornersInfiniteReceiver (e : M ≃ₘ⟮I, J⟯ N) := e
def modelReceiver (e : E ≃ₘ^n[𝕜] F) := e
def modelInfiniteReceiver (e : E ≃ₘ[𝕜] F) := e
end Diffeomorph
namespace BialgHom
def bialgHomReceiver (f : A →ₐc[R] B) := f
end BialgHom
namespace CoalgEquiv
def coalgEquivReceiver (e : A ≃ₗc[R] B) := e
end CoalgEquiv
namespace LinearPMap
def linearPMapReceiver (f : E →ₗ.[R] F) := f
def semilinearPMapReceiver (f : E →ₛₗ.[σ] F) := f
end LinearPMap
namespace Hom
def categoryHomReceiver (f : X ⟶ Y) := f
end Hom
namespace TensorProduct
def tensorProductReceiver (x : M ⊗[R] N) := x
end TensorProduct
namespace LieHom
def lieHomReceiver (f : L →ₗ⁅R⁆ L') := f
end LieHom
end TauCeti
"""
        result = findings(source, {"AlgEquiv", "BialgHom", "CoalgEquiv",
                                   "ContinuousLinearMap", "ContinuousMap",
                                   "ContinuousMultilinearMap", "Diffeomorph", "Equiv", "Hom",
                                   "Homeomorph", "LieHom", "LinearIsometryEquiv", "LinearMap",
                                   "LinearPMap", "RingHom", "TensorProduct"})
        self.assertEqual([finding.declaration for finding in result], [
            "TauCeti.ContinuousLinearMap.notationReceiver",
            "TauCeti.LinearMap.linearMapReceiver",
            "TauCeti.Equiv.equivReceiver",
            "TauCeti.ContinuousMap.continuousMapReceiver",
            "TauCeti.ContinuousMultilinearMap.multilinearReceiver",
            "TauCeti.RingHom.ringHomReceiver",
            "TauCeti.AlgEquiv.algEquivReceiver",
            "TauCeti.LinearIsometryEquiv.linearIsometryEquivReceiver",
            "TauCeti.Homeomorph.homeomorphReceiver",
            "TauCeti.Diffeomorph.withCornersReceiver",
            "TauCeti.Diffeomorph.withCornersInfiniteReceiver",
            "TauCeti.Diffeomorph.modelReceiver",
            "TauCeti.Diffeomorph.modelInfiniteReceiver",
            "TauCeti.BialgHom.bialgHomReceiver",
            "TauCeti.CoalgEquiv.coalgEquivReceiver",
            "TauCeti.LinearPMap.linearPMapReceiver",
            "TauCeti.LinearPMap.semilinearPMapReceiver",
            "TauCeti.Hom.categoryHomReceiver",
            "TauCeti.TensorProduct.tensorProductReceiver",
            "TauCeti.LieHom.lieHomReceiver",
        ])

    def test_scoped_variable_and_dotted_name_are_detected(self):
        source = """\
namespace TauCeti
namespace Foo
variable (x : Foo)
variable {y : Foo}
def fromVariable : x = x := rfl
def implicitVariable : y = y := rfl
end Foo
def Foo.dotted (x : Foo) := x
def Foo.termType (x : Foo.term) := x
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.fromVariable", "TauCeti.Foo.dotted"])

    def test_include_and_omit_follow_scope(self):
        source = """\
namespace TauCeti
namespace Foo
variable (x : Foo)
include x
theorem included : True := True.intro
section Inner
omit x
theorem omittedInside : True := True.intro
end Inner
theorem restored : True := True.intro
omit x
theorem omittedAfter : True := True.intro
include x in
theorem includedOnce : True := True.intro
theorem omittedFinally : True := True.intro
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)], [
            "TauCeti.Foo.included",
            "TauCeti.Foo.restored",
            "TauCeti.Foo.includedOnce",
        ])

    def test_owned_names_are_lowercase_and_matched_by_full_path(self):
        sources = {
            pathlib.Path("TauCeti/Own.lean"): """\
namespace TauCeti
def prod : Type := Nat
namespace prod
def fst (x : prod) := x
end prod
end TauCeti
""",
            pathlib.Path("TauCeti/Other.lean"): """\
namespace TauCeti
namespace prod
def correctlyOwned (x : prod) := x
end prod
end TauCeti
""",
            pathlib.Path("TauCeti/Unrelated.lean"): """\
namespace TauCeti.Other
namespace prod
def misplaced (x : prod) := x
end prod
end TauCeti.Other
""",
            pathlib.Path("TauCeti/Nested.lean"): """\
namespace TauCeti
def Quiver.IsAcyclic : Type := Nat
end TauCeti
""",
            pathlib.Path("TauCeti/NestedOther.lean"): """\
namespace TauCeti.Quiver.IsAcyclic
def correctlyNested (x : Quiver.IsAcyclic) := x
end TauCeti.Quiver.IsAcyclic
""",
        }
        self.assertEqual([finding.declaration for finding in
                          lint.find_violations(sources, {"prod", "Quiver", "IsAcyclic"})],
                         ["TauCeti.Other.prod.misplaced"])

    def test_value_declaration_does_not_exempt_a_namespace(self):
        source = """\
namespace TauCeti
def Foo : Nat := 0
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.stillMisplaced"])

    def test_nested_owned_type_does_not_exempt_an_outer_namespace(self):
        source = """\
namespace TauCeti.Foo
structure Owned
namespace Owned
def stillMisplaced (x : _root_.Foo) := x
end Owned
end TauCeti.Foo
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.Owned.stillMisplaced"])

    def test_owned_type_does_not_exempt_a_nested_mathlib_named_namespace(self):
        source = """\
namespace TauCeti
def Owned : Type := Nat
namespace Owned.Foo
def stillMisplaced (x : _root_.Foo) := x
end Owned.Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Owned.Foo.stillMisplaced"])

    def test_strict_implicit_type_binder_does_not_make_a_value_an_owned_type(self):
        source = """\
namespace TauCeti
def Foo ⦃α : Type⦄ (n : Nat) : Nat := n
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.stillMisplaced"])

    def test_explicit_receiver_after_strict_implicit_binder_is_detected(self):
        source = """\
namespace TauCeti.Foo
theorem detected ⦃α : Type⦄ (x : _root_.Foo) : True := True.intro
end TauCeti.Foo
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.detected"])

    def test_parenthesized_arrow_domain_does_not_make_a_value_an_owned_type(self):
        source = """\
namespace TauCeti
def Foo : (Type u) → Nat := fun _ ↦ 0
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.stillMisplaced"])

    def test_indexed_type_family_is_an_owned_type(self):
        source = """\
namespace TauCeti
def Foo : Nat → Type := fun _ ↦ Nat
def Bar : Nat -> Type := fun _ ↦ Nat
namespace Foo
def correctlyOwned (x : _root_.Foo 0) := x
end Foo
end TauCeti
"""
        self.assertEqual(findings(source), [])
        self.assertIn(("TauCeti", "Bar"), lint.own_declaration_paths(
            {pathlib.Path("TauCeti/Test.lean"): source}))

    def test_unannotated_type_alias_is_not_an_owned_type(self):
        source = """\
namespace TauCeti
abbrev Foo := Nat
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.stillMisplaced"])

    def test_prop_and_opaque_sort_results_are_owned(self):
        source = """\
namespace TauCeti
def Predicate : Prop := True
opaque Hidden : Type
def Family : ∀ n : Nat, Type := fun _ ↦ Nat
def Parenthesized : (Nat → Type) := fun _ ↦ Nat
end TauCeti
"""
        self.assertEqual(lint.own_declaration_paths(
            {pathlib.Path("TauCeti/Test.lean"): source}),
            {("TauCeti", "Predicate"), ("TauCeti", "Hidden"),
             ("TauCeti", "Family"), ("TauCeti", "Parenthesized")})

    def test_universe_annotation_is_not_part_of_a_declaration_name(self):
        source = """\
namespace TauCeti
def Foo.{u} (X : Type u) : Type u := X
namespace Foo
def correctlyOwned (x : _root_.Foo Type) := x
end Foo
end TauCeti
"""
        self.assertEqual(findings(source), [])
        self.assertIn(("TauCeti", "Foo"), lint.own_declaration_paths(
            {pathlib.Path("TauCeti/Test.lean"): source}))

    def test_missing_mathlib_checkout_fails_loudly(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            source_root = root / "TauCeti"
            source_root.mkdir()
            baseline = root / "baseline.txt"
            baseline.write_text("")
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                result = lint.main(
                    ["--mathlib-root", str(root / "missing"), "--source-root", str(source_root),
                     "--baseline", str(baseline)])
        self.assertEqual(result, 2)
        self.assertIn("Mathlib source directory not found", stderr.getvalue())

    def test_primed_identifier_does_not_open_a_character_literal(self):
        cleaned = lint.strip_comments_and_strings("Homeomorph.prodAssoc F F' G' ''\ndef next := 1\n")
        self.assertIn("def next", cleaned)

    def test_raw_strings_and_quoted_identifiers_preserve_following_declarations(self):
        source = ('def «"» := r#"""#\n'
                  'def text := r###"namespace Hidden "# /- text\n'
                  'def hidden := 1 "###\n'
                  'def next := 1\n')
        cleaned = lint.strip_comments_and_strings(source)
        self.assertEqual(len(cleaned), len(source))
        self.assertEqual(cleaned.count("\n"), source.count("\n"))
        self.assertIn("def next := 1", cleaned)
        self.assertNotIn("Hidden", cleaned)
        self.assertNotIn("hidden", cleaned)

    def test_quoted_namespace_is_not_truncated_to_an_unquoted_prefix(self):
        self.assertEqual(lint.scopes("namespace Foo.«bar»\nend Foo.«bar»\n"), [])

    def test_identifier_suffixes_do_not_start_raw_strings_or_characters(self):
        for prefix in ('Foo.r', 'f!r', 'f?r', '℘r'):
            source = 'def text := ' + prefix + '"\\\" /- "\ndef next := 1\n'
            with self.subTest(prefix=prefix):
                self.assertIn('def next := 1', lint.strip_comments_and_strings(source))
        source = 'def text := f!\'"\' /- "\ndef next := 1\n'
        self.assertIn('def next := 1', lint.strip_comments_and_strings(source))

    def test_literal_string_text_can_be_preserved_for_conservative_guards(self):
        source = ('def text := "set_option"\n'
                  'def raw := r#"set_option """#\n'
                  '-- set_option maxRecDepth 4000\n'
                  'def next := 1\n')
        cleaned = lint.strip_comments_and_strings(source, mask_strings=False)
        self.assertEqual(len(cleaned), len(source))
        self.assertEqual(cleaned.count("set_option"), 2)
        self.assertNotIn("maxRecDepth", cleaned)
        self.assertIn("def next := 1", cleaned)
        self.assertNotIn("set_option", lint.strip_comments_and_strings(source))

    def test_main_rejects_new_and_reports_ratchetable_findings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            mathlib = root / "Mathlib"
            source_root = root / "TauCeti"
            mathlib.mkdir()
            source_root.mkdir()
            (mathlib / "Foo.lean").write_text("namespace Foo\nend Foo\n")
            source = source_root / "Test.lean"
            source.write_text("namespace TauCeti\nnamespace Foo\ndef bar (x : Foo) := x\n"
                              "end Foo\nend TauCeti\n")
            baseline = pathlib.Path(directory) / "baseline.txt"
            baseline.write_text("")
            args = ["--mathlib-root", str(mathlib), "--source-root", str(source_root),
                    "--baseline", str(baseline)]
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(lint.main(args), 1)
                self.assertEqual(lint.main([*args, "--write-baseline"]), 0)
                source.write_text("namespace TauCeti\ndef _root_.Foo.bar (x : Foo) := x\nend TauCeti\n")
                self.assertEqual(lint.main(args), 0)
            self.assertIn("1 new", stdout.getvalue())
            self.assertIn("1 ratchetable", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
