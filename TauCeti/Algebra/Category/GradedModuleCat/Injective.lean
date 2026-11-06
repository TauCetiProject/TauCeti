/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Homogeneous extensions into injective graded modules

Injectivity in the graded module category extends maps of every degree, not only degree zero:
a degree-`p` map into `I` is a degree-zero map into `I{-p}`. Grading shifts preserve injectivity
because they are autoequivalences. These extensions allow one to construct homotopies with
values in graded-injective differential modules.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Projective`:
  the extension argument is dual to its homogeneous lifting for graded-projectives.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Grading shifts preserve injective graded modules. -/
instance injective_shiftObj (I : GradedModuleCat.{v} 𝒜) [Injective I] (n : ℤ) :
    Injective (I.shiftObj n) :=
  Injective.of_iso ((shiftPowIso 𝒜 n).app I) ((((shift 𝒜) ^ n).map_injective_iff I).2 ‹_›)

/-- A homogeneous map into an injective graded module extends across a graded monomorphism,
without changing its degree. -/
theorem exists_isHomogeneous_comp_eq_of_mono (I : GradedModuleCat.{v} 𝒜) [Injective I]
    {K L : GradedModuleCat.{v} 𝒜} (f : K ⟶ L) [Mono f] {p : ℤ} (u : K →ₗ[A] I)
    (hu : LinearMap.IsHomogeneous u K.grading.piece I.grading.piece p) :
    ∃ v : L →ₗ[A] I, LinearMap.IsHomogeneous v L.grading.piece I.grading.piece p ∧
      v ∘ₗ f.hom = u := by
  let u' : K ⟶ I.shiftObj (-p) := ofHom u (by
    rw [_root_.LinearMap.isHomogeneous_shiftObj_iff]
    simpa only [zero_sub, neg_neg] using hu)
  refine ⟨(Injective.factorThru u' f).hom, ?_,
    congrArg Hom.hom (Injective.comp_factorThru u' f)⟩
  simpa only [zero_sub, neg_neg] using
    (_root_.LinearMap.isHomogeneous_shiftObj_iff (M := L) (N := I) _ (-p) 0).1
      (Injective.factorThru u' f).isHomogeneous

end TauCeti.GradedModuleCat
