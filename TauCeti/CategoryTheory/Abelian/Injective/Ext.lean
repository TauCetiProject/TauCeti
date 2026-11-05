/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Degree-zero classes of an injective resolution

Mathlib's `CategoryTheory.InjectiveResolution.extMk` sends a cocycle `f : X ⟶ Iⁿ` of an injective
resolution `I` of `Y` to its class in `Extⁿ(X, Y)`, and
`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff` says that this class vanishes exactly when
`f` is a coboundary, in every positive degree `n = p + 1`. In degree zero there are no
coboundaries, so the class of a degree-zero cocycle vanishes only when the cocycle itself does
(`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff_eq_zero`). Together the two statements
identify `Extⁿ(X, Y)` with the cohomology of the complex `Hom(X, I)` in every degree.
-/

public section

universe w v u

open CategoryTheory Limits CochainComplex HomComplex Abelian

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y)

/-- The class of a degree-zero cocycle `f : X ⟶ I⁰` of an injective resolution in `Ext⁰` vanishes
only if `f` is zero. This is the degree-zero counterpart of
`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff`. -/
lemma extMk_eq_zero_iff_eq_zero (f : X ⟶ R.cocomplex.X 0) (m : ℕ) (hm : 0 + 1 = m)
    (hf : f ≫ R.cocomplex.d 0 m = 0) :
    R.extMk f m hm hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  rw [← R.extEquivCohomologyClass.apply_eq_iff_eq, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff,
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by lia)] at h
  obtain ⟨g, hg⟩ := h
  -- the resolution has no term in degree `-1`
  obtain rfl : g = 0 := (R.cochainComplex.isZero_of_isStrictlyGE 0 (-1)).eq_of_tgt _ _
  rw [zero_comp] at hg
  exact (cancel_mono (R.cochainComplexXIso 0 0 rfl).inv).1 (hg.symm.trans zero_comp.symm)

end CategoryTheory.InjectiveResolution
