/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

/-!
# Degreewise formulas for `linearHomComplex` into a degree-zero object

For a `ℤ`-indexed cochain complex `K` in a `k`-linear preadditive category `C` with a zero object
and an object `Y : C`, the degree-`i` term of
`CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` is identified with `K.X (-i) ⟶ Y`
via Mathlib's `Cochain.toSingleLinearEquiv (neg_add_cancel i)`.

This file records the explicit degreewise formulas under this identification for the differential
and for precomposition and postcomposition chain maps.

## Main results

* `TauCeti.toSingleLinearEquiv_linearHomComplex_d_apply`: the differential from degree `i` to
  degree `i + 1` sends `f : K.X (-i) ⟶ Y` to `(-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`.
* `TauCeti.toSingleLinearEquiv_linearHomComplexPrecomp_f_apply`: precomposition by `φ : K₁ ⟶ K₂`
  acts in degree `i` by precomposing with `φ.f (-i)`.
* `TauCeti.toSingleLinearEquiv_linearHomComplexPostcomp_f_apply`: postcomposition by
  `(singleFunctor C 0).map g` acts in degree `i` by postcomposing with `g`.

## References

* Joël Riou's Mathlib constructions `CochainComplex.linearHomComplex` and
  `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv` in
  `Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean`.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] {k : Type*} [Ring k] [Linear k C]

/-- **The differential of `linearHomComplex` into a degree-zero object.** Under the degreewise
identification `Cochain.toSingleLinearEquiv (neg_add_cancel _)`, the differential from degree `i` to
degree `i + 1` sends `f : K.X (-i) ⟶ Y` to `(-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`. -/
theorem toSingleLinearEquiv_linearHomComplex_d_apply [HasZeroObject C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) =
      (i + 1).negOnePow •
        (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplex_d_hom_apply, ← hz,
    Cochain.δ_toSingleMk _ (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1))]
  simp [Cochain.toSingleLinearEquiv]

/-- Under `Cochain.toSingleLinearEquiv`, precomposition in `linearHomComplex` into a degree-zero
object acts by precomposing with `φ.f (-i)`. -/
lemma toSingleLinearEquiv_linearHomComplexPrecomp_f_apply [HasZeroObject C]
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) (i : ℤ)
    (z : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)).f i).hom z) =
      φ.f (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplexPrecomp_f_apply, ← hz, ← Cochain.toSingleMk_precomp]
  simp [Cochain.toSingleLinearEquiv]

/-- Under `Cochain.toSingleLinearEquiv`, postcomposition in `linearHomComplex` into a degree-zero
object acts by postcomposing with `g`. -/
lemma toSingleLinearEquiv_linearHomComplexPostcomp_f_apply [HasZeroObject C]
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplexPostcomp k K ((singleFunctor C 0).map g)).f i).hom z) =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z ≫ g := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplexPostcomp_f_apply, ← hz, ← Cochain.toSingleMk_postcomp]
  simp [Cochain.toSingleLinearEquiv]

end TauCeti
