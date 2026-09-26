/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Isometries of quadratic maps

This file records general properties of quadratic-map isometries.  It also reindexes a weighted
sum of squares along an equivalence of its index type, which complements Mathlib's
`QuadraticForm.weightedSumSquaresCongr` for equal weights and
`QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares` for weights rescaled by squares.

## Main results

* `QuadraticMap.Isometry.polar_apply`: an isometry preserves polarization.
* `QuadraticMap.IsometryEquiv.polar_apply`: an isometric equivalence preserves polarization.
* `QuadraticMap.IsometryEquiv.trans_apply`: composition of isometries acts by composition.
* `QuadraticMap.IsometryEquiv.nondegenerate_iff`: nondegeneracy is invariant under isometry.
* `QuadraticForm.isometryEquivWeightedSumSquaresReindex`: reindexing the weights of a weighted sum
  of squares along an equivalence of index types gives an isometric quadratic form.
* `QuadraticForm.equivalent_weightedSumSquares_of_comp_eq`: weighted sums of squares whose weights
  agree after reindexing are equivalent.
-/

public section

namespace TauCeti

open QuadraticMap

universe u v w

/-- An isometry preserves the polarization of a quadratic map. -/
@[simp]
theorem _root_.QuadraticMap.Isometry.polar_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N}
    {Q₂ : QuadraticMap R M₂ N} (f : Q₁ →qᵢ Q₂) (x y : M₁) :
    polar Q₂ (f x) (f y) = polar Q₁ x y := by
  simp only [QuadraticMap.polar, ← map_add f, QuadraticMap.Isometry.map_app]

/-- An isometric equivalence preserves the polarization of a quadratic map. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.polar_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x y : M₁) : polar Q₂ (e x) (e y) = polar Q₁ x y := by
  simpa using e.toIsometry.polar_apply x y

/-- The composition of two isometric equivalences acts by composing their underlying maps. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.trans_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {M₃ : Type*} {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup N]
    [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) (x : M₁) :
    f.trans g x = g (f x) :=
  rfl

/-- Nondegeneracy of a quadratic map is invariant under an isometric equivalence. -/
theorem _root_.QuadraticMap.IsometryEquiv.nondegenerate_iff
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w}
    [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.Nondegenerate ↔ Q₂.Nondegenerate := by
  -- This follows the proof of Mathlib's `QuadraticMap.IsometryEquiv.map_radical`
  -- (`Mathlib/LinearAlgebra/QuadraticForm/Radical.lean`), with the polar kernel for the radical.
  have hpolar : Q₁.polarBilin.ker.map e.toLinearMap = Q₂.polarBilin.ker := by
    ext
    simp [LinearMap.ext_iff, e.toEquiv.forall_congr_left]
  constructor
  · intro hQ₁
    have hradical := e.map_radical
    rw [hQ₁.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    rw [← hpolar]
    apply Cardinal.lift_le_one_iff.mp
    rw [e.toLinearEquiv.lift_rank_map_eq]
    exact Cardinal.lift_le_one_iff.mpr hQ₁.rank_rad_polar_le
  · intro hQ₂
    have hradical := e.symm.map_radical
    rw [hQ₂.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    apply Cardinal.lift_le_one_iff.mp
    rw [← e.toLinearEquiv.lift_rank_map_eq Q₁.polarBilin.ker, hpolar]
    exact Cardinal.lift_le_one_iff.mpr hQ₂.rank_rad_polar_le

section Reindex

variable {ι ι' R S : Type*} [Fintype ι] [Fintype ι'] [CommSemiring R] [Monoid S]
  [DistribMulAction S R] [SMulCommClass S R R]

/-- Reindexing the weights of a weighted sum of squares along an equivalence of the index types
gives an isometric quadratic form.  The isometry is precomposition with the equivalence. -/
def _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex (w : ι → S) (e : ι' ≃ ι) :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R (w ∘ e)) where
  __ := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    simpa [weightedSumSquares_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      using e.sum_comp fun i ↦ w i • (x i * x i)

/-- The reindexing isometry acts on a vector by precomposition with the equivalence. -/
@[simp]
theorem _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex_apply (w : ι → S) (e : ι' ≃ ι)
    (x : ι → R) (i : ι') :
    QuadraticForm.isometryEquivWeightedSumSquaresReindex w e x i = x (e i) :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

/-- Weighted sums of squares whose weights agree after reindexing are equivalent. -/
theorem _root_.QuadraticForm.equivalent_weightedSumSquares_of_comp_eq
    {w : ι → S} {w' : ι' → S} (e : ι' ≃ ι) (h : w ∘ e = w') :
    (weightedSumSquares R w').Equivalent (weightedSumSquares R w) :=
  ⟨((QuadraticForm.isometryEquivWeightedSumSquaresReindex w e).trans
    (QuadraticForm.weightedSumSquaresCongr h)).symm⟩

end Reindex

end TauCeti
