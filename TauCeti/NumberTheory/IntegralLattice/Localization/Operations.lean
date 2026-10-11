/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Localization and lattice operations

Localization commutes with orthogonal sums and integral form twists. The sum comparison is an
isometry, both on the integral localizations and on the completed rational spaces. The two
comparisons intertwine the canonical maps from localization to completion, so the integral and
rational decompositions describe the same embedded local lattice.

Form twists keep the carrier and the canonical embedding fixed and multiply each local form by
the image of the integer scalar. No nondegeneracy or invertibility of two is required: zero
forms, rank zero, and the dyadic prime are included.

## Main declarations

* `TauCeti.IntegralLattice.localOrthogonalSumIsometry`: the integral localization of an
  orthogonal sum is the product of the localized forms.
* `TauCeti.IntegralLattice.completedOrthogonalSumIsometry`: the analogous rational comparison.
* `TauCeti.IntegralLattice.localizationToCompletion_orthogonalSum`: compatibility of these
  comparisons with the embeddings into the completed spaces.
* `TauCeti.IntegralLattice.localIntegralForm_smul` and
  `TauCeti.IntegralLattice.completedRationalForm_smul`: localization commutes with form twists.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter VIII.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open TensorProduct

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  (L : IntegralLattice V) (M : IntegralLattice W) (p : ℕ) [Fact p.Prime]

/-- The localization of an orthogonal sum is isometric to the product of the localized forms.
The underlying equivalence is scalar extension of the carrier-product equivalence followed by
tensor-product distribution over products. -/
noncomputable def localOrthogonalSumIsometry :
    ((L.orthogonalSum M).localIntegralForm p).IsometryEquiv
      ((L.localIntegralForm p).prod (M.localIntegralForm p)) where
  toLinearEquiv := ((L.orthogonalSumCarrierEquiv M).baseChange ℤ ℤ_[p] _ _).trans
    (TensorProduct.prodRight ℤ ℤ_[p] ℤ_[p] L M)
  map_app' x y := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul b y =>
        simp [LinearMap.BilinForm.prod_apply, localIntegralForm_tmul,
          integralForm_orthogonalSum, orthogonalSumFst_apply, orthogonalSumSnd_apply]
        ring

/-- The integral sum comparison on a pure tensor. -/
@[simp]
theorem localOrthogonalSumIsometry_tmul (a : ℤ_[p]) (x : L.orthogonalSum M) :
    L.localOrthogonalSumIsometry M p (a ⊗ₜ x) =
      (a ⊗ₜ L.orthogonalSumFst M x, a ⊗ₜ L.orthogonalSumSnd M x) := by
  rw [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    localOrthogonalSumIsometry]
  simp [orthogonalSumFst_apply, orthogonalSumSnd_apply]

/-- The inverse integral sum comparison on a pair of pure tensors with a common scalar. -/
@[simp]
theorem localOrthogonalSumIsometry_symm_tmul (a : ℤ_[p]) (x : L) (y : M) :
    (L.localOrthogonalSumIsometry M p).toLinearEquiv.symm (a ⊗ₜ x, a ⊗ₜ y) =
      a ⊗ₜ ((L.orthogonalSumInl M x) + (L.orthogonalSumInr M y)) := by
  apply (L.localOrthogonalSumIsometry M p).toLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  simp

/-- The completion of an orthogonal sum is isometric to the product of the completed forms. -/
noncomputable def completedOrthogonalSumIsometry :
    ((L.orthogonalSum M).completedRationalForm p).IsometryEquiv
      ((L.completedRationalForm p).prod (M.completedRationalForm p)) where
  toLinearEquiv := TensorProduct.prodRight ℚ ℚ_[p] ℚ_[p] V W
  map_app' x y := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul b y =>
        simp [LinearMap.BilinForm.prod_apply, completedRationalForm_tmul]
        ring

/-- The rational sum comparison on a pure tensor. -/
@[simp]
theorem completedOrthogonalSumIsometry_tmul (a : ℚ_[p]) (x : V × W) :
    L.completedOrthogonalSumIsometry M p (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) := by
  rw [completedOrthogonalSumIsometry]
  exact TensorProduct.prodRight_tmul ℚ ℚ_[p] ℚ_[p] V W a x

/-- The inverse rational sum comparison on a pair of pure tensors with a common scalar. -/
@[simp]
theorem completedOrthogonalSumIsometry_symm_tmul (a : ℚ_[p]) (x : V) (y : W) :
    (L.completedOrthogonalSumIsometry M p).toLinearEquiv.symm (a ⊗ₜ x, a ⊗ₜ y) =
      a ⊗ₜ (x, y) := by
  apply (L.completedOrthogonalSumIsometry M p).toLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  simp

/-- The integral and rational orthogonal-sum comparisons commute with the canonical embeddings
from localization to completion. -/
theorem localizationToCompletion_orthogonalSum (x : (L.orthogonalSum M).LocalCarrier p) :
    L.completedOrthogonalSumIsometry M p ((L.orthogonalSum M).localizationToCompletion p x) =
      (L.localizationToCompletion p (L.localOrthogonalSumIsometry M p x).1,
        M.localizationToCompletion p (L.localOrthogonalSumIsometry M p x).2) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, Prod.fst_add, Prod.snd_add, h₁, h₂, Prod.mk_add_mk]
  | tmul a x => simp

/-- The local carrier of an orthogonal sum, transported to the product completion, is the product
of the two local carriers. This identifies the embedded lattices, not just their forms. -/
theorem range_localizationToCompletion_orthogonalSum :
    (LinearMap.range ((L.orthogonalSum M).localizationToCompletion p)).map
        ((L.completedOrthogonalSumIsometry M p).toLinearEquiv.toLinearMap.restrictScalars ℤ_[p]) =
      (LinearMap.range (L.localizationToCompletion p)).prod
        (LinearMap.range (M.localizationToCompletion p)) := by
  rw [← LinearMap.range_comp]
  have hcomp :
      ((L.completedOrthogonalSumIsometry M p).toLinearEquiv.toLinearMap.restrictScalars ℤ_[p]).comp
          ((L.orthogonalSum M).localizationToCompletion p) =
        ((L.localizationToCompletion p).prodMap (M.localizationToCompletion p)).comp
          (L.localOrthogonalSumIsometry M p).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact L.localizationToCompletion_orthogonalSum M p x
  rw [hcomp, LinearEquiv.range_comp, LinearMap.range_prodMap]

/-- Form twisting does not change the canonical map from the localization to the completion.
The carrier is unchanged, so both maps have the same domain. -/
@[simp]
theorem localizationToCompletion_smul (n : ℤ) :
    (n • L).localizationToCompletion p = L.localizationToCompletion p := by
  ext x
  simp

/-- An integral form twist localizes to the same scalar twist over `ℤ_p`. -/
@[simp]
theorem localIntegralForm_smul (n : ℤ) :
    (n • L).localIntegralForm p = (n : ℤ_[p]) • L.localIntegralForm p := by
  ext x y
  simp

/-- An integral form twist completes to the same scalar twist over `ℚ_p`. -/
@[simp]
theorem completedRationalForm_smul (n : ℤ) :
    (n • L).completedRationalForm p = (n : ℚ_[p]) • L.completedRationalForm p := by
  ext x y
  simp

end TauCeti.IntegralLattice
