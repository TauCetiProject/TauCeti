/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Covector
public import TauCeti.Analysis.Sobolev.DifferentialForm.Lp
public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry

/-!
# The Hodge star of `Lᵖ` differential forms

For an orientation `o` of `ℝⁿ` and `k + l = n`, the Hodge star of covectors
`Orientation.covectorHodgeStar` is a linear isometry for the Gram norm. Applied pointwise, it is a
linear isometric equivalence `o.lpFormHodgeStar hkl : LpForm Ω p k ≃ₗᵢ[ℝ] LpForm Ω p l` between the
`Lᵖ` forms of complementary degrees on an open set `Ω`. It satisfies `⋆⋆ = (-1) ^ (k l)`, changes
sign with the orientation, and for `p = 2` its adjoint is `(-1) ^ (k l) ⋆`:
`⟪⋆u, v⟫ = (-1) ^ (k l) ⟪u, ⋆v⟫`.

Square-integrable forms whose star has a weak exterior derivative are the domain of the weak
codifferential `δ = ± ⋆ d ⋆`; the adjointness of the star is the pointwise identity that relates
`δ` to the adjoint of the weak exterior derivative.

## Main definitions

* `Orientation.lpFormHodgeStar`: the pointwise Hodge star of `Lᵖ` forms.

## Main results

* `Orientation.coeFn_lpFormHodgeStar`: it is the Hodge star of covectors almost everywhere.
* `Orientation.lpFormHodgeStar_lpFormHodgeStar`: `⋆⋆u = (-1) ^ (k l) u`.
* `Orientation.inner_lpFormHodgeStar_left`: `⟪⋆u, v⟫ = (-1) ^ (k l) ⟪u, ⋆v⟫` in `L²`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Module TauCeti
open scoped ENNReal RealInnerProductSpace

namespace Orientation

variable {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin n))} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k l : ℕ}
  (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))

/-- The Hodge star of `Lᵖ` forms of degree `k` into `Lᵖ` forms of degree `l`, for `k + l = n`: the
Hodge star of covectors `Orientation.covectorHodgeStar` applied pointwise. -/
def lpFormHodgeStar (hkl : k + l = n) : LpForm Ω p k ≃ₗᵢ[ℝ] LpForm Ω p l :=
  (o.covectorHodgeStar (hkl.trans finrank_euclideanSpace_fin.symm)).compLpₗᵢ p _

/-- The Hodge star of an `Lᵖ` form is almost everywhere the Hodge star of its values. -/
theorem coeFn_lpFormHodgeStar (hkl : k + l = n) (u : LpForm Ω p k) :
    o.lpFormHodgeStar hkl u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
      fun x ↦ o.covectorHodgeStar (hkl.trans finrank_euclideanSpace_fin.symm) (u x) :=
  LinearIsometryEquiv.coeFn_compLpₗᵢ _ u

/-- **The square of the Hodge star of `Lᵖ` forms**: `⋆⋆u = (-1) ^ (k l) u` for an `Lᵖ` form `u` of
degree `k`, where `k + l = n`. -/
theorem lpFormHodgeStar_lpFormHodgeStar (hkl : k + l = n) (hlk : l + k = n) (u : LpForm Ω p k) :
    o.lpFormHodgeStar hlk (o.lpFormHodgeStar hkl u) = (-1 : ℝ) ^ (k * l) • u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lpFormHodgeStar o hlk (o.lpFormHodgeStar hkl u),
    coeFn_lpFormHodgeStar o hkl u, Lp.coeFn_smul ((-1 : ℝ) ^ (k * l)) u] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, covectorHodgeStar_covectorHodgeStar, Pi.smul_apply]

/-- The inverse of the Hodge star of `Lᵖ` forms is `(-1) ^ (k l)` times the Hodge star in the
complementary degree. -/
theorem lpFormHodgeStar_symm_apply (hkl : k + l = n) (hlk : l + k = n) (v : LpForm Ω p l) :
    (o.lpFormHodgeStar hkl).symm v = (-1 : ℝ) ^ (k * l) • o.lpFormHodgeStar hlk v := by
  apply (o.lpFormHodgeStar hkl).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_smul, mul_comm k l,
    lpFormHodgeStar_lpFormHodgeStar o hlk hkl, smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp

/-- Reversing the orientation negates the Hodge star of `Lᵖ` forms. -/
@[simp]
theorem lpFormHodgeStar_neg_orientation (hkl : k + l = n) (u : LpForm Ω p k) :
    (-o).lpFormHodgeStar hkl u = -o.lpFormHodgeStar hkl u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lpFormHodgeStar (-o) hkl u, coeFn_lpFormHodgeStar o hkl u,
    Lp.coeFn_neg (o.lpFormHodgeStar hkl u)] with x h₁ h₂ h₃
  rw [h₁, h₃, Pi.neg_apply, h₂, covectorHodgeStar_neg_orientation]

/-- **The adjoint of the Hodge star of `L²` forms**: `⟪⋆u, v⟫ = (-1) ^ (k l) ⟪u, ⋆v⟫` for an `L²`
form `u` of degree `k` and an `L²` form `v` of degree `l`, where `k + l = n`. -/
theorem inner_lpFormHodgeStar_left (hkl : k + l = n) (hlk : l + k = n) (u : LpForm Ω 2 k)
    (v : LpForm Ω 2 l) :
    ⟪o.lpFormHodgeStar hkl u, v⟫ = (-1 : ℝ) ^ (k * l) * ⟪u, o.lpFormHodgeStar hlk v⟫ := by
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpFormHodgeStar o hkl u, coeFn_lpFormHodgeStar o hlk v] with x h₁ h₂
  rw [h₁, h₂, inner_covectorHodgeStar_left]

end Orientation
