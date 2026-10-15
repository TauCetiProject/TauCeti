/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing

/-!
# The quadratic transport cost and its cyclically monotone sets

On a real inner product space `E`, the quadratic transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`
differs from the pairing cost `-⟪x, y⟫` of `TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing`
by the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. Split terms are invisible to cyclical
monotonicity, so a set is `c`-cyclically monotone for the quadratic cost exactly when it is
cyclically monotone in the classical sense `∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫`. The
`c`-transform vocabulary of the quadratic cost is the Legendre–Fenchel vocabulary of the inner
product; that dictionary is recorded in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic`. Every statement in this file
accounts for the factor `1 / 2` in the cost. The same factor connects a minimizer of the
half-squared cost to a minimizer of squared ground distance, as used by `W₂`.

## Main statements

* `TauCeti.norm_sub_sq_div_two_eq_pairingCost_add_add` — the quadratic cost is the pairing cost
  of the inner product plus the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`;
* `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff` — `c`-cyclical monotonicity for the
  quadratic cost is cyclical monotonicity for the inner-product pairing, with
  `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le` its classical
  sum form.
* `TauCeti.edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two`,
  `TauCeti.isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two` and
  `TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two` — convert between the
  half-squared Brenier cost and the squared-distance cost without changing optimal couplings.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1, where the quadratic cost is reduced to the inner-product pairing.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic cost is the inner-product pairing cost plus the split term
`‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. -/
theorem norm_sub_sq_div_two_eq_pairingCost_add_add :
    (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) =
      fun p => pairingCost (innerₗ E) p + ‖p.1‖ ^ 2 / 2 + ‖p.2‖ ^ 2 / 2 := by
  funext p
  rw [pairingCost_apply, innerₗ_apply_apply, norm_sub_sq_real]
  ring

/-- `c`-cyclical monotonicity for the quadratic cost is cyclical monotonicity for the
inner-product pairing. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      IsCyclicallyMonotone (pairingCost (innerₗ E)) S := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCyclicallyMonotone_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      fun y => ‖y‖ ^ 2 / 2]

/-- `c`-cyclical monotonicity for the quadratic cost is the classical cyclical monotonicity
condition: rearranging the targets of finitely many points of the set does not increase the
total inner product. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∀ (n : ℕ) (x y : Fin n → E), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫ := by
  rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff, isCyclicallyMonotone_pairingCost_iff]
  simp only [innerₗ_apply_apply]

end TauCeti

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]

omit [MeasurableSpace F] in
/-- Squared distance is twice the half-squared-displacement cost. This identity accounts for
the factor `1 / 2` in the quadratic Brenier cost when reading a plan as a `W₂` plan. -/
theorem edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two (z : F × F) :
    edist z.1 z.2 ^ (2 : ℝ) =
      (2 : ℝ≥0∞) * ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by
  rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), dist_eq_norm]
  rw [Real.rpow_ofNat]
  calc
    ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) =
        ENNReal.ofReal (2 * (‖z.1 - z.2‖ ^ 2 / 2)) := congrArg _ (by ring)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- A coupling optimal for the half-squared-displacement cost is optimal for squared distance.
The factor of two is positive, so it preserves the minimizing plans even when the value is
infinite. -/
theorem isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two
    {μ ν : Measure F} {π : Measure (F × F)}
    (hπ : IsOptimalCoupling
      (fun z ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν) :
    IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ)) π μ ν := by
  simpa only [← edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two] using
    hπ.const_mul (a := 2) ENNReal.ofNat_ne_top

/-- A coupling optimal for squared distance is optimal for the half-squared-displacement cost.
The factor of one half is positive and finite, so it preserves the minimizing plans even when the
value is infinite. -/
theorem isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two
    {μ ν : Measure F} {π : Measure (F × F)}
    (hπ : IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ)) π μ ν) :
    IsOptimalCoupling (fun z ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν := by
  simpa only [edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two,
    ENNReal.inv_mul_cancel_left two_ne_zero ENNReal.ofNat_ne_top] using
    hπ.const_mul (a := 2⁻¹) (ENNReal.inv_ne_top.2 two_ne_zero)

end TauCeti

end

end
