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
accounts for the factor `1 / 2` in the cost.

## Main statements

* `TauCeti.norm_sub_sq_div_two_eq_pairingCost_add_add` — the quadratic cost is the pairing cost
  of the inner product plus the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`;
* `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff` — `c`-cyclical monotonicity for the
  quadratic cost is cyclical monotonicity for the inner-product pairing, with
  `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le` its classical
  sum form.

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

end

end
