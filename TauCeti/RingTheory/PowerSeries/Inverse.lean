/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coefficient bounds for inverses of power series

Over a normed ring, the power-series inverse of a polynomial whose constant coefficient is a unit
has geometrically bounded coefficients. This is what makes sums against such an inverse converge
when the other factor decays faster than any geometric sequence, as for entire series.

## Main results

* `PowerSeries.norm_coeff_invOfUnit_coe_le`: if the constant coefficient of a polynomial `p` is a
  unit `u`, the `k`-th coefficient of the inverse of `p` is at most
  `‖u⁻¹‖ * (1 + ‖u⁻¹‖ * ∑ᵢ ‖pᵢ‖) ^ k`.
-/

public section

namespace PowerSeries

open Finset

variable {R : Type*} [NormedRing R]

/-- **Geometric growth of the inverse of a polynomial.** If the constant coefficient of a
polynomial `p` is a unit `u`, the coefficients of the power series inverse of `p` are bounded by
`‖u⁻¹‖ * (1 + ‖u⁻¹‖ * ∑ᵢ ‖pᵢ‖) ^ k`. -/
theorem norm_coeff_invOfUnit_coe_le (p : Polynomial R) (u : Rˣ) (k : ℕ) :
    ‖coeff k (invOfUnit (p : R⟦X⟧) u)‖ ≤
      ‖(↑u⁻¹ : R)‖ * (1 + ‖(↑u⁻¹ : R)‖ * ∑ i ∈ p.support, ‖p.coeff i‖) ^ k := by
  set A := ‖(↑u⁻¹ : R)‖
  set s := ∑ i ∈ p.support, ‖p.coeff i‖
  have hA : 0 ≤ A := norm_nonneg _
  have hs : 0 ≤ s := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hC : 1 ≤ 1 + A * s := le_add_of_nonneg_right (mul_nonneg hA hs)
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeff_invOfUnit, A]
  rw [coeff_invOfUnit, ite_eq_right hk.ne', neg_mul, norm_neg]
  simp only [Polynomial.coeff_coe]
  -- Each term of the recursion is bounded by `‖pᵢ‖ * A * C ^ (k - 1)`.
  have hterm (x : ℕ × ℕ) : ‖if x.2 < k then p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u)
      else 0‖ ≤ ‖p.coeff x.1‖ * (A * (1 + A * s) ^ (k - 1)) := by
    split_ifs with hx
    · refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (ih x.2 hx).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hC (by omega)) hA)
    · rw [norm_zero]
      positivity
  have hsupp : ∑ x ∈ antidiagonal k, ‖p.coeff x.1‖ ≤ s := by
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_filter_of_ne (p := (· ∈ p.support))
      fun i _ hi ↦ Polynomial.mem_support_iff.mpr fun h ↦ hi (by simp [h])]
    exact sum_le_sum_of_subset_of_nonneg (fun _ hi ↦ (mem_filter.mp hi).2)
      fun _ _ _ ↦ norm_nonneg _
  calc ‖(↑u⁻¹ : R) * ∑ x ∈ antidiagonal k, if x.2 < k then
          p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u) else 0‖
      ≤ A * ∑ x ∈ antidiagonal k, ‖p.coeff x.1‖ * (A * (1 + A * s) ^ (k - 1)) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (sum_le_sum fun x _ ↦ hterm x)) hA)
    _ ≤ A * (s * (A * (1 + A * s) ^ (k - 1))) := by
        rw [← sum_mul]
        gcongr
    _ = A * (A * s) * (1 + A * s) ^ (k - 1) := by ring
    _ ≤ A * (1 + A * s) * (1 + A * s) ^ (k - 1) := by gcongr; linarith
    _ = A * (1 + A * s) ^ k := by
        rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]

end PowerSeries
