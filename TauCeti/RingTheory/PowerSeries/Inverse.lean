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

Over a seminormed ring, the power-series inverse of a polynomial whose constant coefficient is a
unit has geometrically bounded coefficients. This is what makes sums against such an inverse
converge when the other factor decays faster than any geometric sequence, as for entire series.

## Main results

* `PowerSeries.norm_coeff_invOfUnit_coe_le`: for a polynomial `p` and a unit `u`, the `k`-th
  coefficient of `invOfUnit p u` is at most `‖u⁻¹‖ * (1 + ‖u⁻¹‖ * ∑ᵢ ‖pᵢ‖) ^ k`. When `u` is the
  constant coefficient of `p`, `invOfUnit p u` is the inverse of `p`.
-/

public section

namespace PowerSeries

open Finset

variable {R : Type*} [SeminormedRing R]

/-- **Geometric growth of the inverse of a polynomial.** For a polynomial `p` and any unit `u`,
the `k`-th coefficient of `invOfUnit p u` is bounded by `‖u⁻¹‖ * (1 + ‖u⁻¹‖ * ∑ᵢ ‖pᵢ‖) ^ k`.
When `u` is the constant coefficient of `p`, `invOfUnit p u` is the power series inverse of `p`
(`PowerSeries.mul_invOfUnit`), so this bounds the coefficients of that inverse. -/
theorem norm_coeff_invOfUnit_coe_le (p : Polynomial R) (u : Rˣ) (k : ℕ) :
    ‖coeff k (invOfUnit (p : R⟦X⟧) u)‖ ≤
      ‖(↑u⁻¹ : R)‖ * (1 + ‖(↑u⁻¹ : R)‖ * ∑ i ∈ p.support, ‖p.coeff i‖) ^ k := by
  set A := ‖(↑u⁻¹ : R)‖
  set s := ∑ i ∈ p.support, ‖p.coeff i‖
  have hC : 1 ≤ 1 + A * s := le_add_of_nonneg_right (by positivity)
  induction k using Nat.strong_induction_on with | _ k ih => ?_
  obtain _ | k := k
  · simp [coeff_invOfUnit, A]
  rw [coeff_invOfUnit, ite_eq_right k.succ_ne_zero, neg_mul, norm_neg]
  simp only [Polynomial.coeff_coe]
  -- Each term of the recursion is bounded by `‖pᵢ‖ * (A * (1 + A * s) ^ k)`.
  have hterm (x : ℕ × ℕ) : ‖if x.2 < k + 1 then p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u)
      else 0‖ ≤ ‖p.coeff x.1‖ * (A * (1 + A * s) ^ k) := by
    split_ifs with hx
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      exact (ih _ hx).trans (by gcongr; omega)
    · simp only [norm_zero]
      positivity
  have hsupp : ∑ x ∈ antidiagonal (k + 1), ‖p.coeff x.1‖ ≤ s := by
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_filter_of_ne (p := (· ∈ p.support))
      fun i _ hi ↦ Polynomial.mem_support_iff.mpr fun h ↦ hi (by simp [h])]
    exact sum_le_sum_of_subset_of_nonneg (fun _ hi ↦ (mem_filter.mp hi).2)
      fun _ _ _ ↦ norm_nonneg _
  calc ‖(↑u⁻¹ : R) * ∑ x ∈ antidiagonal (k + 1), if x.2 < k + 1 then
          p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u) else 0‖
      ≤ A * ∑ x ∈ antidiagonal (k + 1), ‖p.coeff x.1‖ * (A * (1 + A * s) ^ k) :=
        (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (sum_le_sum fun x _ ↦ hterm x)) (norm_nonneg _)
    _ ≤ A * (s * (A * (1 + A * s) ^ k)) := by
        rw [← sum_mul]
        gcongr
    _ = A * (A * s) * (1 + A * s) ^ k := by ring
    _ ≤ A * (1 + A * s) * (1 + A * s) ^ k := by gcongr; linarith
    _ = A * (1 + A * s) ^ (k + 1) := by ring

end PowerSeries
