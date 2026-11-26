/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Absolute convergence and average coefficient growth

Absolute convergence at `s` bounds the sum of the absolute values of the first `n`
coefficients by `O(n ^ s.re)`, provided `s.re ≥ 0`. Together with Mathlib's
`LSeriesSummable_of_sum_norm_bigO` (Xavier Roblot), this characterizes an upper bound
on the abscissa of absolute convergence by average coefficient bounds with every
slightly larger exponent, and yields absolute convergence on `Re s > 1` from a real-cutoff
Chebyshev bound `O(x)`. The sums start at one, so the unused coefficient at zero
is unrestricted.
-/

public section

open Asymptotics Filter Finset
open scoped Topology

namespace LSeriesSummable

/-- Absolute convergence at a point of nonnegative real part bounds the absolute
coefficient sums by the corresponding power. -/
theorem isBigO_sum_norm {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s)
    (hs : 0 ≤ s.re) :
    (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  refine isBigO_iff.mpr ⟨∑' k, ‖LSeries.term f s k‖, Eventually.of_forall fun n ↦ ?_⟩
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  calc
    ∑ k ∈ Icc 1 n, ‖f k‖
      = ∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖ * (k : ℝ) ^ s.re := by
        apply sum_congr rfl
        intro k hk
        have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
        rw [LSeries.norm_term_eq, ite_eq_right hk0, div_mul_cancel₀ _
          (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)) _).ne']
    _ ≤ ∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖ * (n : ℝ) ^ s.re := by
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast (mem_Icc.mp hk).2) hs)
          (norm_nonneg _)
    _ = (∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖) * (n : ℝ) ^ s.re :=
        (sum_mul _ _ _).symm
    _ ≤ (∑' k, ‖LSeries.term f s k‖) * (n : ℝ) ^ s.re :=
        mul_le_mul_of_nonneg_right (h.norm.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end LSeriesSummable

namespace TauCeti.LSeries

/-- For a nonnegative `r`, absolute convergence to the right of `r` is equivalent
to average absolute coefficient bounds with every exponent larger than `r`. -/
theorem abscissaOfAbsConv_le_iff_sum_norm_isBigO {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    _root_.LSeries.abscissaOfAbsConv f ≤ (r : EReal) ↔
      ∀ t : ℝ, r < t →
        (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ t := by
  constructor
  · intro h t ht
    have hsum : LSeriesSummable f (t : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (h.trans_lt (by exact_mod_cast ht))
    simpa using hsum.isBigO_sum_norm (by simpa using hr.trans ht.le)
  · intro h
    apply _root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro t ht
    obtain ⟨u, hru, hut⟩ := exists_between ht
    exact LSeriesSummable_of_sum_norm_bigO (h u hru) (hr.trans hru.le) (by simpa using hut)

/-- Under the Chebyshev bound `∑_{1 ≤ n ≤ x} ‖f n‖ = O(x)`, the Dirichlet series of `f`
converges at every `s` with `Re s > 1`. -/
theorem LSeriesSummable_of_isBigO_sum_Icc_norm_id {f : ℕ → ℂ}
    (hcheby : (fun x : ℝ ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] fun x ↦ x)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s := by
  have hnat : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    simpa only [Function.comp_def, Nat.floor_natCast, Real.rpow_one] using
      hcheby.comp_tendsto tendsto_natCast_atTop_atTop
  exact LSeriesSummable_of_sum_norm_bigO hnat zero_le_one hs

end TauCeti.LSeries
