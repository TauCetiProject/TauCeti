/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.FourierChar

/-!
# Finite triangular Fourier sum identity

This file records the finite Fejér triangular Fourier sum identity for the real additive character
`Real.fourierChar`:

* `TauCeti.sum_Icc_max_sub_abs_mul_fourierChar`: for `M ≤ K`,
  `∑ n ∈ Icc (-K) K, max 0 (M - |n|) * e(n * t) = ‖∑ k ∈ range M, e(k * t)‖ ^ 2`.
-/

public section

namespace TauCeti

/-- For `M ≤ K`, the triangular Fourier polynomial over `[-K, K]` equals the squared norm of the
first `M` additive characters `k ↦ Real.fourierChar (k * t)`. -/
theorem sum_Icc_max_sub_abs_mul_fourierChar {M K : ℕ} (hMK : M ≤ K) (t : ℝ) :
    ∑ n ∈ Finset.Icc (-(K : ℤ)) K,
        ((max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) : ℝ) : ℂ) *
          (Real.fourierChar ((n : ℝ) * t) : ℂ) =
      (‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 : ℝ) := by
  have hexp :
      ((‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ Finset.range M ×ˢ Finset.range M,
          (Real.fourierChar ((((p.1 : ℤ) - p.2 : ℤ) : ℝ) * t) : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Real.conj_fourierChar, Real.fourierChar_mul_fourierChar]
    congr 2; push_cast; ring
  have hmem : ∀ p ∈ Finset.range M ×ˢ Finset.range M,
      ((p.1 : ℤ) - p.2) ∈ Finset.Icc (-(K : ℤ)) K := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
    rw [Finset.mem_range] at hi hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [hexp, ← sum_card_filter_nsmul_eq_sum_comp (t := Finset.Icc (-(K : ℤ)) K) hmem
      (fun n ↦ (Real.fourierChar ((n : ℝ) * t) : ℂ))]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hcount :
      ((Finset.range M ×ˢ Finset.range M).filter fun p ↦ (p.1 : ℤ) - p.2 = n).card =
        M - n.natAbs := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_range_sum_range_ite_int_sub_eq_nsmul,
      smul_eq_mul, mul_one]
  rw [hcount, nsmul_eq_mul]
  congr 1
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcast : ((M - n.natAbs : ℕ) : ℝ) = max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) := by
    rw [← habs]
    by_cases hn : n.natAbs ≤ M
    · rw [Nat.cast_sub hn, max_eq_right (sub_nonneg.mpr (Nat.cast_le.mpr hn))]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hn), Nat.cast_zero,
        max_eq_left (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_ge hn)))]
  exact_mod_cast hcast.symm

end TauCeti
