/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Taylor remainders of the exponential on the imaginary axis

For real `x`, the Taylor polynomial of degree `n - 1` approximates `exp (x * I)` to within
`|x| ^ n / n !` (`TauCeti.norm_exp_ofReal_mul_I_sub_sum_le`). Unlike the bounds for a general
complex argument, which need `‖x‖ ≤ 1`, this holds for every real `x`, because `exp (x * I)` stays
on the unit circle. The two cases used to estimate a characteristic function near the origin are
spelled out for the second-order remainder: it is at most `|x| ^ 3 / 6`
(`TauCeti.norm_exp_ofReal_mul_I_sub_le_cube`) and at most `x ^ 2`
(`TauCeti.norm_exp_ofReal_mul_I_sub_le_sq`). The first is sharp as `x → 0`. The second has the
right order of growth for large `|x|`, where the remainder is asymptotic to `x ^ 2 / 2`.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 26, (26.4).
-/

public section

open Complex Finset Nat

namespace TauCeti

/-- The partial sums of the exponential series along the imaginary axis differentiate to `I`
times the previous partial sum. -/
private theorem hasDerivAt_sum_range_ofReal_mul_I_pow_div (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∑ k ∈ range (n + 1), ((s : ℂ) * I) ^ k / (k ! : ℂ))
      (I * ∑ k ∈ range n, ((t : ℂ) * I) ^ k / (k ! : ℂ)) t := by
  have hI : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * I) I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).mul_const I
  induction n with
  | zero => simpa using hasDerivAt_const t (1 : ℂ)
  | succ n ih =>
    have hpow := (hI.pow (n + 1)).div_const ((n + 1) ! : ℂ)
    convert ih.add hpow using 1
    · ext s
      rw [sum_range_succ _ (n + 1)]
      rfl
    · rw [sum_range_succ, mul_add, Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp

/-- The Taylor remainders of `exp (x * I)` are invariant under `x ↦ -x` in norm. -/
private theorem norm_exp_ofReal_mul_I_sub_sum_neg (n : ℕ) (x : ℝ) :
    ‖exp (↑(-x) * I) - ∑ k ∈ range n, (((-x : ℝ) : ℂ) * I) ^ k / (k ! : ℂ)‖ =
      ‖exp (x * I) - ∑ k ∈ range n, ((x : ℂ) * I) ^ k / (k ! : ℂ)‖ := by
  rw [← Complex.norm_conj (exp (x * I) - _)]
  congr 1
  have hc : (starRingEnd ℂ) ((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I := by simp
  simp only [map_sub, map_sum, map_div₀, map_pow, map_natCast, ← Complex.exp_conj, hc]

/-- **Taylor bound for `exp (x * I)`.** For every real `x` and every `n`, the Taylor polynomial
of degree `n - 1` approximates `exp (x * I)` to within `|x| ^ n / n !`. -/
theorem norm_exp_ofReal_mul_I_sub_sum_le (n : ℕ) (x : ℝ) :
    ‖exp (x * I) - ∑ k ∈ range n, ((x : ℂ) * I) ^ k / (k ! : ℂ)‖ ≤ |x| ^ n / (n ! : ℝ) := by
  -- reduce to `0 ≤ x` by conjugation, then induct on `n` with the fencing theorem
  suffices h : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      ‖exp (x * I) - ∑ k ∈ range n, ((x : ℂ) * I) ^ k / (k ! : ℂ)‖ ≤ x ^ n / (n ! : ℝ) by
    rcases le_total 0 x with hx | hx
    · simpa [abs_of_nonneg hx] using h n x hx
    · rw [abs_of_nonpos hx, ← norm_exp_ofReal_mul_I_sub_sum_neg]
      exact h n (-x) (neg_nonneg.2 hx)
  intro n
  induction n with
  | zero =>
    intro x _
    simp [Complex.norm_exp_ofReal_mul_I]
  | succ n ih =>
    intro x hx
    have hderiv (t : ℝ) : HasDerivAt
        (fun s : ℝ ↦ exp (s * I) - ∑ k ∈ range (n + 1), ((s : ℂ) * I) ^ k / (k ! : ℂ))
        (I * (exp (t * I) - ∑ k ∈ range n, ((t : ℂ) * I) ^ k / (k ! : ℂ))) t := by
      have hexp : HasDerivAt (fun s : ℝ ↦ exp (s * I)) (exp (t * I) * I) t := by
        have hI : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * I) I t := by
          simpa using ((hasDerivAt_id t).ofReal_comp).mul_const I
        exact hI.cexp
      convert hexp.sub (hasDerivAt_sum_range_ofReal_mul_I_pow_div n t) using 1
      ring
    have hB (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ s ^ (n + 1) / ((n + 1) ! : ℝ)) (t ^ n / (n ! : ℝ)) t := by
      convert (hasDerivAt_pow (n + 1) t).div_const ((n + 1) ! : ℝ) using 1
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hderiv t).hasDerivWithinAt) ?_ hB (fun t ht ↦ ?_) ⟨hx, le_rfl⟩
    · simp [sum_range_succ']
    · rw [norm_mul, Complex.norm_I, one_mul]
      exact ih t ht.1

/-- The second-order Taylor remainder of `x ↦ exp (x * I)` is at most `|x| ^ 3 / 6`. -/
theorem norm_exp_ofReal_mul_I_sub_le_cube (x : ℝ) :
    ‖exp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ |x| ^ 3 / 6 := by
  have h := norm_exp_ofReal_mul_I_sub_sum_le 3 x
  have hs : ∑ k ∈ range 3, ((x : ℂ) * I) ^ k / (k ! : ℂ) = 1 + x * I - x ^ 2 / 2 := by
    simp only [sum_range_succ, range_zero, sum_empty]
    simp [Nat.factorial, mul_pow, I_sq]
    ring
  rw [hs] at h
  simpa [Nat.factorial] using h

/-- The second-order Taylor remainder of `x ↦ exp (x * I)` is at most `x ^ 2`. -/
theorem norm_exp_ofReal_mul_I_sub_le_sq (x : ℝ) :
    ‖exp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ x ^ 2 := by
  have h := norm_exp_ofReal_mul_I_sub_sum_le 2 x
  have hs : exp (x * I) - (1 + x * I - x ^ 2 / 2) =
      (exp (x * I) - ∑ k ∈ range 2, ((x : ℂ) * I) ^ k / (k ! : ℂ)) + (x : ℂ) ^ 2 / 2 := by
    simp only [sum_range_succ, range_zero, sum_empty]
    simp
    ring
  have h2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp
  rw [hs]
  refine (norm_add_le _ _).trans ?_
  rw [h2]
  have : |x| ^ 2 / (2 ! : ℝ) = x ^ 2 / 2 := by simp [sq_abs, Nat.factorial]
  linarith

end TauCeti
