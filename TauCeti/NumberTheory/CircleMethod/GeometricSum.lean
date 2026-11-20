/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.FourierChar.Basic

/-!
# Geometric exponential sums

An unweighted sum of the real Fourier character over consecutive integers is bounded both
by the length of the sum and, off the integers, by the reciprocal of twice the distance of
the phase from an integer. This is the geometric-sum estimate used to bound additive twists in
the circle method (Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 25).

For an integral phase the summands are all one, so the bound uses the length alone rather than
Lean's zero reciprocal. The interval form accommodates the shifted ranges in bilinear sums.
-/

public section

open Finset Real
open scoped FourierTransform

namespace TauCeti

/-- An exponential sum over a translated interval factors into its initial phase and a
geometric progression of the interval's length. -/
theorem sum_Ico_fourierChar_eq_mul_sum_range (M N : ℕ) (β : ℝ) :
    (∑ n ∈ Ico M N, (𝐞 ((n : ℝ) * β) : ℂ)) =
      (𝐞 ((M : ℝ) * β) : ℂ) * ∑ n ∈ range (N - M), (𝐞 β : ℂ) ^ n := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Nat.cast_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul, ← nsmul_eq_mul n β,
    AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- The closed form of the geometric exponential sum over `1, …, N` at a nonintegral phase. -/
theorem sum_fourierChar_eq (N : ℕ) {β : ℝ} (hβ : (β : UnitAddCircle) ≠ 0) :
    (∑ n ∈ Icc 1 N, (𝐞 ((n : ℝ) * β) : ℂ)) =
      (𝐞 β : ℂ) * ((𝐞 ((N : ℝ) * β) : ℂ) - 1) / ((𝐞 β : ℂ) - 1) := by
  have h₁ : (𝐞 β : ℂ) ≠ 1 := fun he ↦ hβ (fourierChar_eq_one_iff.mp (Circle.coe_eq_one.mp he))
  rw [← Finset.Ico_succ_right_eq_Icc, sum_Ico_fourierChar_eq_mul_sum_range]
  simp only [Nat.succ_eq_succ, Nat.succ_sub_one, Nat.cast_one, one_mul]
  rw [geom_sum_eq h₁, ← mul_div_assoc, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

/-- On `[M, N)`, the geometric exponential sum is bounded by its length and, when the phase
is not an integer, by the reciprocal of twice its distance from the integers. -/
theorem norm_sum_Ico_fourierChar_le (M N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Ico M N, (𝐞 ((n : ℝ) * β) : ℂ)‖ ≤
      if (β : UnitAddCircle) = 0 then ((N - M : ℕ) : ℝ)
      else min ((N - M : ℕ) : ℝ) (1 / (2 * ‖(β : UnitAddCircle)‖)) := by
  have hlen : ‖∑ n ∈ Ico M N, (𝐞 ((n : ℝ) * β) : ℂ)‖ ≤ ((N - M : ℕ) : ℝ) := by
    simpa using (norm_sum_le (Ico M N) fun n ↦ (𝐞 ((n : ℝ) * β) : ℂ))
  split_ifs with hβ
  · exact hlen
  refine le_min hlen ?_
  -- Clear the denominator using the geometric identity before estimating the numerator.
  rw [sum_Ico_fourierChar_eq_mul_sum_range, norm_mul, Circle.norm_coe, one_mul]
  have hgeom := congrArg norm (geom_sum_mul (𝐞 β : ℂ) (N - M))
  rw [norm_mul, Real.norm_fourierChar_sub_one] at hgeom
  have hnum : ‖(𝐞 β : ℂ) ^ (N - M) - 1‖ ≤ 2 := by
    simpa [one_add_one_eq_two] using (norm_sub_le ((𝐞 β : ℂ) ^ (N - M)) (1 : ℂ))
  have hsin := Real.two_mul_norm_unitAddCircle_le_abs_sin β
  rw [le_div_iff₀ (mul_pos two_pos (norm_pos_iff.mpr hβ))]
  set S : ℂ := ∑ n ∈ range (N - M), (𝐞 β : ℂ) ^ n
  calc
    ‖S‖ * (2 * ‖(β : UnitAddCircle)‖) ≤ ‖S‖ * |sin (π * β)| :=
      mul_le_mul_of_nonneg_left hsin (norm_nonneg S)
    _ = ‖(𝐞 β : ℂ) ^ (N - M) - 1‖ / 2 := by linarith only [hgeom]
    _ ≤ 1 := by linarith only [hnum]

/-- The geometric exponential sum over `1, …, N` is bounded by `N` and, off the integers,
by the reciprocal of twice the distance of the phase from an integer. -/
theorem norm_sum_fourierChar_le (N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Icc 1 N, (𝐞 ((n : ℝ) * β) : ℂ)‖ ≤
      if (β : UnitAddCircle) = 0 then (N : ℝ)
      else min (N : ℝ) (1 / (2 * ‖(β : UnitAddCircle)‖)) := by
  rw [← Finset.Ico_succ_right_eq_Icc]
  simpa only [Nat.succ_eq_succ, Nat.succ_sub_one] using
    norm_sum_Ico_fourierChar_le 1 (Order.succ N) β

-- At zero the length bound is attained. Substituting the zero reciprocal in the minimum
-- at this phase would therefore give a false bound for every positive `N`.
example (N : ℕ) : ‖∑ n ∈ Icc 1 N, (𝐞 ((n : ℝ) * 0) : ℂ)‖ = (N : ℝ) := by
  simp

end TauCeti
