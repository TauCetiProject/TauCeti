/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.AddCircle
import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter

/-!
# Geometric exponential sums over shifted intervals

An unweighted sum of the real Fourier character over consecutive integers factors into an
initial phase and a geometric progression. In particular, shifting the interval does not change
the norm. The bound for `[1, N]` in `TauCeti.norm_sum_expTwoPiI_le` (Davenport,
*Multiplicative Number Theory*, 3rd ed., Chapter 25) thus also applies to shifted intervals,
including the empty interval.
-/

public section

open Finset
open scoped FourierTransform

namespace Nat

/-- An exponential sum over a translated interval factors into its initial phase and a
geometric progression of the interval's length. -/
theorem sum_Ico_fourierChar_eq_mul_sum_range (M N : ℕ) (β : ℝ) :
    (∑ n ∈ Ico M N, (𝐞 ((n : ℝ) * β) : ℂ)) =
      (𝐞 ((M : ℝ) * β) : ℂ) * ∑ n ∈ range (N - M), (𝐞 β : ℂ) ^ n := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hpow : 𝐞 ((n : ℝ) * β) = 𝐞 β ^ n := by
    simpa only [nsmul_eq_mul] using AddChar.map_nsmul_eq_pow (𝐞 : AddChar ℝ Circle) n β
  simp [add_mul, AddChar.map_add_eq_mul, hpow]

/-- On `[M, N)`, the geometric exponential sum is bounded by its length and, when the phase
is not an integer, by the reciprocal of twice its distance from the integers. -/
theorem norm_sum_Ico_fourierChar_le (M N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Ico M N, (𝐞 ((n : ℝ) * β) : ℂ)‖ ≤
      if (β : UnitAddCircle) = 0 then ((N - M : ℕ) : ℝ)
      else min ((N - M : ℕ) : ℝ) (1 / (2 * ‖(β : UnitAddCircle)‖)) := by
  have h := TauCeti.norm_sum_expTwoPiI_le (N - M) β
  simp only [TauCeti.expTwoPiI_eq_fourierChar, TauCeti.distInt_eq_norm, norm_eq_zero] at h
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_fourierChar_eq_mul_sum_range] at h
  simpa only [sum_Ico_fourierChar_eq_mul_sum_range, norm_mul, Circle.norm_coe, one_mul,
    Nat.add_sub_cancel] using h

end Nat
