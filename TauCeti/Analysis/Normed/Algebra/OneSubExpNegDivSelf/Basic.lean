/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quotient `(1 - exp (-a)) / a`

This basic file packages the power series representing `(1 - exp (-a)) / a` without requiring `a`
to be invertible. In a complete normed algebra over a normed characteristic-zero field the series is
summable at every point. It is the analytic factor in the differential of a Lie-group exponential
map.

## Main results

* `oneSubExpNegDivSelf`: the series `∑ n, (n + 1)!⁻¹ • (-a)ⁿ`.
* `summable_oneSubExpNegDivSelf`: the series is summable in a complete normed algebra.
* `commute_oneSubExpNegDivSelf`: the series commutes with its argument.
* `mul_oneSubExpNegDivSelf`: multiplying the series by `a` gives `1 - exp (-a)`.
* `oneSubExpNegDivSelf_mul`: the corresponding right-multiplication identity.
* `map_oneSubExpNegDivSelf`: continuous ring homomorphisms preserve the series.

## References

* Mathlib's `spectrum.exp_mem_exp`, whose proof supplies the shifted-exponential series argument
  adapted here.
-/

public section

open NormedSpace

noncomputable section

section Topological

variable {𝕂 A : Type*} [Field 𝕂] [Ring A] [Algebra 𝕂 A] [TopologicalSpace A]
  [IsTopologicalRing A]

variable (𝕂) in
/-- The value of `(1 - exp (-a)) / a` with its removable singularity filled in, defined by a power
series. The series is summable everywhere in the complete normed-algebra setting below. -/
def oneSubExpNegDivSelf (a : A) : A :=
  FormalMultilinearSeries.ofScalarsSum (E := A) (fun n ↦ ((n + 1).factorial⁻¹ : 𝕂)) (-a)

/-- The defining series for `oneSubExpNegDivSelf`. -/
theorem oneSubExpNegDivSelf_eq_tsum (a : A) :
    oneSubExpNegDivSelf 𝕂 a = ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ n :=
  FormalMultilinearSeries.ofScalars_sum_eq _ _

/-- The quotient with its removable singularity filled in takes the value `1` at zero. -/
@[simp]
theorem oneSubExpNegDivSelf_zero : oneSubExpNegDivSelf 𝕂 (0 : A) = 1 := by
  simp [oneSubExpNegDivSelf]

variable [T2Space A]

/-- The filled-in quotient commutes with its argument. -/
theorem commute_oneSubExpNegDivSelf (a : A) : Commute a (oneSubExpNegDivSelf 𝕂 a) := by
  rw [oneSubExpNegDivSelf_eq_tsum]
  exact Commute.tsum_right _ fun n ↦ ((Commute.refl a).neg_right.pow_right n).smul_right _

end Topological

section Normed

variable {𝕂 A : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]

/-- The series defining `oneSubExpNegDivSelf` is summable in a complete normed algebra. -/
theorem summable_oneSubExpNegDivSelf (a : A) :
    Summable fun n : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ n := by
  -- Each term is `(n + 1)⁻¹` times an exponential-series term, and `‖(n + 1)⁻¹‖ < 1` eventually.
  have h : ∀ᶠ n : ℕ in Filter.atTop, ‖((n + 1 : ℕ) : 𝕂)⁻¹‖ < 1 := by
    refine Filter.Tendsto.eventually_lt_const zero_lt_one ?_
    simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕂)).comp
      (Filter.tendsto_add_atTop_nat 1)).norm
  refine .of_norm_bounded_eventually (norm_expSeries_summable' (𝕂 := 𝕂) (-a)) ?_
  filter_upwards [Nat.cofinite_eq_atTop ▸ h] with n hn
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_smul, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hn.le

/-- Multiplying the filled-in quotient on the left by its argument recovers its numerator. -/
@[simp]
theorem mul_oneSubExpNegDivSelf (a : A) :
    a * oneSubExpNegDivSelf 𝕂 a = 1 - exp (-a) := by
  -- Split off the constant term of the exponential series; the tail is `-a` times the quotient.
  rw [← (exp_series_hasSum_exp' (𝕂 := 𝕂) (-a)).tsum_eq,
    (expSeries_summable' (𝕂 := 𝕂) (-a)).tsum_eq_zero_add, oneSubExpNegDivSelf_eq_tsum,
    ← (summable_oneSubExpNegDivSelf a).tsum_mul_left]
  simp [← tsum_neg, pow_succ']

/-- Multiplying the filled-in quotient on the right by its argument recovers its numerator. -/
@[simp]
theorem oneSubExpNegDivSelf_mul (a : A) :
    oneSubExpNegDivSelf 𝕂 a * a = 1 - exp (-a) := by
  rw [← (commute_oneSubExpNegDivSelf a).eq, mul_oneSubExpNegDivSelf]

/-- At an invertible argument, the filled-in quotient is left division by that argument. -/
theorem oneSubExpNegDivSelf_eq_invOf_mul (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = ⅟ a * (1 - exp (-a)) := by
  rw [← mul_oneSubExpNegDivSelf (𝕂 := 𝕂), ← mul_assoc, invOf_mul_self, one_mul]

/-- At an invertible argument, the filled-in quotient is right division by that argument. -/
theorem oneSubExpNegDivSelf_eq_mul_invOf (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = (1 - exp (-a)) * ⅟ a := by
  rw [← oneSubExpNegDivSelf_mul (𝕂 := 𝕂), mul_assoc, mul_invOf_self, mul_one]

end Normed

section Map

variable {𝕂 A B : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
  [ContinuousSMul ℚ 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]
  [Ring B] [Algebra 𝕂 B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]

/-- Any continuous ring homomorphism commutes with `oneSubExpNegDivSelf`. -/
theorem map_oneSubExpNegDivSelf {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) (a : A) :
    f (oneSubExpNegDivSelf 𝕂 a) = oneSubExpNegDivSelf 𝕂 (f a) := by
  rw [oneSubExpNegDivSelf_eq_tsum, oneSubExpNegDivSelf_eq_tsum,
    (summable_oneSubExpNegDivSelf a).map_tsum f hf]
  simp only [map_inv_natCast_smul f 𝕂 𝕂, map_pow, map_neg]

end Map
