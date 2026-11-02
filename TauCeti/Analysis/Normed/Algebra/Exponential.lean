/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The normed-algebra exponential

For an algebra `A` over a field, with `A` a topological ring, the third partial sum of
`NormedSpace.expSeries` is `1 + x + 2⁻¹ • x ^ 2`. This identity needs no norm or completeness
assumption.
In a complete normed algebra, the exponential agrees with this quadratic truncation to third
order at the origin, and it is multiplicative on scalar multiples of a fixed element
(`NormedSpace.exp_add_smul`). This file records that estimate in `Asymptotics.IsBigO` form.
It also bounds the norm of the exponential by a scalar exponential, comparing the exponential
series termwise with the series of `Real.exp`.

The exponential is analytic at `0` with power series `NormedSpace.expSeries`, so the statement is
the Taylor formula `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` at `n = 3`, once the third partial
sum of `expSeries` is evaluated. The quadratic order pins down the second-order term of the
Baker--Campbell--Hausdorff expansion.

## Main results

* `NormedSpace.expSeries_partialSum_three`: the third partial sum of the exponential series is
  `1 + x + 2⁻¹ • x ^ 2`.
* `NormedSpace.isBigO_exp_sub_quadratic`: `exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` at the
  origin.
* `NormedSpace.exp_add_smul`: `exp` is multiplicative on scalar multiples of a fixed element.
* `TauCeti.norm_exp_le_mul_exp_of_norm_pow_le`: if `‖x ^ n‖ ≤ M * r ^ n` for every `n`, then
  `‖exp x‖ ≤ M * Real.exp r`; in particular `‖exp x‖ ≤ Real.exp ‖x‖` when `‖1‖ ≤ 1`
  (`TauCeti.norm_exp_le_exp_norm`, with the scalar-multiple form `TauCeti.norm_exp_smul_le`), and
  power-bounded elements satisfy `‖exp (s • b)‖ ≤ M * Real.exp ‖s‖`
  (`TauCeti.norm_exp_smul_le_mul_exp_of_norm_pow_le`).
* `TauCeti.exp_smul_one`: the exponential of a scalar multiple of the unit.
-/

public section

open Asymptotics Filter Topology
open scoped Nat

noncomputable section

namespace NormedSpace

section Algebra

variable (𝕂 : Type*) {A : Type*} [Field 𝕂] [Ring A] [Algebra 𝕂 A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- For an algebra `A` over a field, with `A` a topological ring, the third partial sum of the
exponential series is the quadratic truncation `1 + x + 2⁻¹ • x ^ 2`. -/
@[simp]
theorem expSeries_partialSum_three (x : A) :
    (expSeries 𝕂 A).partialSum 3 x = 1 + x + (2⁻¹ : 𝕂) • x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, expSeries_apply_eq,
    Nat.factorial]

end Algebra

variable (𝕂 : Type*) {A : Type*} [NontriviallyNormedField 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]
  [CharZero 𝕂] [ContinuousSMul ℚ 𝕂] [CompleteSpace A]

/-- **The quadratic Taylor estimate for the exponential.**  In a complete normed algebra,
`exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` as `x → 0`. -/
theorem isBigO_exp_sub_quadratic :
    (fun x : A ↦ exp x - (1 + x + (2⁻¹ : 𝕂) • x ^ 2)) =O[𝓝 (0 : A)] fun x ↦ ‖x‖ ^ 3 := by
  simpa only [zero_add, expSeries_partialSum_three] using
    (exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A)).isBigO_sub_partialSum_pow 3

/-! ### Additivity and cancellation in a complete normed algebra -/

section Normed

variable {𝕂 A : Type*} [RCLike 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [NormedAlgebra ℚ A]
  [CompleteSpace A]

/-- The exponential is multiplicative on scalar multiples of a fixed element:
`exp ((s + t) • a) = exp (s • a) * exp (t • a)`. -/
theorem exp_add_smul (a : A) (s t : 𝕂) :
    exp ((s + t) • a) = exp (s • a) * exp (t • a) := by
  rw [add_smul, exp_add_of_commute (((Commute.refl a).smul_left _).smul_right _)]

end Normed

end NormedSpace

namespace TauCeti

open NormedSpace

/-! ### Norm bounds by a scalar exponential -/

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- In a normed `ℚ`-algebra, if the powers of `x` satisfy `‖x ^ n‖ ≤ M * r ^ n`, then
`‖exp x‖ ≤ M * Real.exp r`. -/
theorem norm_exp_le_mul_exp_of_norm_pow_le [NormedAlgebra ℚ 𝔸] {x : 𝔸} {M r : ℝ}
    (h : ∀ n : ℕ, ‖x ^ n‖ ≤ M * r ^ n) : ‖exp x‖ ≤ M * Real.exp r := by
  have hr := (exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r).mul_left M
  rw [exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ]
  refine tsum_of_norm_bounded hr fun n => ?_
  have hfact : ‖((n ! : ℚ))⁻¹‖ = ((n ! : ℝ))⁻¹ := by
    rw [← Rat.norm_cast_real]
    simp
  rw [norm_smul, hfact, smul_eq_mul, mul_left_comm]
  gcongr
  exact h n

/-- In a normed `ℚ`-algebra whose unit has norm at most one, the exponential is norm-bounded by
the scalar exponential of the norm: `‖exp x‖ ≤ Real.exp ‖x‖`. -/
theorem norm_exp_le_exp_norm [NormedAlgebra ℚ 𝔸] (h_one : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hpow (n : ℕ) : ‖x ^ n‖ ≤ 1 * ‖x‖ ^ n := by
    rw [one_mul]
    cases n with
    | zero => simpa only [pow_zero] using h_one
    | succ m => exact norm_pow_le' x m.succ_pos
  simpa only [one_mul] using norm_exp_le_mul_exp_of_norm_pow_le hpow

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 𝔸]

/-- In a normed algebra whose unit has norm at most one, the exponential of a scalar multiple
satisfies `‖exp (t • a)‖ ≤ Real.exp (‖a‖ * ‖t‖)`. -/
theorem norm_exp_smul_le (h_one : ‖(1 : 𝔸)‖ ≤ 1) (a : 𝔸) (t : 𝕜) :
    ‖exp (t • a)‖ ≤ Real.exp (‖a‖ * ‖t‖) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕜 𝔸
  rw [mul_comm, ← norm_smul]
  exact norm_exp_le_exp_norm h_one _

/-- If every power of `b` has norm at most `M`, then `‖exp (s • b)‖ ≤ M * Real.exp ‖s‖`. -/
theorem norm_exp_smul_le_mul_exp_of_norm_pow_le {b : 𝔸} {M : ℝ} (s : 𝕜)
    (hpow : ∀ n : ℕ, ‖b ^ n‖ ≤ M) : ‖exp (s • b)‖ ≤ M * Real.exp ‖s‖ := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕜 𝔸
  refine norm_exp_le_mul_exp_of_norm_pow_le fun n => ?_
  rw [smul_pow, norm_smul, norm_pow, mul_comm]
  gcongr
  exact hpow n

/-- The exponential of a scalar multiple of the unit is the corresponding scalar exponential
times the unit. -/
@[simp]
theorem exp_smul_one (c : 𝕜) : exp (c • (1 : 𝔸)) = exp c • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm]

end RCLike

/-- If the unit has norm at most one, then the norm of the exponential of a real scalar multiple
of the unit is at most the corresponding scalar exponential. -/
theorem norm_exp_smul_one_le [NormedAlgebra ℝ 𝔸] (h_one : ‖(1 : 𝔸)‖ ≤ 1) (c : ℝ) :
    ‖exp (c • (1 : 𝔸))‖ ≤ Real.exp c := by
  rw [exp_smul_one, ← Real.exp_eq_exp_ℝ, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg c)]
  exact mul_le_of_le_one_right (Real.exp_nonneg c) h_one

end TauCeti
