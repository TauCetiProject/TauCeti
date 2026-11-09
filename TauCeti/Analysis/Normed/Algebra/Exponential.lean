/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

* `NormedSpace.contDiff_exp`: the exponential is smooth of every order, including analytic.
* `NormedSpace.tendsto_exp_nhds_zero_nhds_one`: the exponential tends to `1` at the origin.
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
* `TauCeti.exists_norm_exp_smul_le_of_norm_exp_smul_lt_one`: if `‖exp (τ • x)‖ < 1` for one time
  `τ > 0`, then `‖exp (t • x)‖` decays exponentially as `t → ∞`.
-/

public section

open Asymptotics Filter Topology
open scoped Nat ContDiff

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

/-- The exponential on a complete normed algebra is smooth of every order, including analytic. -/
theorem contDiff_exp {k : ℕ∞ω} : ContDiff 𝕂 k (exp : A → A) :=
  contDiff_iff_contDiffAt.mpr fun x ↦ (exp_analytic (𝕂 := 𝕂) x).contDiffAt.of_le le_top

include 𝕂 in
/-- The exponential on a complete normed algebra is continuous at `0`, with value `1`. -/
theorem tendsto_exp_nhds_zero_nhds_one : Tendsto (exp : A → A) (𝓝 (0 : A)) (𝓝 (1 : A)) := by
  simpa only [exp_zero] using (exp_analytic (𝕂 := 𝕂) (0 : A)).continuousAt.tendsto

/-- **The quadratic Taylor estimate for the exponential.**  In a complete normed algebra,
`exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` as `x → 0`. -/
theorem isBigO_exp_sub_quadratic :
    (fun x : A ↦ exp x - (1 + x + (2⁻¹ : 𝕂) • x ^ 2)) =O[𝓝 (0 : A)] fun x ↦ ‖x‖ ^ 3 := by
  simpa only [zero_add, expSeries_partialSum_three] using
    (exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A)).isBigO_sub_partialSum_pow 3

/-! ### Additivity and cancellation in a complete normed algebra -/

section Normed

variable {𝕂 A : Type*} [RCLike 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]
  [CompleteSpace A]

/-- The exponential is multiplicative on scalar multiples of a fixed element:
`exp ((s + t) • a) = exp (s • a) * exp (t • a)`. -/
theorem exp_add_smul (a : A) (s t : 𝕂) :
    exp ((s + t) • a) = exp (s • a) * exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ 𝕂 A
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

/-- **Exponential decay from a single contraction.** In a complete normed real algebra, if
`‖exp (τ • x)‖ < 1` for some `τ > 0`, then `‖exp (t • x)‖ ≤ K * Real.exp (-α * t)` for all
`t ≥ 0`, with constants `K` and `α > 0`. -/
theorem exists_norm_exp_smul_le_of_norm_exp_smul_lt_one [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (x : 𝔸) {τ : ℝ} (hτ : 0 < τ) (h : ‖exp (τ • x)‖ < 1) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • x)‖ ≤ K * Real.exp (-α * t) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  -- Write `t = n τ + s` with `0 ≤ s < τ`: then `exp (t • x) = exp (s • x) * exp (τ • x) ^ n`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Set.Icc 0 τ, ‖exp (s • x)‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn
      (exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
  set q := max ‖exp (τ • x)‖ (1 / 2)
  have hq0 : 0 < q := lt_max_of_lt_right (by norm_num)
  have hlog : Real.log q < 0 := Real.log_neg hq0 (max_lt h (by norm_num))
  refine ⟨M / q, -Real.log q / τ, div_pos (neg_pos.mpr hlog) hτ, fun t ht ↦ ?_⟩
  set n := ⌊t / τ⌋₊
  have hn : (n : ℝ) * τ ≤ t := (le_div_iff₀ hτ).mp (Nat.floor_le (div_nonneg ht hτ.le))
  have hn' : t / τ ≤ n + 1 := (Nat.lt_floor_add_one (t / τ)).le
  have hn'' : t ≤ (n + 1) * τ := (div_le_iff₀ hτ).mp hn'
  have hsplit : exp (t • x) = exp ((t - n * τ) • x) * exp (τ • x) ^ n := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← exp_add_smul]
    ring_nf
  have hM0 : ‖exp ((t - n * τ) • x)‖ ≤ M := hM _ ⟨by linarith, by linarith⟩
  have hM0' : 0 ≤ M := (norm_nonneg _).trans hM0
  have hpow : ‖exp (t • x)‖ ≤ M * q ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0] at hM0
      rwa [hsplit, h0, pow_zero, mul_one, pow_zero, mul_one]
    · rw [hsplit]
      refine (norm_mul_le _ _).trans (mul_le_mul hM0 ?_ (norm_nonneg _) hM0')
      exact (norm_pow_le' _ hpos).trans (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) n)
  calc ‖exp (t • x)‖ ≤ M * q ^ n := hpow
    _ = M / q * Real.exp ((n + 1 : ℕ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq0, pow_succ]
        field_simp
    _ ≤ M / q * Real.exp (-(-Real.log q / τ) * t) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (div_nonneg hM0' hq0.le)
        calc ((n + 1 : ℕ) : ℝ) * Real.log q ≤ t / τ * Real.log q := by
              push_cast
              exact mul_le_mul_of_nonpos_right hn' hlog.le
          _ = -(-Real.log q / τ) * t := by ring

/-- If the unit has norm at most one, then the norm of the exponential of a real scalar multiple
of the unit is at most the corresponding scalar exponential. -/
theorem norm_exp_smul_one_le [NormedAlgebra ℝ 𝔸] (h_one : ‖(1 : 𝔸)‖ ≤ 1) (c : ℝ) :
    ‖exp (c • (1 : 𝔸))‖ ≤ Real.exp c := by
  rw [exp_smul_one, ← Real.exp_eq_exp_ℝ, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg c)]
  exact mul_le_of_le_one_right (Real.exp_nonneg c) h_one

end TauCeti
