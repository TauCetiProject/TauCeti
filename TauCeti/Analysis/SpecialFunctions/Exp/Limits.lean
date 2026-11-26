/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.DSlope

/-!
# Limits of the real exponential

Mathlib records `Real.tendsto_exp_nhds_zero_nhds_one : exp u → 1` as `u → 0`. This file adds
the scaled form `c e^{a u} → c`, which is how a discount factor `K e^{-r τ}` approaches the
undiscounted amount `K` as the time `τ` tends to `0`, and the first-order limit
`(e^{a t} - 1) / t → a`, the difference quotient of `t ↦ e^{a t}` at zero, which identifies the
generator of an exponentially rescaled semigroup. At infinity, it records that an exponentially
decaying bound `c e^{-κ s}`, `κ > 0`, tends to zero as `s → ∞`.

## Main declarations

* `Real.tendsto_mul_exp_mul_nhds_zero`: `c e^{a u} → c` as `u → 0`.
* `Real.le_of_forall_pos_le_exp_mul`: a bound `a ≤ e^{δ c} N` for all `δ > 0` gives `a ≤ N`.
* `Real.tendsto_exp_mul_sub_one_div`: `(e^{a t} - 1) / t → a` as `t → 0`, `t ≠ 0`.
* `Real.eventually_mul_lt_and_exp_mul_sub_one_lt`: near `0`, both `a x` and `e^{b x} - 1` are
  smaller than a given `ε > 0`.
* `Real.isBigO_exp_comp_sub_one`: if `f → 0` and `f = O(g)` along a filter, then
  `e^f - 1 = O(g)`.
* `Real.tendsto_const_mul_exp_neg_mul_atTop`: `c e^{-κ s} → 0` as `s → ∞`, for `κ > 0`.
* `Real.tendsto_exp_neg_mul_log_atTop`: `e^{-z} log z → 0` as `z → ∞`.
* `Real.continuous_update_exp_sub_one_div_zero`: the filled-in quotient
  `Function.update (fun u ↦ (e^u - 1) / u) 0 1` is continuous on `ℝ`.
* `Real.continuous_update_one_sub_exp_neg_div_zero`: the filled-in quotient
  `Function.update (fun t ↦ (1 - e^{-t}) / t) 0 1` is continuous on `ℝ`.
* `Real.tendsto_exp_sub_one_sub_div_sq`: `(e^h - 1 - h) / h² → 1 / 2` as `h → 0`, `h ≠ 0`.
-/

public section

open Asymptotics Filter
open scoped Topology Nat

namespace Real

/-- For all `c` and `a`, `c e^{a u}` tends to `c` as `u → 0`. -/
theorem tendsto_mul_exp_mul_nhds_zero (c a : ℝ) :
    Tendsto (fun u => c * exp (a * u)) (𝓝 0) (𝓝 c) := by
  have h : Continuous fun u => c * exp (a * u) := by fun_prop
  simpa using h.tendsto 0

/-- If `a ≤ e^{δ c} N` for every `δ > 0`, then `a ≤ N`: the limit `δ → 0` that removes a damping
factor such as a Gaussian `e^{δ (z - θ)²}` from a norm bound. -/
theorem le_of_forall_pos_le_exp_mul {a c N : ℝ} (h : ∀ δ > 0, a ≤ exp (δ * c) * N) : a ≤ N :=
  ge_of_tendsto
    ((tendsto_mul_exp_mul_nhds_zero N c).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (eventually_nhdsWithin_of_forall fun δ hδ =>
      (h δ hδ).trans_eq (by rw [mul_comm N, mul_comm c]))

/-- The difference quotient `(e^{a t} - 1) / t` of `t ↦ e^{a t}` at zero tends to `a` as
`t → 0` with `t ≠ 0`. -/
theorem tendsto_exp_mul_sub_one_div (a : ℝ) :
    Tendsto (fun t => (exp (a * t) - 1) / t) (𝓝[≠] 0) (𝓝 a) := by
  simpa [div_eq_inv_mul] using ((hasDerivAt_id (0 : ℝ)).const_mul a).exp.tendsto_slope_zero

/-- For `ε > 0`, both `a x` and `e^{b x} - 1` are smaller than `ε` for `x` near `0`: the choice
of a small parameter making a linear displacement bound and an exponential derivative bound
smaller than `ε`. -/
theorem eventually_mul_lt_and_exp_mul_sub_one_lt (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 0, a * x < ε ∧ exp (b * x) - 1 < ε :=
  (ContinuousAt.eventually_lt (f := fun x ↦ a * x) (by fun_prop) continuousAt_const
      (by simpa using hε)).and
    (ContinuousAt.eventually_lt (f := fun x ↦ exp (b * x) - 1) (by fun_prop) continuousAt_const
      (by simpa using hε))

/-- If `f` tends to zero and `f = O(g)` along a filter, then `e^f - 1 = O(g)`: near zero,
`e^u - 1 = O(u)` (`HasDerivAt.isBigO_sub` for `exp` at `0`). -/
theorem isBigO_exp_comp_sub_one {α F : Type*} [Norm F] {l : Filter α} {f : α → ℝ} {g : α → F}
    (hf : Tendsto f l (𝓝 0)) (hfg : f =O[l] g) : (fun x ↦ exp (f x) - 1) =O[l] g := by
  have h := (hasDerivAt_exp 0).isBigO_sub.comp_tendsto hf
  simp only [Function.comp_def, exp_zero, sub_zero] at h
  exact h.trans hfg

/-- An exponentially decaying bound `c e^{-κ s}` with `κ > 0` tends to zero as `s → ∞`. -/
theorem tendsto_const_mul_exp_neg_mul_atTop (c : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun s => c * exp (-(κ * s))) atTop (𝓝 0) := by
  simpa using (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hκ)).const_mul c

/-- `e^{-z} log z → 0` as `z → ∞`. -/
theorem tendsto_exp_neg_mul_log_atTop :
    Tendsto (fun z : ℝ ↦ exp (-z) * log z) atTop (𝓝 0) := by
  have hpoly : Tendsto (fun z : ℝ ↦ z * exp (-z)) atTop (𝓝 0) := by
    simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero' (g := fun z : ℝ ↦ z * exp (-z)) ?_ ?_ hpoly
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact mul_nonneg (exp_pos _).le (log_nonneg hz)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (log_le_self (by positivity)) (exp_pos _).le

/-- The filled-in quotient `Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1` is continuous on `ℝ`.
-/
theorem continuous_update_exp_sub_one_div_zero :
    Continuous (Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1) := by
  have heq : Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1 = dslope exp 0 := by
    ext u
    rcases eq_or_ne u 0 with rfl | hu
    · simp [dslope_same]
    · simp [Function.update_of_ne hu, dslope_of_ne _ hu, slope_def_field]
  rw [heq, ← continuousOn_univ]
  exact (continuousOn_dslope univ_mem).mpr ⟨continuous_exp.continuousOn, differentiableAt_exp⟩

/-- The filled-in quotient `Function.update (fun t : ℝ ↦ (1 - exp (-t)) / t) 0 1` is continuous on
`ℝ`. -/
theorem continuous_update_one_sub_exp_neg_div_zero :
    Continuous (Function.update (fun t : ℝ ↦ (1 - exp (-t)) / t) 0 1) := by
  have heq : Function.update (fun t : ℝ ↦ (1 - exp (-t)) / t) 0 1 =
      fun t : ℝ ↦ Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1 (-t) := by
    ext t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · simp [ht]
      ring
  rw [heq]
  exact continuous_update_exp_sub_one_div_zero.comp continuous_neg

/-- Second-order difference quotient `(e^h - 1 - h) / h² → 1 / 2` as `h → 0`, `h ≠ 0`. -/
theorem tendsto_exp_sub_one_sub_div_sq :
    Tendsto (fun h : ℝ ↦ (exp h - 1 - h) / h ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε / 2), lt_min zero_lt_one (half_pos hε), fun h hh hd ↦ ?_⟩
  have hh0 : h ≠ 0 := Set.mem_compl_singleton_iff.mp hh
  rw [Real.dist_eq, sub_zero] at hd
  have hbound := exp_bound (hd.le.trans (min_le_left _ _)) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    div_one] at hbound
  have hdiv : |(exp h - 1 - h) / h ^ 2 - 1 / 2| =
      |exp h - (1 + h + h ^ 2 / 2)| / |h| ^ 2 := by
    rw [← abs_pow, ← abs_div]
    congr 1
    field_simp [hh0]
    ring
  rw [Real.dist_eq, hdiv]
  calc |exp h - (1 + h + h ^ 2 / 2)| / |h| ^ 2
      ≤ (|h| ^ 3 * ((3 + 1 : ℕ) / ((3 : ℕ)! * (3 : ℕ)))) / |h| ^ 2 := by
        gcongr
        simpa [sq_abs] using hbound
    _ = (2 / 9 : ℝ) * |h| := by
        have ha : |h| ≠ 0 := abs_ne_zero.mpr hh0
        have hfac : ((3 + 1 : ℕ) / ((3 : ℕ)! * (3 : ℕ)) : ℝ) = 2 / 9 := by
          norm_num [Nat.factorial]
        rw [hfac]
        field_simp [ha]
    _ < ε := by linarith [hd.trans_le (min_le_right _ _), abs_nonneg h]

end Real
