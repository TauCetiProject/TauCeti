/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Limits of the real and complex exponential

Mathlib records `Real.tendsto_exp_nhds_zero_nhds_one : exp u → 1` as `u → 0`. This file adds
the scaled form `c e^{a u} → c`, which is how a discount factor `K e^{-r τ}` approaches the
undiscounted amount `K` as the time `τ` tends to `0`, and the first-order limit
`(e^{a t} - 1) / t → a`, the difference quotient of `t ↦ e^{a t}` at zero, which identifies the
generator of an exponentially rescaled semigroup. At infinity, it records that an exponentially
decaying bound `c e^{-κ s}`, `κ > 0`, tends to zero as `s → ∞`. For the complex exponential on a
finite index set `s`, it records that `exp (t * f a)` is uniformly close to `1` on `s` for small
positive `t`.

## Main declarations

* `Real.tendsto_mul_exp_mul_nhds_zero`: `c e^{a u} → c` as `u → 0`.
* `Real.le_of_forall_pos_le_exp_mul`: a bound `a ≤ e^{δ c} N` for all `δ > 0` gives `a ≤ N`.
* `Real.tendsto_exp_mul_sub_one_div`: `(e^{a t} - 1) / t → a` as `t → 0`, `t ≠ 0`.
* `Real.eventually_mul_lt_and_exp_mul_sub_one_lt`: near `0`, both `a x` and `e^{b x} - 1` are
  smaller than a given `ε > 0`.
* `Real.isBigO_exp_comp_sub_one`: if `f → 0` and `f = O(g)` along a filter, then
  `e^f - 1 = O(g)`.
* `Real.tendsto_const_mul_exp_neg_mul_atTop`: `c e^{-κ s} → 0` as `s → ∞`, for `κ > 0`.
* `Complex.exists_pos_forall_mem_norm_exp_mul_sub_lt`: for a finite set `s` and `f : α → ℂ`,
  there exists `t > 0` such that `‖exp (t * f a) - 1‖ < ε` for all `a ∈ s`.
-/

public section

open Asymptotics Filter
open scoped Topology

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

end Real

namespace Complex

/-- For a finite set `s` and a function `f : α → ℂ`, for every `ε > 0` there exists `t > 0` such
that `exp (t * f a)` lies within `ε` of `1` for every `a ∈ s`. -/
theorem exists_pos_forall_mem_norm_exp_mul_sub_lt {α : Type*} (s : Finset α) (f : α → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ a ∈ s, ‖exp ((t : ℂ) * f a) - 1‖ < ε := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ a ∈ s, ‖exp ((t : ℂ) * f a) - 1‖ < ε := by
    refine (Filter.eventually_all_finset s).mpr fun a _ ↦ ?_
    have hcont : Continuous fun t : ℝ ↦ exp ((t : ℂ) * f a) := by fun_prop
    have ht0 : Tendsto (fun t : ℝ ↦ exp ((t : ℂ) * f a)) (𝓝 0) (𝓝 1) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht0 ε hε
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, hr_sub ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (half_pos hr).le]
  exact half_lt_self hr

end Complex
