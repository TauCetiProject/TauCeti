/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The smooth transition function and cutoffs near zero

Mathlib's `Analysis/SpecialFunctions/SmoothTransition.lean` proves that
`Real.smoothTransition` is smooth and equals one on `[1, ∞)`, but states no derivative values.
This file records that its derivative vanishes on the closed rays `(-∞, 0]` and `[1, ∞)`,
including the transition endpoints, so that the derivative is compactly supported. Being continuous,
it is then bounded, which bounds the gradients of cutoffs built from `Real.smoothTransition`. It is
also integrable with integral one, so its rescalings `t ↦ c ψ'(c (a - t))` are approximate
identities; together with the chain rule and local Lipschitz continuity of `ψ (c (u - t))`, this
is what is needed to smooth the indicator of a superlevel set `{u > t}`. The one-sided rescalings
`y ↦ c ψ'(c (y - a))`, supported in `[a, a + c⁻¹]`, converge at every Lebesgue point: if the mean
oscillation of `u` about `v` on `closedBall a r` tends to zero, then
`∫ c ψ'(c (y - a)) u y dy → v` as `c → ∞`. Pairing a function with the derivative of a smooth
step `ψ (c (y - a))` therefore recovers its Lebesgue value at `a`.

It also uses the smooth transition to cut a function off near zero. For `m > 0` and a function
`g : ℝ → ℝ`, `TauCeti.positiveCutoff m g` is the product of `g` with a smooth transition from `0`
to `1` on `[m/4, m/2]`. It vanishes for `t ≤ m/4` and agrees with `g` for `t ≥ m/2`, so it is a
globally defined replacement for a function such as `t ↦ 1/t` or `Real.log` that is only well
behaved on `(0, ∞)`. If `g` is `C¹` on `(0, ∞)` then the cutoff is `C¹` on `ℝ`, and if `g'` is
bounded on `[m, ∞)` then the derivative of the cutoff is bounded on `ℝ`; these are the hypotheses
of chain rules for Sobolev functions. Finally, rescaling the smooth transition gives a smooth
nonincreasing step from any value `v ≥ 0` down to `0` across an interval `[a, b]`. A smooth
plateau, built from two smooth transitions, is equal to `1` on `[a + δ, b - δ]` and vanishes outside
`(a, b)`; integrating it gives such a step with slope at most `τ` whenever
`v < τ (b - a)`, which is the best possible bound, since the mean slope of the step is
`v / (b - a)`. Translating and reflecting the smooth transition also gives three cutoffs summing to
one, supported near `+∞`, near `-∞` and on a bounded interval, with bounded derivatives.

The derivative supremum bounds are adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Profile.lean`.

## Main declarations

* `expNegInvGlue.lt_one`: `expNegInvGlue x < 1`.
* `expNegInvGlue.hasDerivAt`: the derivative of `expNegInvGlue` at `x` is
  `x⁻² expNegInvGlue x`.
* `expNegInvGlue.hasFDerivAt_norm_sq`: on a real inner product space, the derivative of
  `x ↦ expNegInvGlue (‖x‖²)` at `x` is `‖x‖⁻⁴ expNegInvGlue (‖x‖²) · 2 ⟪x, ·⟫`.
* `Real.smoothTransition.one_sub`: reflection exchanges the two plateaus.
* `Real.smoothTransition.deriv_nonneg`: the derivative is nonnegative.
* `Real.smoothTransition.bddAbove_range_deriv`, `Real.smoothTransition.deriv_le_iSup` and
  `Real.smoothTransition.iSup_deriv_nonneg`: the derivative has a nonnegative finite supremum.
* `Real.smoothTransition.mul_deriv_nonneg` and `Real.smoothTransition.mul_deriv_le_deriv`:
  multiplying the derivative by its argument gives a value between zero and the derivative.
* `Real.smoothTransition.abs_le_one`: `|Real.smoothTransition x| ≤ 1`.
* `Real.smoothTransition.deriv_of_nonpos`: `deriv Real.smoothTransition x = 0` for `x ≤ 0`.
* `Real.smoothTransition.deriv_of_one_le`: `deriv Real.smoothTransition x = 0` for `1 ≤ x`.
* `Real.smoothTransition.hasCompactSupport_deriv`: the derivative is compactly supported.
* `Real.smoothTransition.deriv_deriv_of_neg`: the second derivative vanishes on the negative
  half-line.
* `Real.smoothTransition.exists_forall_norm_deriv_le` and
  `Real.smoothTransition.exists_forall_norm_deriv_deriv_le`: the first two derivatives are bounded.
* `Real.smoothTransition.differentiable_deriv`: the derivative is differentiable.
* `Real.smoothTransition.abs_deriv_mul_mul_le`: `|ψ'(a t) (a y)| ≤ M C` when `M` bounds `ψ'`,
  `0 ≤ C` and `|y| ≤ C |t|`.
* `Real.smoothTransition.integral_deriv`: the derivative has integral one.
* `Real.smoothTransition.setIntegral_Icc_deriv`, `Real.smoothTransition.setIntegral_deriv_le_one`:
  its integral over an interval containing `[0, 1]` is one, and over any set at most one.
* `Real.smoothTransition.lintegral_ofReal_mul_deriv`: `∫_ℝ c ψ'(c (a - t)) dt = 1` for `c > 0`.
* `Real.smoothTransition.integral_mul_deriv_mul_sub`: `∫_ℝ c ψ'(c (y - a)) dy = 1` for `c > 0`.
* `Real.smoothTransition.integral_deriv_mul_sub`: `∫_ℝ ψ'(c y - a) dy = |c|⁻¹`.
* `Real.smoothTransition.lintegral_ofReal_deriv_mul_sub` and
  `Real.smoothTransition.lintegral_ofReal_deriv_sub_mul`: `∫⁻_ℝ ψ'(± (c y - a)) dy = |c|⁻¹`.
* `Real.smoothTransition.measurable_ofReal_mul_deriv_mul_sub_mul` and
  `Real.smoothTransition.lintegral_lintegral_ofReal_mul_deriv_mul_sub_mul`: the weight
  `(t, x) ↦ c ψ'(c (t - g x)) w x` is measurable, and integrating it over `x` and `t` gives `∫ w`.
* `Real.smoothTransition.tendsto_integral_deriv_mul_sub_mul`: `∫_ℝ ψ'(c y - T) a y dy` tends to
  `|c|⁻¹ a₀` as `T → ∞` when `a (c⁻¹ σ) → a₀` as `σ → ∞`.
* `Real.smoothTransition.integrable_mul_deriv_mul_sub_smul`: its product with a function
  integrable on `closedBall a c⁻¹` is integrable.
* `Real.smoothTransition.tendsto_indicator`: the smoothed superlevel functions
  `ψ ((n + 1) (f - t))` converge pointwise to the indicator of `{f > t}`.
* `Real.smoothTransition.enorm_sub_indicator_le_one`: `ψ y` differs from the indicator of any set
  by at most `1`.
* `Real.smoothTransition.tendsto_integral_mul_deriv_mul_sub_smul`: at a Lebesgue point `a` of `u`
  with value `v`, `∫ c ψ'(c (y - a)) u y dy → v` as `c → ∞`.
* `HasFDerivAt.smoothTransition` and `HasDerivAt.smoothTransition`: the chain rule for `ψ ∘ f`.
* `HasDerivAt.deriv_smoothTransition`: the chain rule for `ψ' ∘ f`.
* `DifferentiableAt.enorm_fderiv_smoothTransition_mul_sub`: for `c ≥ 0`,
  `‖d(ψ(c (t - u)))‖ = c ψ'(c (t - u)) ‖du‖`.
* `LocallyLipschitzOn.smoothTransition_mul_sub`: `ψ (c (u - t))` is locally Lipschitz on `s`
  when `u` is.
* `TauCeti.positiveCutoff`: the cutoff of `g` near zero.
* `TauCeti.contDiff_positiveCutoff`: the cutoff of a function that is `C¹` on `(0, ∞)` is `C¹`.
* `TauCeti.exists_nnnorm_deriv_positiveCutoff_le`: its derivative is bounded when `g'` is bounded
  on `[m, ∞)`.
* `TauCeti.neckCutoff`: the cutoff `s ↦ ψ (1 + a s)`, equal to `1` where `0 ≤ a s` and to `0` where
  `1 + a s ≤ 0`, with derivative at most `|a|` times a bound for `ψ'`. These cutoffs splice
  right inverses along a neck of length `2 R`, with slope `O(1 / R)`.
* `TauCeti.neckCutoff_neg_two_div_eq_one`, `TauCeti.neckCutoff_neg_two_div_eq_zero` and their
  `two_div` counterparts: where the neck cutoffs for `a = ∓ 2 / R` equal `1` and vanish.
* `TauCeti.exists_contDiff_antitone_cutoff`: a smooth nonincreasing step from a value `v ≥ 0` on
  `(-∞, a]` down to `0` on `[b, ∞)`, positive on `(-∞, b)` when `v > 0`.
* `TauCeti.exists_contDiff_plateau`: a smooth function with values in `[0, 1]`, vanishing outside
  `(a, b)` and equal to `1` on `[a + δ, b - δ]`.
* `TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`: such a step whose slope is at most `τ`,
  for every `v < τ (b - a)`.
* `TauCeti.exists_contDiff_odd_truncation`: a smooth odd function equal to the identity on
  `[-r, r]`, to `±1` on `±[R, ∞)`, with the sign of its argument.
* `TauCeti.exists_cutoffs_add_add_eq_one`: three smooth cutoffs summing to one, vanishing for
  `s ≤ R`, for `s ≥ -R` and outside `(-(R + 1), R + 1)`, with derivatives bounded by a common
  constant and supported in `[-(R + 1), R + 1]`.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped ContDiff ENNReal NNReal Topology

namespace expNegInvGlue

/-- The function `expNegInvGlue` is less than `1` everywhere. -/
theorem lt_one (x : ℝ) : expNegInvGlue x < 1 := by
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx]
  · simp only [expNegInvGlue, hx.not_ge, ↓reduceIte]
    exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (inv_pos.2 hx))

/-- The derivative of `expNegInvGlue` at `x` is `x⁻² expNegInvGlue x`, also for `x ≤ 0`, where
both sides vanish. -/
theorem hasDerivAt (x : ℝ) : HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  simpa using hasDerivAt_polynomial_eval_inv_mul 1 x

/-- The second derivative of the glued exponential profile, including the joining point. -/
theorem deriv_deriv (s : ℝ) :
    deriv (deriv expNegInvGlue) s =
      (s⁻¹ ^ 4 - 2 * s⁻¹ ^ 3) * expNegInvGlue s := by
  -- Function extensionality packages the existing pointwise first-derivative formula.
  rw [show deriv expNegInvGlue = (fun x ↦ x⁻¹ ^ 2 * expNegInvGlue x) by
    funext x; exact (hasDerivAt x).deriv]
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X ^ 2 : Polynomial ℝ) s).deriv
  simp only [Polynomial.eval_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.derivative_X_pow, Polynomial.eval_C] at h
  convert h using 1; ring

/-- On a real inner product space, the derivative of `x ↦ expNegInvGlue (‖x‖ ^ 2)` at `x` is
`‖x‖⁻⁴ expNegInvGlue (‖x‖²) · 2 ⟪x, ·⟫`, also at `x = 0`, where it vanishes. -/
theorem hasFDerivAt_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    HasFDerivAt (fun y ↦ expNegInvGlue (‖y‖ ^ 2))
      (((‖x‖ ^ 2)⁻¹ ^ 2 * expNegInvGlue (‖x‖ ^ 2)) • (2 • innerSL ℝ x)) x :=
  (hasDerivAt _).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt

end expNegInvGlue

namespace TauCeti

/-- The time derivative of an exponentially damped translating glued exponential profile. -/
public theorem hasDerivAt_exp_mul_expNegInvGlue (c A b epsilon t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ epsilon * Real.exp (-A * s) * expNegInvGlue (c + b * s))
      (epsilon * Real.exp (-A * t) *
        (-A * expNegInvGlue (c + b * t) + b * deriv expNegInvGlue (c + b * t))) t := by
  have harg : HasDerivAt (fun s : ℝ ↦ c + b * s) b t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ b * s) b t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul b
    simpa only [Pi.add_apply, zero_add] using! (hasDerivAt_const t (c)).add hlin
  have hψ : HasDerivAt (fun s : ℝ ↦ expNegInvGlue (c + b * s))
      (deriv expNegInvGlue (c + b * t) * b) t := by
    have hbase : HasDerivAt expNegInvGlue
        (deriv expNegInvGlue (c + b * t)) (c + b * t) := by
      exact ((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).1
        (c + b * t)).hasDerivAt
    exact hbase.comp t harg
  have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-A * s))
      (-A * Real.exp (-A * t)) t := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-A)).exp
  have hc : HasDerivAt (fun s : ℝ ↦ epsilon * Real.exp (-A * s))
      (epsilon * (-A * Real.exp (-A * t))) t := by
    have hfun : (fun s : ℝ ↦ epsilon * Real.exp (-A * s)) =
        (fun _ : ℝ ↦ epsilon) * (fun s : ℝ ↦ Real.exp (-A * s)) := by
      funext s
      rfl
    rw [hfun]
    simpa only [zero_mul, zero_add] using (hasDerivAt_const t epsilon).mul he
  have hfun : (fun s : ℝ ↦ epsilon * Real.exp (-A * s) *
      expNegInvGlue (c + b * s)) =
      (fun s : ℝ ↦ epsilon * Real.exp (-A * s)) *
        (fun s : ℝ ↦ expNegInvGlue (c + b * s)) := by
    funext s
    rfl
  rw [hfun]
  convert! hc.mul hψ using 1
  ring


end TauCeti

namespace Real.smoothTransition

/-- Reflection about `1 / 2` exchanges the two plateaus of the smooth transition. -/
theorem one_sub (x : ℝ) : smoothTransition (1 - x) = 1 - smoothTransition x := by
  simp only [smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x))]
  field_simp [(pos_denom x).ne']
  ring

/-- The smooth transition function takes values of absolute value at most one. -/
theorem abs_le_one (x : ℝ) : |smoothTransition x| ≤ 1 :=
  (abs_of_nonneg (nonneg x)).trans_le (le_one x)

/-- The smooth transition function has derivative zero on `(-∞, 0]`. -/
theorem deriv_of_nonpos {x : ℝ} (hx : x ≤ 0) : deriv smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with y
  rw [zero_of_nonpos hx]
  exact nonneg y

/-- The smooth transition function has derivative zero on `[1, ∞)`. -/
theorem deriv_of_one_le {x : ℝ} (hx : 1 ≤ x) : deriv smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [one_of_one_le hx]
  exact le_one y

/-- The derivative of the smooth transition function is nonnegative. -/
theorem deriv_nonneg (t : ℝ) : 0 ≤ deriv smoothTransition t :=
  smoothTransition.monotone.deriv_nonneg

/-- The derivative of the smooth transition function is supported in `[0, 1]`. -/
theorem hasCompactSupport_deriv : HasCompactSupport (deriv smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    rcases not_and_or.1 hx with h | h
    · exact deriv_of_nonpos (not_le.1 h).le
    · exact deriv_of_one_le (not_le.1 h).le

/-- The second derivative of the smooth transition function is zero to the left of `0`. -/
theorem deriv_deriv_of_neg {x : ℝ} (hx : x < 0) : deriv (deriv smoothTransition) x = 0 := by
  have h : deriv smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hx) fun _ ht => deriv_of_nonpos ht.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition function is bounded. -/
theorem exists_forall_norm_deriv_le : ∃ L : ℝ, ∀ τ, ‖deriv smoothTransition τ‖ ≤ L :=
  (Real.smoothTransition.contDiff.iterate_deriv 1).continuous.bounded_above_of_compact_support
    hasCompactSupport_deriv

/-- The range of the derivative of the smooth transition function is bounded above. -/
theorem bddAbove_range_deriv : BddAbove (range (deriv smoothTransition)) := by
  obtain ⟨B, hB⟩ := exists_forall_norm_deriv_le
  exact ⟨B, forall_mem_range.2 fun t ↦ (le_norm_self _).trans (hB t)⟩

/-- The derivative of the smooth transition function is at most its supremum. -/
theorem deriv_le_iSup (t : ℝ) : deriv smoothTransition t ≤ ⨆ s, deriv smoothTransition s :=
  le_ciSup bddAbove_range_deriv t

/-- The supremum of the derivative of the smooth transition function is nonnegative. -/
theorem iSup_deriv_nonneg : 0 ≤ ⨆ s, deriv smoothTransition s :=
  (deriv_nonneg 0).trans (deriv_le_iSup 0)

/-- Multiplying the derivative of the smooth transition function by its argument is nonnegative. -/
theorem mul_deriv_nonneg (t : ℝ) : 0 ≤ t * deriv smoothTransition t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [deriv_of_nonpos ht, mul_zero]
  · exact mul_nonneg ht.le (deriv_nonneg t)

/-- Multiplying the derivative by its argument is at most the derivative itself. -/
theorem mul_deriv_le_deriv (t : ℝ) :
    t * deriv smoothTransition t ≤ deriv smoothTransition t := by
  rcases le_or_gt 1 t with ht | ht
  · rw [deriv_of_one_le ht, mul_zero]
  · exact mul_le_of_le_one_left (deriv_nonneg t) ht.le

/-- The second derivative of the smooth transition function is bounded. -/
theorem exists_forall_norm_deriv_deriv_le :
    ∃ L : ℝ, ∀ τ, ‖deriv (deriv smoothTransition) τ‖ ≤ L :=
  (Real.smoothTransition.contDiff.iterate_deriv 2).continuous.bounded_above_of_compact_support
    hasCompactSupport_deriv.deriv

/-- The derivative of the smooth transition function is differentiable. -/
theorem differentiable_deriv : Differentiable ℝ (deriv smoothTransition) :=
  (contDiff_infty_iff_deriv.1 smoothTransition.contDiff).2.differentiable (by simp)

/-- A bound for the error term of a smooth transition rescaled by `a`: if `M` bounds the
derivative of the smooth transition function `ψ`, `0 ≤ C` and `|y| ≤ C |t|`, then
`|ψ'(a t) (a y)| ≤ M C`. The factor `a y` only matters where `0 ≤ a t ≤ 1`, the support of
`ψ'`, and there `|a y| ≤ C |a t| ≤ C`. -/
theorem abs_deriv_mul_mul_le {M C a t y : ℝ} (hM : ∀ t, ‖deriv smoothTransition t‖ ≤ M)
    (hC : 0 ≤ C) (hy : |y| ≤ C * |t|) :
    |deriv smoothTransition (a * t) * (a * y)| ≤ M * C := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases lt_or_ge (a * t) 0 with ht | ht
  · simpa [deriv_of_nonpos ht.le] using mul_nonneg hM0 hC
  rcases lt_or_ge 1 (a * t) with ht' | ht'
  · simpa [deriv_of_one_le ht'.le] using mul_nonneg hM0 hC
  rw [abs_mul, abs_mul]
  refine mul_le_mul (hM _) ?_ (by positivity) hM0
  calc |a| * |y| ≤ |a| * (C * |t|) := by gcongr
    _ = C * |a * t| := by rw [abs_mul]; ring
    _ ≤ C * 1 := by rw [abs_of_nonneg ht]; gcongr
    _ = C := mul_one _

/-- The derivative of the smooth transition function is integrable. -/
theorem integrable_deriv : Integrable (deriv smoothTransition) :=
  ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).integrable_of_hasCompactSupport
    hasCompactSupport_deriv

/-- The derivative of the smooth transition function has integral one, the total increase of the
function from `0` to `1`. -/
@[simp]
theorem integral_deriv : ∫ x, deriv smoothTransition x = 1 := by
  have hdiff : Differentiable ℝ smoothTransition :=
    (smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have := integral_of_hasDerivAt_of_tendsto (fun x => (hdiff x).hasDerivAt) integrable_deriv
    ((tendsto_const_nhds (x := (0 : ℝ))).congr' ?_)
    ((tendsto_const_nhds (x := (1 : ℝ))).congr' ?_)
  · simpa using this
  · filter_upwards [eventually_le_atBot 0] with x hx
    exact (zero_of_nonpos hx).symm
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact (one_of_one_le hx).symm

/-- Over any interval `[a, b]` containing `[0, 1]`, the derivative of the smooth transition
function has integral one, its total increase. -/
theorem setIntegral_Icc_deriv {a b : ℝ} (ha : a ≤ 0) (hb : 1 ≤ b) :
    ∫ x in Icc a b, deriv smoothTransition x = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_, integral_deriv]
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact deriv_of_nonpos (hx.trans_le ha).le
  · exact deriv_of_one_le (hb.trans_lt hx).le

/-- Over any set, the derivative of the smooth transition function has integral at most one. -/
theorem setIntegral_deriv_le_one (s : Set ℝ) : ∫ x in s, deriv smoothTransition x ≤ 1 :=
  integral_deriv ▸ setIntegral_le_integral integrable_deriv
    (.of_forall fun _ ↦ smoothTransition.monotone.deriv_nonneg)

/-- The rescaled derivatives `t ↦ c ψ'(c (a - t))` of the smooth transition function `ψ`
integrate to one: `∫_ℝ c ψ'(c (a - t)) dt = 1` for `c > 0`. -/
@[simp]
theorem lintegral_ofReal_mul_deriv (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t, ENNReal.ofReal (c * deriv smoothTransition (c * (a - t))) = 1 := by
  have hint : Integrable fun t => c * deriv smoothTransition (c * (a - t)) :=
    ((integrable_deriv.comp_mul_left' hc.ne').comp_sub_left a).const_mul c
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (.of_forall fun t => mul_nonneg hc.le smoothTransition.monotone.deriv_nonneg)]
  simp [integral_const_mul, integral_sub_left_eq_self (fun s => deriv smoothTransition (c * s)),
    Measure.integral_comp_mul_left, abs_of_pos hc, hc.ne']

/-- The rescaled derivatives `y ↦ c ψ'(c (y - a))` of the smooth transition function `ψ` integrate
to one: `∫_ℝ c ψ'(c (y - a)) dy = 1` for `c > 0`. -/
@[simp]
theorem integral_mul_deriv_mul_sub (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ y, c * deriv smoothTransition (c * (y - a)) = 1 := by
  rw [integral_const_mul, integral_sub_right_eq_self (fun z => deriv smoothTransition (c * z)),
    Measure.integral_comp_mul_left, integral_deriv, abs_of_pos (inv_pos.2 hc)]
  simp [hc.ne']

/-- The derivative of the smooth transition function `ψ`, composed with an affine map
`y ↦ c y - a`, has integral `|c|⁻¹`: `∫_ℝ ψ'(c y - a) dy = |c|⁻¹`. -/
theorem integral_deriv_mul_sub (c a : ℝ) : ∫ y, deriv smoothTransition (c * y - a) = |c|⁻¹ := by
  rw [Measure.integral_comp_mul_left (fun y => deriv smoothTransition (y - a)),
    integral_sub_right_eq_self (deriv smoothTransition), integral_deriv, abs_inv, smul_eq_mul,
    mul_one]

/-- The rescaled derivative `s ↦ ψ'(c s - a)` of the smooth transition function `ψ` has integral
`|c|⁻¹` for `c ≠ 0`, the total increase of `ψ` divided by the speed `|c|` at which it is traversed.
-/
theorem lintegral_ofReal_deriv_mul_sub (a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (c * s - a)) = ENNReal.ofReal |c|⁻¹ := by
  have hint : Integrable fun s => deriv smoothTransition (c * s - a) :=
    (integrable_deriv.comp_sub_right a).comp_mul_left' hc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ => smoothTransition.monotone.deriv_nonneg),
    integral_deriv_mul_sub c a]

/-- The derivative of the smooth transition function `ψ`, evaluated at the affine argument
`a - c y` with `c ≠ 0`, has lower Lebesgue integral `|c|⁻¹`: `∫⁻_ℝ ψ'(a - c y) dy = |c|⁻¹`. -/
theorem lintegral_ofReal_deriv_sub_mul (a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (deriv smoothTransition (a - c * y)) = ENNReal.ofReal |c|⁻¹ := by
  simpa [sub_eq_neg_add, add_comm] using lintegral_ofReal_deriv_mul_sub (-a) (neg_ne_zero.2 hc)

/-- For measurable `g` and `w`, the weight `(t, x) ↦ c ψ'(c (t - g x)) w x` built from the
derivative of the smooth transition function `ψ` is measurable. -/
theorem measurable_ofReal_mul_deriv_mul_sub_mul {X : Type*} [MeasurableSpace X] {g : X → ℝ}
    {w : X → ℝ≥0∞} (hg : Measurable g) (hw : Measurable w) (c : ℝ) :
    Measurable fun p : ℝ × X =>
      ENNReal.ofReal (c * deriv smoothTransition (c * (p.1 - g p.2))) * w p.2 := by
  have _ : Measurable (deriv smoothTransition) := measurable_deriv _
  fun_prop

/-- Integrating the weight `c ψ'(c (t - g x)) w x` over `x` and then over the level `t` gives
`∫ w dμ`, because `t ↦ c ψ'(c (t - a))` has total integral one for `c > 0`. -/
theorem lintegral_lintegral_ofReal_mul_deriv_mul_sub_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g : X → ℝ} {w : X → ℝ≥0∞} (hg : Measurable g)
    (hw : Measurable w) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t, ∫⁻ x, ENNReal.ofReal (c * deriv smoothTransition (c * (t - g x))) * w x ∂μ =
      ∫⁻ x, w x ∂μ := by
  rw [lintegral_lintegral_swap (measurable_ofReal_mul_deriv_mul_sub_mul hg hw c).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hk : ∫⁻ t, ENNReal.ofReal (c * deriv smoothTransition (c * (t - g x))) = 1 := by
    simp_rw [ENNReal.ofReal_mul hc.le, mul_sub]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_ofReal_deriv_mul_sub _ hc.ne', ← ENNReal.ofReal_mul hc.le,
      abs_of_pos hc, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one]
  have _ : Measurable (deriv smoothTransition) := measurable_deriv _
  rw [lintegral_mul_const _ (by fun_prop), hk, one_mul]

/-- Averaging a function `a` against the derivative `ψ'(c y - T)` of the smooth transition
function `ψ` recovers `|c|⁻¹` times its limit `a₀` along the direction of `c` as `T → ∞`: for
`c ≠ 0` the weight has integral `|c|⁻¹` and is supported where `c y ≥ T`, and for `c = 0` it
vanishes once `T > 0`. -/
theorem tendsto_integral_deriv_mul_sub_mul {c : ℝ} {a : ℝ → ℝ} {a₀ : ℝ}
    (ha : Tendsto (fun σ => a (c⁻¹ * σ)) atTop (𝓝 a₀))
    (hint : ∀ᶠ T in atTop, Integrable fun y => deriv smoothTransition (c * y - T) * a y) :
    Tendsto (fun T => ∫ y, deriv smoothTransition (c * y - T) * a y) atTop
      (𝓝 (|c|⁻¹ * a₀)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [abs_zero, inv_zero, zero_mul, zero_mul, zero_sub]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp [deriv_of_nonpos (neg_neg_of_pos hT).le]
  have hc' : 0 < |c| := abs_pos.2 hc
  have hβ (T : ℝ) : Integrable fun y => deriv smoothTransition (c * y - T) :=
    (integrable_deriv.comp_sub_right T).comp_mul_left' hc
  have hβ0 (y : ℝ) : 0 ≤ deriv smoothTransition y := smoothTransition.monotone.deriv_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 ha (|c| * ε / 2) (by positivity))
  filter_upwards [hint, eventually_ge_atTop R] with T hT hTR
  have hdiff : (∫ y, deriv smoothTransition (c * y - T) * a y) - |c|⁻¹ * a₀ =
      ∫ y, deriv smoothTransition (c * y - T) * (a y - a₀) := by
    simp only [mul_sub]
    rw [integral_sub hT ((hβ T).mul_const a₀), integral_mul_const, integral_deriv_mul_sub]
  -- Where `ψ'(c y - T) ≠ 0`, we have `c y ≥ T ≥ R`, so `a y` is close to `a₀`.
  have hpt (y : ℝ) : ‖deriv smoothTransition (c * y - T) * (a y - a₀)‖ ≤
      deriv smoothTransition (c * y - T) * (|c| * ε / 2) := by
    rw [norm_mul, Real.norm_of_nonneg (hβ0 _)]
    by_cases hy : c * y - T < 0
    · simp [deriv_of_nonpos hy.le]
    · refine mul_le_mul_of_nonneg_left ?_ (hβ0 _)
      have h := hR (c * y) (by linarith)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, Real.dist_eq, ← Real.norm_eq_abs] at h
      exact h.le
  calc dist (∫ y, deriv smoothTransition (c * y - T) * a y) (|c|⁻¹ * a₀)
      = ‖∫ y, deriv smoothTransition (c * y - T) * (a y - a₀)‖ := by
        rw [Real.dist_eq, hdiff, Real.norm_eq_abs]
    _ ≤ ∫ y, deriv smoothTransition (c * y - T) * (|c| * ε / 2) :=
        norm_integral_le_of_norm_le ((hβ T).mul_const _) (ae_of_all _ hpt)
    _ < ε := by
        rw [integral_mul_const, integral_deriv_mul_sub, ← mul_div_assoc,
          inv_mul_cancel_left₀ hc'.ne']
        linarith

/-- The rescaled derivative `y ↦ ψ'(c (y - a))` of the smooth transition function `ψ` vanishes
outside `closedBall a c⁻¹`; it is supported in `[a, a + c⁻¹]`. -/
theorem deriv_mul_sub_eq_zero {a c y : ℝ} (hc : 0 < c) (hy : y ∉ Metric.closedBall a c⁻¹) :
    deriv smoothTransition (c * (y - a)) = 0 := by
  rw [Real.closedBall_eq_Icc, mem_Icc, not_and_or, not_le, not_le] at hy
  rcases hy with hy | hy
  · exact deriv_of_nonpos (mul_neg_of_pos_of_neg hc (by linarith [inv_pos.2 hc])).le
  · refine deriv_of_one_le ?_
    calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * (y - a) := mul_le_mul_of_nonneg_left (by linarith) hc.le

/-- The product of the rescaled derivative `y ↦ c ψ'(c (y - a))` of the smooth transition
function `ψ` with a function integrable on `closedBall a c⁻¹` is integrable. -/
theorem integrable_mul_deriv_mul_sub_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {a c : ℝ} (hc : 0 < c) (hu : IntegrableOn u (Metric.closedBall a c⁻¹)) :
    Integrable fun y => (c * deriv smoothTransition (c * (y - a))) • u y := by
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall a c⁻¹) ?_).1 ?_
  · refine Function.support_subset_iff'.2 fun y hy => ?_
    rw [deriv_mul_sub_eq_zero hc hy, mul_zero, zero_smul]
  · exact hu.continuousOn_smul (continuous_const.mul
      (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).continuousOn
      (isCompact_closedBall a c⁻¹)

/-- **The rescaled derivatives of the smooth transition function are an approximate identity at
Lebesgue points.** If `u` is integrable near `a` and its mean oscillation about `v` on
`closedBall a r` tends to zero as `r → 0`, then `∫ c ψ'(c (y - a)) u y dy → v` as `c → ∞`. -/
theorem tendsto_integral_mul_deriv_mul_sub_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {u : ℝ → E} {a : ℝ} {v : E}
    (hu : IntegrableAtFilter u (𝓝 a))
    (hv : Tendsto (fun r => ⨍ y in Metric.closedBall a r, ‖u y - v‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun c => ∫ y, (c * deriv smoothTransition (c * (y - a))) • u y) atTop
      (𝓝 v) := by
  obtain ⟨C, hC⟩ :=
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
      hasCompactSupport_deriv
  obtain ⟨s, hs, hus⟩ := hu
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  -- The kernel `c ψ'(c (y - a))` is supported in `closedBall a c⁻¹`, has integral one and is
  -- bounded by `c C = 2 C / volume (closedBall a c⁻¹)`.
  refine tendsto_integral_smul_of_tendsto_average_norm_sub (a := fun c => Metric.closedBall a c⁻¹)
    (2 * C) (hv.comp tendsto_inv_atTop_nhdsGT_zero) ?_
    (tendsto_const_nhds.congr' ?_) ?_ ?_
  · filter_upwards [eventually_gt_atTop ε⁻¹] with c hc
    exact hus.mono_set ((Metric.closedBall_subset_ball (inv_lt_of_inv_lt₀ hε hc)).trans hεs)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact (integral_mul_deriv_mul_sub a hc).symm
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact Function.support_subset_iff'.2 fun y hy => by
      rw [deriv_mul_sub_eq_zero hc hy, mul_zero]
  · filter_upwards [eventually_gt_atTop 0] with c hc y
    rw [Real.volume_real_closedBall (inv_pos.2 hc).le, abs_mul, abs_of_pos hc]
    calc c * |deriv smoothTransition (c * (y - a))| ≤ c * C := by gcongr; exact hC _
      _ = 2 * C / (2 * c⁻¹) := by field_simp

/-- The pointwise limit of `d + ψ ((n + 1) t) e + ψ' ((n + 1) t) ((n + 1) k)` for the smooth
transition `ψ`: the sequence tends to `d` for `t ≤ 0` and to `d + e` for `0 < t`. At `t = 0` the
last term vanishes because `ψ' 0 = 0`, whatever `k` is. -/
theorem tendsto_add_mul_add_deriv_mul {t d e k : ℝ} :
    Tendsto (fun n : ℕ => d + smoothTransition ((n + 1) * t) * e +
      deriv smoothTransition ((n + 1) * t) * ((n + 1) * k)) atTop
      (𝓝 (if t ≤ 0 then d else d + e)) := by
  rcases le_or_gt t 0 with ht | ht
  · have ht' (n : ℕ) : ((n : ℝ) + 1) * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
    simp [zero_of_nonpos (ht' _), deriv_of_nonpos (ht' _), ht]
  · have hev : ∀ᶠ n : ℕ in atTop, 1 < ((n : ℝ) + 1) * t :=
      (Tendsto.atTop_mul_const ht (tendsto_natCast_atTop_atTop.atTop_add
        tendsto_const_nhds)).eventually_gt_atTop 1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp [one_of_one_le hn.le, deriv_of_one_le hn.le, not_le.2 ht]

/-- **Smoothing a superlevel indicator.** The functions `ψ ((n + 1) (f - t))` converge pointwise
to the indicator of the superlevel set `{f > t}`. -/
theorem tendsto_indicator {X : Type*} (f : X → ℝ) (t : ℝ) (x : X) :
    Tendsto (fun n : ℕ => smoothTransition ((n + 1) * (f x - t))) atTop
      (𝓝 ({x | t < f x}.indicator 1 x)) := by
  convert tendsto_add_mul_add_deriv_mul (t := f x - t) (d := 0) (e := 1) (k := 0) using 2
  · simp
  · by_cases hxt : t < f x <;> simp [hxt]

/-- `ψ y` differs from the value at `x` of the indicator of any set `s` by at most `1`, since both
lie in `[0, 1]`. -/
theorem enorm_sub_indicator_le_one {X : Type*} (y : ℝ) (s : Set X) (x : X) :
    ‖smoothTransition y - s.indicator 1 x‖ₑ ≤ 1 := by
  rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
  refine abs_sub_le_of_nonneg_of_le (nonneg _) (le_one _) ?_ ?_ <;>
    by_cases hxs : x ∈ s <;> simp [hxs]

/-- `x + (1 - smoothTransition x)` is at least `x`. -/
theorem le_add_one_sub (x : ℝ) : x ≤ x + (1 - smoothTransition x) := by
  linarith [le_one x]

/-- `x + (1 - smoothTransition x)` is nonzero for `x ≥ 0`. -/
theorem add_one_sub_ne_zero {x : ℝ} (hx : 0 ≤ x) : x + (1 - smoothTransition x) ≠ 0 := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · exact (h.trans_le (le_add_one_sub x)).ne'

end Real.smoothTransition

/-- The chain rule for the smooth transition function `ψ`: if `f` has derivative `f'` at `x`,
then `ψ ∘ f` has derivative `ψ'(f x) • f'` there. -/
theorem HasFDerivAt.smoothTransition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => Real.smoothTransition (f y))
      (deriv Real.smoothTransition (f x) • f') x :=
  (((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
    (f x)).hasDerivAt).comp_hasFDerivAt x hf

/-- The chain rule for the smooth transition function `ψ` in one variable: if `f` has derivative
`f'` at `x`, then `ψ ∘ f` has derivative `ψ'(f x) * f'` there. -/
theorem HasDerivAt.smoothTransition {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => Real.smoothTransition (f y))
      (_root_.deriv Real.smoothTransition (f x) * f') x :=
  (((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
    (f x)).hasDerivAt).comp x hf

/-- The chain rule for the derivative `ψ'` of the smooth transition function: if `f` has
derivative `f'` at `x`, then `ψ' ∘ f` has derivative `ψ''(f x) * f'` there. -/
theorem HasDerivAt.deriv_smoothTransition {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => _root_.deriv Real.smoothTransition (f y))
      (_root_.deriv (_root_.deriv Real.smoothTransition) (f x) * f') x :=
  (Real.smoothTransition.differentiable_deriv (f x)).hasDerivAt.comp x hf

/-- If `u` is differentiable at `x` and `c ≥ 0`, the derivative of `y ↦ ψ(c (t - u y))` at `x`,
for the smooth transition function `ψ`, has norm `c ψ'(c (t - u x)) ‖du x‖`. -/
theorem DifferentiableAt.enorm_fderiv_smoothTransition_mul_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖fderiv ℝ (fun y => Real.smoothTransition (c * (t - u y))) x‖ₑ =
      ENNReal.ofReal (c * deriv Real.smoothTransition (c * (t - u x))) * ‖fderiv ℝ u x‖ₑ := by
  rw [((hu.hasFDerivAt.const_sub t).const_mul c).smoothTransition.fderiv, smul_smul, mul_comm,
    eNorm_smul, eNorm_neg,
    Real.eNorm_of_nonneg (mul_nonneg hc Real.smoothTransition.monotone.deriv_nonneg)]

/-- If `u` is locally Lipschitz on `s`, then so is `ψ (c (u - t))` for the smooth transition
function `ψ`. -/
theorem LocallyLipschitzOn.smoothTransition_mul_sub {α : Type*} [PseudoEMetricSpace α]
    {s : Set α} {u : α → ℝ} (hu : LocallyLipschitzOn s u) (c t : ℝ) :
    LocallyLipschitzOn s fun x => Real.smoothTransition (c * (u x - t)) :=
  ((Real.smoothTransition.contDiff (n := 1)).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))).locallyLipschitz
    |>.locallyLipschitzOn.comp hu (mapsTo_univ _ _)

namespace TauCeti

/-- The function `t ↦ s((4t - m)/m) g(t)`, where `s` is `Real.smoothTransition`. For `m > 0` it
vanishes for `t ≤ m/4` and agrees with `g` for `t ≥ m/2`, so it is a globally defined replacement
for a function `g` that is only well behaved on `(0, ∞)`. -/
def positiveCutoff (m : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * t - m) / m) * g t

/-- The cutoff vanishes on `(-∞, m/4]`. -/
@[simp]
theorem positiveCutoff_of_le {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : t ≤ m / 4) : positiveCutoff m g t = 0 := by
  rw [positiveCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hm.le), zero_mul]

/-- The cutoff agrees with `g` on `[m/2, ∞)`. -/
@[simp]
theorem positiveCutoff_of_ge {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 ≤ t) : positiveCutoff m g t = g t := by
  rw [positiveCutoff, Real.smoothTransition.one_of_one_le
    (by rw [le_div_iff₀ hm]; linarith), one_mul]

/-- The cutoff agrees with `g` near every point of `(m/2, ∞)`. -/
theorem positiveCutoff_eventuallyEq {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 < t) : positiveCutoff m g =ᶠ[𝓝 t] g := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact positiveCutoff_of_ge hm g (le_of_lt hs)

/-- On `(m/2, ∞)` the derivative of the cutoff is the derivative of `g`. -/
theorem deriv_positiveCutoff {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 < t) : deriv (positiveCutoff m g) t = deriv g t :=
  (positiveCutoff_eventuallyEq hm g ht).deriv_eq

/-- The cutoff of a function that is nonnegative on `(0, ∞)` is nonnegative. -/
theorem positiveCutoff_nonneg {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → 0 ≤ g t) (t : ℝ) : 0 ≤ positiveCutoff m g t := by
  rcases le_or_gt t (m / 4) with ht | ht
  · rw [positiveCutoff_of_le hm g ht]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (hg t (by linarith))

/-- The cutoff of a function that is `C¹` on `(0, ∞)` is `C¹` on the whole line. -/
theorem contDiff_positiveCutoff {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ContDiffAt ℝ 1 g t) : ContDiff ℝ 1 (positiveCutoff m g) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (m / 4) with ht | ht
  · -- Below `m/4` the function vanishes identically.
    have hev : positiveCutoff m g =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact positiveCutoff_of_le hm g (le_of_lt hs)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs : ContDiffAt ℝ 1 (fun s : ℝ => Real.smoothTransition ((4 * s - m) / m)) t :=
      Real.smoothTransition.contDiffAt.comp t
        (((contDiffAt_id.const_smul (4 : ℝ)).sub contDiffAt_const).div_const m)
    exact hs.mul (hg t (by linarith))

/-- If `g` is `C¹` on `(0, ∞)` and `|g'| ≤ K` on `[m, ∞)`, then the derivative of the cutoff is
bounded on the whole line. -/
theorem exists_nnnorm_deriv_positiveCutoff_le {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ContDiffAt ℝ 1 g t) {K : ℝ} (hK : ∀ t, m ≤ t → |deriv g t| ≤ K) :
    ∃ M : ℝ≥0, ∀ t, ‖deriv (positiveCutoff m g) t‖₊ ≤ M := by
  have hcont : Continuous (deriv (positiveCutoff m g)) :=
    (contDiff_positiveCutoff hm hg).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (m / 4) m))
  refine ⟨Real.toNNReal (max C K), fun t => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  rcases lt_or_ge t (m / 4) with ht | ht
  · -- Below `m/4` the derivative vanishes.
    have hev : positiveCutoff m g =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact positiveCutoff_of_le hm g (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const, norm_zero]
    exact le_trans (norm_nonneg _) ((hC (m / 4) ⟨le_rfl, by linarith⟩).trans (le_max_left _ _))
  rcases le_or_gt t m with htm | htm
  · exact (hC t ⟨ht, htm⟩).trans (le_max_left _ _)
  · rw [deriv_positiveCutoff hm g (by linarith), Real.norm_eq_abs]
    exact (hK t htm.le).trans (le_max_right _ _)

/-- **The neck cutoff** `s ↦ ψ (1 + a s)`, for the smooth transition `ψ = Real.smoothTransition`.
It equals `1` where `0 ≤ a s` (`TauCeti.neckCutoff_eq_one`) and `0` where `1 + a s ≤ 0`
(`TauCeti.neckCutoff_eq_zero`), and its derivative is at most `|a|` times a bound for `ψ'`
(`TauCeti.abs_deriv_neckCutoff_le`). For `a = -(2 / R)` it is `1` on `(-∞, 0]` and `0` on
`[R / 2, ∞)`; for `a = 2 / R` it is `1` on `[0, ∞)` and `0` on `(-∞, -R / 2]`. These are the
cutoffs that splice right inverses along a neck of length `2 R`, with slope `O(1 / R)`. -/
def neckCutoff (a s : ℝ) : ℝ :=
  Real.smoothTransition (1 + a * s)

/-- The defining formula of the neck cutoff. -/
theorem neckCutoff_def (a s : ℝ) : neckCutoff a s = Real.smoothTransition (1 + a * s) :=
  (rfl)

/-- The neck cutoff is smooth. -/
theorem contDiff_neckCutoff (a : ℝ) {n : ℕ∞} : ContDiff ℝ n (neckCutoff a) := by
  unfold neckCutoff
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The neck cutoff is nonnegative. -/
theorem neckCutoff_nonneg (a s : ℝ) : 0 ≤ neckCutoff a s :=
  Real.smoothTransition.nonneg _

/-- The neck cutoff is at most `1`. -/
theorem neckCutoff_le_one (a s : ℝ) : neckCutoff a s ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The neck cutoff takes values in `[-1, 1]`. -/
theorem abs_neckCutoff_le_one (a s : ℝ) : |neckCutoff a s| ≤ 1 :=
  Real.smoothTransition.abs_le_one _

/-- The derivative of the neck cutoff, by the chain rule. -/
theorem hasDerivAt_neckCutoff (a s : ℝ) :
    HasDerivAt (neckCutoff a) (deriv Real.smoothTransition (1 + a * s) * a) s := by
  unfold neckCutoff
  simpa using (((hasDerivAt_id s).const_mul a).const_add 1).smoothTransition

/-- The derivative of the neck cutoff is at most `|a| L`, for a bound `L` on the derivative of the
smooth transition. -/
theorem abs_deriv_neckCutoff_le {L : ℝ}
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (a s : ℝ) :
    |deriv (neckCutoff a) s| ≤ |a| * L := by
  rw [(hasDerivAt_neckCutoff a s).deriv, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hL _) (abs_nonneg a)

/-- The neck cutoff is `1` where `0 ≤ a s`. -/
theorem neckCutoff_eq_one {a s : ℝ} (h : 0 ≤ a * s) : neckCutoff a s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The neck cutoff is `0` where `1 + a s ≤ 0`. -/
theorem neckCutoff_eq_zero {a s : ℝ} (h : 1 + a * s ≤ 0) : neckCutoff a s = 0 :=
  Real.smoothTransition.zero_of_nonpos h

/-- The left neck cutoff `neckCutoff (-(2 / R))` is `1` on `(-∞, 0]`. -/
theorem neckCutoff_neg_two_div_eq_one {R s : ℝ} (hR : 0 ≤ R) (hs : s ≤ 0) :
    neckCutoff (-(2 / R)) s = 1 :=
  neckCutoff_eq_one (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (by positivity)) hs)

/-- The right neck cutoff `neckCutoff (2 / R)` is `1` on `[0, ∞)`. -/
theorem neckCutoff_two_div_eq_one {R s : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) :
    neckCutoff (2 / R) s = 1 :=
  neckCutoff_eq_one (mul_nonneg (by positivity) hs)

/-- The left neck cutoff `neckCutoff (-(2 / R))` vanishes on `[R / 2, ∞)`. -/
theorem neckCutoff_neg_two_div_eq_zero {R s : ℝ} (hR : 0 < R) (hs : R / 2 ≤ s) :
    neckCutoff (-(2 / R)) s = 0 :=
  neckCutoff_eq_zero (by field_simp; linarith)

/-- The right neck cutoff `neckCutoff (2 / R)` vanishes on `(-∞, -(R / 2)]`. -/
theorem neckCutoff_two_div_eq_zero {R s : ℝ} (hR : 0 < R) (hs : s ≤ -(R / 2)) :
    neckCutoff (2 / R) s = 0 :=
  neckCutoff_eq_zero (by field_simp; linarith)

/-- A smooth nonincreasing step down from a value `v ≥ 0` to `0`: for `a < b` there is a smooth
antitone function `μ ≥ 0` equal to `v` on `(-∞, a]` and to `0` on `[b, ∞)`. When `v > 0` it is
positive on `(-∞, b)`, so `b` is exactly where it reaches `0`. -/
theorem exists_contDiff_antitone_cutoff {a b v : ℝ} (hab : a < b) (hv : 0 ≤ v) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ Antitone μ ∧ (∀ r, 0 ≤ μ r) ∧ (∀ r, b ≤ r → μ r = 0) ∧
      (∀ r ≤ a, μ r = v) ∧ (0 < v → ∀ r < b, 0 < μ r) := by
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨fun r ↦ v * (1 - Real.smoothTransition ((r - a) / (b - a))),
    contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))),
    fun r s hrs ↦ mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (by linarith) hba.le)) _) hv,
    fun r ↦ mul_nonneg hv (sub_nonneg.2 (Real.smoothTransition.le_one _)),
    fun r hr ↦ ?_, fun r hr ↦ ?_, fun hv r hr ↦ ?_⟩
  · have h : 1 ≤ (r - a) / (b - a) := (one_le_div hba).2 (by linarith)
    simp only [Real.smoothTransition.one_of_one_le h, sub_self, mul_zero]
  · have h : (r - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
    simp only [Real.smoothTransition.zero_of_nonpos h, sub_zero, mul_one]
  · have h : (r - a) / (b - a) < 1 := (div_lt_one hba).2 (by linarith)
    exact mul_pos hv (sub_pos.2 (Real.smoothTransition.lt_one_of_lt_one h))

/-- A smooth **plateau** on `[a, b]`: for `δ > 0` there is a smooth function with values in
`[0, 1]`, vanishing outside `(a, b)` and equal to `1` on `[a + δ, b - δ]`. Its integral over
`[a, b]` is therefore at least `b - a - 2δ`. -/
theorem exists_contDiff_plateau {a b δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ r, 0 ≤ ψ r) ∧ (∀ r, ψ r ≤ 1) ∧
      (∀ r ∉ Ioo a b, ψ r = 0) ∧ (∀ r ∈ Icc (a + δ) (b - δ), ψ r = 1) ∧
      b - a - 2 * δ ≤ ∫ r in a..b, ψ r := by
  set ψ : ℝ → ℝ := fun r ↦
    Real.smoothTransition ((r - a) / δ) * Real.smoothTransition ((b - r) / δ) with hψ
  have hψc : ContDiff ℝ ∞ ψ :=
    (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  have hψ0 (r : ℝ) (hr : r ∉ Ioo a b) : ψ r = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hr
    rcases hr with hr | hr
    · have h : (r - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      simp only [hψ, Real.smoothTransition.zero_of_nonpos h, zero_mul]
    · have h : (b - r) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      simp only [hψ, Real.smoothTransition.zero_of_nonpos h, mul_zero]
  have hψnn (r : ℝ) : 0 ≤ ψ r :=
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hψ1 (r : ℝ) (hr : r ∈ Icc (a + δ) (b - δ)) : ψ r = 1 := by
    have h₁ : 1 ≤ (r - a) / δ := (one_le_div hδ).2 (by linarith [hr.1])
    have h₂ : 1 ≤ (b - r) / δ := (one_le_div hδ).2 (by linarith [hr.2])
    simp only [hψ, Real.smoothTransition.one_of_one_le h₁, Real.smoothTransition.one_of_one_le h₂,
      mul_one]
  refine ⟨ψ, hψc, hψnn, fun r ↦ (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _), hψ0, hψ1, ?_⟩
  rcases le_or_gt (a + δ) (b - δ) with h | h
  · calc b - a - 2 * δ = ∫ _ in (a + δ)..(b - δ), (1 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      _ = ∫ r in (a + δ)..(b - δ), ψ r :=
          intervalIntegral.integral_congr fun r hr ↦ (hψ1 r (by rwa [uIcc_of_le h] at hr)).symm
      _ ≤ ∫ r in a..b, ψ r := intervalIntegral.integral_mono_interval (by linarith)
          (by linarith) (by linarith) (Eventually.of_forall hψnn)
          (hψc.continuous.intervalIntegrable _ _)
  · rcases le_total a b with hab | hab
    · exact (by linarith : b - a - 2 * δ ≤ 0).trans
        (intervalIntegral.integral_nonneg hab fun r _ ↦ hψnn r)
    · have h0 : ψ = 0 := funext fun r ↦ hψ0 r fun hr ↦ absurd (hr.1.trans hr.2) (not_lt.2 hab)
      rw [h0]
      simp only [Pi.zero_apply, intervalIntegral.integral_zero]
      linarith

/-- A smooth nonincreasing step down from `v ≥ 0` to `0` across `[a, b]` with **slope at most
`τ`**: if `v < τ (b - a)`, there is a smooth antitone function `μ ≥ 0` equal to `v` on `(-∞, a]`
and to `0` on `[b, ∞)`, with `|μ'| ≤ τ` everywhere and `μ' = 0` outside `(a, b)`. -/
theorem exists_contDiff_antitone_cutoff_abs_deriv_le {a b v τ : ℝ} (hab : a < b) (hv : 0 ≤ v)
    (hvτ : v < τ * (b - a)) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ Antitone μ ∧ (∀ r, 0 ≤ μ r) ∧ (∀ r, b ≤ r → μ r = 0) ∧
      (∀ r ≤ a, μ r = v) ∧ (∀ r, |deriv μ r| ≤ τ) ∧ ∀ r ∉ Ioo a b, deriv μ r = 0 := by
  have hτ : 0 < τ := by
    by_contra h
    nlinarith
  have hvτ' : v / τ < b - a := by rw [div_lt_iff₀ hτ]; linarith
  have hvτ0 : 0 ≤ v / τ := div_nonneg hv hτ.le
  -- The step is `v` minus a multiple of the primitive of a plateau `ψ`, which is supported in
  -- `[a, b]` and equal to `1` on `[a + δ, b - δ]`, with `δ` small enough that the integral of `ψ`
  -- exceeds `v / τ`.
  set δ := (b - a - v / τ) / 4 with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by norm_num)
  obtain ⟨ψ, hψc, hψnn, hψle, hψ0, -, hJ⟩ := exists_contDiff_plateau (a := a) (b := b) hδpos
  have hψi (c d : ℝ) : IntervalIntegrable ψ volume c d := hψc.continuous.intervalIntegrable _ _
  set J := ∫ r in a..b, ψ r
  have hJv : v / τ < J := by linarith
  have hJ0 : 0 < J := hvτ0.trans_lt hJv
  set c := v / J with hc
  have hc0 : 0 ≤ c := div_nonneg hv hJ0.le
  have hcτ : c ≤ τ := (div_le_iff₀ hJ0).2 ((div_lt_iff₀' hτ).1 hJv).le
  set μ : ℝ → ℝ := fun r ↦ v - c * ∫ t in a..r, ψ t with hμ
  have hd (r : ℝ) : HasDerivAt μ (-(c * ψ r)) r := by
    simpa using ((hψc.continuous.integral_hasStrictDerivAt a r).hasDerivAt.const_mul c).const_sub v
  have hderiv : deriv μ = fun r ↦ -(c * ψ r) := funext fun r ↦ (hd r).deriv
  have hdiff : Differentiable ℝ μ := fun r ↦ (hd r).differentiableAt
  have hanti : Antitone μ := antitone_of_deriv_nonpos hdiff fun r ↦ by
    rw [hderiv]
    exact neg_nonpos.2 (mul_nonneg hc0 (hψnn r))
  have hhigh (r : ℝ) (hr : b ≤ r) : μ r = 0 := by
    have h : ∫ t in a..r, ψ t = J := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hψi a b) (hψi b r),
        intervalIntegral.integral_congr (a := b) (b := r) (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_,
        intervalIntegral.integral_zero, add_zero]
      rw [uIcc_of_le hr] at ht
      exact hψ0 t fun h ↦ absurd ht.1 (not_le.2 h.2)
    simp only [hμ, h, hc, div_mul_cancel₀ v hJ0.ne', sub_self]
  refine ⟨μ, contDiff_infty_iff_deriv.2 ⟨hdiff, ?_⟩, hanti, fun r ↦ ?_, hhigh, fun r hr ↦ ?_,
    fun r ↦ ?_, fun r hr ↦ ?_⟩
  · rw [hderiv]
    exact (contDiff_const.mul hψc).neg
  · rcases le_total r b with h | h
    · exact (hhigh b le_rfl).symm.le.trans (hanti h)
    · exact (hhigh r h).symm.le
  · have h : ∫ t in a..r, ψ t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_,
        intervalIntegral.integral_zero]
      rw [uIcc_of_ge hr] at ht
      exact hψ0 t fun h ↦ absurd ht.2 (not_le.2 h.1)
    simp only [hμ, h, mul_zero, sub_zero]
  · rw [hderiv, abs_neg, abs_of_nonneg (mul_nonneg hc0 (hψnn r))]
    exact (mul_le_of_le_one_right hc0 (hψle r)).trans hcτ
  · simp only [hderiv, hψ0 r hr, mul_zero, neg_zero]

/-- A smooth **step** from `0` to `1`: for `a < b` there is a smooth function equal to `0` on
`(-∞, a]` and to `1` on `[b, ∞)`, whose derivative vanishes outside `(a, b)`. -/
theorem exists_contDiff_step {a b : ℝ} (hab : a < b) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ (∀ r ≤ a, μ r = 0) ∧ (∀ r, b ≤ r → μ r = 1) ∧
      ∀ r ∉ Ioo a b, deriv μ r = 0 := by
  obtain ⟨ν, hν, -, -, hνb, hν1, -, hν'⟩ := exists_contDiff_antitone_cutoff_abs_deriv_le hab
    zero_le_one (τ := 2 / (b - a)) (by rw [div_mul_cancel₀ _ (sub_pos.2 hab).ne']; norm_num)
  exact ⟨fun r ↦ 1 - ν r, contDiff_const.sub hν, fun r hr ↦ by simp [hν1 r hr],
    fun r hr ↦ by simp [hνb r hr], fun r hr ↦ by rw [deriv_const_sub, hν' r hr, neg_zero]⟩

/-- **Three cutoffs in `s` summing to one.** For `R ≥ 0` there are smooth cutoffs `βp`, `βm`, `β₀`
summing to one, with `βp` vanishing for `s ≤ R`, `βm` vanishing for `s ≥ -R` and `β₀` vanishing
outside `(-(R + 1), R + 1)`. Each satisfies `|β| ≤ 1`, and their derivatives are bounded by a common
constant `M` and vanish outside `[-(R + 1), R + 1]`. They are `ψ(s - R)`, `ψ(-s - R)` and
`1 - ψ(s - R) - ψ(-s - R)` for the smooth transition `ψ`. -/
theorem exists_cutoffs_add_add_eq_one {R : ℝ} (hR : 0 ≤ R) :
    ∃ M, ∃ βp βm β₀ : ℝ → ℝ, (∀ s, βp s + βm s + β₀ s = 1) ∧ (∀ s, s ≤ R → βp s = 0) ∧
      (∀ s, -R ≤ s → βm s = 0) ∧ (∀ s, s ∉ Ioo (-(R + 1)) (R + 1) → β₀ s = 0) ∧
      ∀ β ∈ ({βp, βm, β₀} : Set (ℝ → ℝ)), ContDiff ℝ ∞ β ∧ (∀ s, |β s| ≤ 1) ∧
        (∀ s, |deriv β s| ≤ M) ∧ ∀ s, s < -(R + 1) ∨ R + 1 < s → deriv β s = 0 := by
  obtain ⟨M, hM⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  set ψ := Real.smoothTransition
  have hψc : ContDiff ℝ ∞ ψ := Real.smoothTransition.contDiff
  have hψd (x : ℝ) : HasDerivAt ψ (deriv ψ x) x :=
    (hψc.differentiable (by simp) x).hasDerivAt
  have hψ0 (x : ℝ) (hx : x ≤ 0) : ψ x = 0 := Real.smoothTransition.zero_of_nonpos hx
  have hψ1 (x : ℝ) (hx : 1 ≤ x) : ψ x = 1 := Real.smoothTransition.one_of_one_le hx
  have hψ'M (x : ℝ) : |deriv ψ x| ≤ M := by simpa using hM x
  have hψ'0 (x : ℝ) (hx : x < 0 ∨ 1 < x) : deriv ψ x = 0 :=
    hx.elim (fun h ↦ Real.smoothTransition.deriv_of_nonpos h.le)
      (fun h ↦ Real.smoothTransition.deriv_of_one_le h.le)
  have hp (s : ℝ) : HasDerivAt (fun s ↦ ψ (s - R)) (deriv ψ (s - R)) s :=
    (hψd (s - R)).comp_sub_const s R
  have hm (s : ℝ) : HasDerivAt (fun s ↦ ψ (-s - R)) (-deriv ψ (-s - R)) s := by
    simpa [Function.comp_def] using (hψd (-s - R)).comp s ((hasDerivAt_neg s).sub_const R)
  have h₀ (s : ℝ) : HasDerivAt (fun s ↦ 1 - ψ (s - R) - ψ (-s - R))
      (0 - deriv ψ (s - R) - -deriv ψ (-s - R)) s :=
    ((hasDerivAt_const s (1 : ℝ)).sub (hp s)).sub (hm s)
  refine ⟨2 * M, fun s ↦ ψ (s - R), fun s ↦ ψ (-s - R), fun s ↦ 1 - ψ (s - R) - ψ (-s - R),
    fun s ↦ by ring, fun s hs ↦ hψ0 _ (by linarith), fun s hs ↦ hψ0 _ (by linarith),
    fun s hs ↦ ?_, ?_⟩
  · rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    beta_reduce
    rcases hs with hs | hs
    · rw [hψ0 (s - R) (by linarith), hψ1 (-s - R) (by linarith)]
      ring
    · rw [hψ0 (-s - R) (by linarith), hψ1 (s - R) (by linarith)]
      ring
  simp only [mem_insert_iff, mem_singleton_iff]
  rintro β (rfl | rfl | rfl)
  · refine ⟨hψc.comp (contDiff_id.sub contDiff_const), fun s ↦ Real.smoothTransition.abs_le_one _,
      fun s ↦ ?_, fun s hs ↦ ?_⟩
    · rw [(hp s).deriv]
      exact (hψ'M _).trans (by linarith [(abs_nonneg _).trans (hψ'M 0)])
    · rw [(hp s).deriv]
      exact hψ'0 _ (by rcases hs with hs | hs <;> [left; right] <;> linarith)
  · refine ⟨hψc.comp (contDiff_neg.sub contDiff_const), fun s ↦ Real.smoothTransition.abs_le_one _,
      fun s ↦ ?_, fun s hs ↦ ?_⟩
    · rw [(hm s).deriv, abs_neg]
      exact (hψ'M _).trans (by linarith [(abs_nonneg _).trans (hψ'M 0)])
    · rw [(hm s).deriv, neg_eq_zero]
      exact hψ'0 _ (by rcases hs with hs | hs <;> [right; left] <;> linarith)
  · refine ⟨(contDiff_const.sub (hψc.comp (contDiff_id.sub contDiff_const))).sub
      (hψc.comp (contDiff_neg.sub contDiff_const)), fun s ↦ ?_, fun s ↦ ?_, fun s hs ↦ ?_⟩
    · have h₁ := Real.smoothTransition.nonneg (s - R)
      have h₂ := Real.smoothTransition.le_one (s - R)
      have h₃ := Real.smoothTransition.nonneg (-s - R)
      have h₄ := Real.smoothTransition.le_one (-s - R)
      beta_reduce
      rcases le_total 0 s with hs | hs
      · rw [hψ0 (-s - R) (by linarith), abs_le]
        constructor <;> linarith
      · rw [hψ0 (s - R) (by linarith), abs_le]
        constructor <;> linarith
    · have h₁ := abs_le.1 (hψ'M (s - R))
      have h₂ := abs_le.1 (hψ'M (-s - R))
      rw [(h₀ s).deriv, abs_le]
      constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    · rw [(h₀ s).deriv, hψ'0 (s - R) (by rcases hs with hs | hs <;> [left; right] <;> linarith),
        hψ'0 (-s - R) (by rcases hs with hs | hs <;> [right; left] <;> linarith)]
      ring


/-- **A smooth odd truncation of the identity.** For `r < R` with `0 < R`, there is a smooth odd
function equal to the identity on `[-r, r]`, to `1` on `[R, ∞)` and to `-1` on `(-∞, -R]`, with
the sign of its argument. -/
theorem exists_contDiff_odd_truncation {r R : ℝ} (hrR : r < R) (hR : 0 < R) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ Function.Odd h ∧ (∀ t, |t| ≤ r → h t = t) ∧
      (∀ t, R ≤ t → h t = 1) ∧ (∀ t, t ≤ -R → h t = -1) ∧ (∀ t, 0 < t → 0 < h t) ∧
      (∀ t, t < 0 → h t < 0) := by
  set r' := max r 0
  have hr'R : r' < R := max_lt hrR hR
  obtain ⟨ν, hν, -, hν0, hνR, hνr, -⟩ := exists_contDiff_antitone_cutoff hr'R zero_le_one
  obtain ⟨μ, hμ, -, -, hμr, hμR, hμpos⟩ :=
    exists_contDiff_antitone_cutoff (neg_lt_neg hr'R) zero_le_one
  set h : ℝ → ℝ := fun t ↦ ν t * ν (-t) * t + μ (-t) - μ t
  have hodd : Function.Odd h := fun t ↦ by simp only [h, neg_neg]; ring
  have hid (t : ℝ) (ht : |t| ≤ r') : h t = t := by
    obtain ⟨h₁, h₂⟩ := abs_le.1 ht
    simp only [h, hνr t h₂, hνr (-t) (by linarith), hμr t h₁, hμr (-t) (by linarith)]
    ring
  have hone (t : ℝ) (ht : R ≤ t) : h t = 1 := by
    simp only [h, hνR t ht, hμR (-t) (by linarith), hμr t (by linarith [le_max_right r 0])]
    ring
  have hpos (t : ℝ) (ht : 0 < t) : 0 < h t := by
    rcases le_or_gt t r' with htr | htr
    · rw [hid t (abs_le.2 ⟨by linarith [le_max_right r 0], htr⟩)]
      exact ht
    · have := hμpos one_pos (-t) (by linarith)
      have : 0 ≤ ν t * ν (-t) * t := mul_nonneg (mul_nonneg (hν0 t) (hν0 (-t))) ht.le
      simp only [h, hμr t (by linarith [le_max_right r 0])]
      linarith
  refine ⟨h, (hν.mul (hν.comp contDiff_neg)).mul contDiff_id |>.add (hμ.comp contDiff_neg)
    |>.sub hμ, hodd, fun t ht ↦ hid t (ht.trans (le_max_left r 0)), hone, fun t ht ↦ ?_, hpos,
    fun t ht ↦ ?_⟩
  · rw [← neg_neg t, hodd, hone (-t) (by linarith)]
  · rw [← neg_neg t, hodd, neg_lt_zero]
    exact hpos (-t) (by linarith)

end TauCeti
