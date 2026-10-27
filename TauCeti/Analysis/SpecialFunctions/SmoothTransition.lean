/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The smooth transition function and cutoffs near zero

Mathlib's `Analysis/SpecialFunctions/SmoothTransition.lean` proves that
`Real.smoothTransition` is smooth and equals one on `[1, ∞)`, but states no derivative values.
This file records that its derivative vanishes on the open rays `(-∞, 0)` and `(1, ∞)`, where the
function is locally constant, so that the derivative is compactly supported. Being continuous, it
is then bounded, which bounds the gradients of cutoffs built from `Real.smoothTransition`. It is
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
of chain rules for Sobolev functions.

## Main declarations

* `expNegInvGlue.lt_one`: `expNegInvGlue x < 1`.
* `expNegInvGlue.hasDerivAt`: the derivative of `expNegInvGlue` at `x` is
  `x⁻² expNegInvGlue x`.
* `Real.smoothTransition.deriv_of_neg`: `deriv Real.smoothTransition x = 0` for `x < 0`.
* `Real.smoothTransition.deriv_of_one_lt`: `deriv Real.smoothTransition x = 0` for `1 < x`.
* `Real.smoothTransition.hasCompactSupport_deriv`: the derivative is compactly supported.
* `Real.smoothTransition.integral_deriv`: the derivative has integral one.
* `Real.smoothTransition.lintegral_ofReal_mul_deriv`: `∫_ℝ c ψ'(c (a - t)) dt = 1` for `c > 0`.
* `Real.smoothTransition.integral_mul_deriv_mul_sub`: `∫_ℝ c ψ'(c (y - a)) dy = 1` for `c > 0`.
* `Real.smoothTransition.integrable_mul_deriv_mul_sub_smul`: its product with a function
  integrable on `closedBall a c⁻¹` is integrable.
* `Real.smoothTransition.tendsto_integral_mul_deriv_mul_sub_smul`: at a Lebesgue point `a` of `u`
  with value `v`, `∫ c ψ'(c (y - a)) u y dy → v` as `c → ∞`.
* `HasFDerivAt.smoothTransition` and `HasDerivAt.smoothTransition`: the chain rule for `ψ ∘ f`.
* `LocallyLipschitzOn.smoothTransition_mul_sub`: `ψ (c (u - t))` is locally Lipschitz on `s`
  when `u` is.
* `TauCeti.positiveCutoff`: the cutoff of `g` near zero.
* `TauCeti.contDiff_positiveCutoff`: the cutoff of a function that is `C¹` on `(0, ∞)` is `C¹`.
* `TauCeti.exists_nnnorm_deriv_positiveCutoff_le`: its derivative is bounded when `g'` is bounded
  on `[m, ∞)`.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped ContDiff NNReal Topology

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

end expNegInvGlue

namespace Real.smoothTransition

/-- The smooth transition function has derivative zero to the left of `0`, where it is
identically zero. -/
theorem deriv_of_neg {x : ℝ} (hx : x < 0) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hx) fun _ ht => zero_of_nonpos (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The smooth transition function has derivative zero to the right of `1`, where it is
identically one. -/
theorem deriv_of_one_lt {x : ℝ} (hx : 1 < x) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
    eventually_of_mem (Ioi_mem_nhds hx) fun _ ht => one_of_one_le (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition function is supported in `[0, 1]`. -/
theorem hasCompactSupport_deriv : HasCompactSupport (deriv smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    rcases not_and_or.1 hx with h | h
    · exact deriv_of_neg (not_le.1 h)
    · exact deriv_of_one_lt (not_le.1 h)

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

/-- The rescaled derivative `y ↦ ψ'(c (y - a))` of the smooth transition function `ψ` vanishes
outside `closedBall a c⁻¹`; it is supported in `[a, a + c⁻¹]`. -/
theorem deriv_mul_sub_eq_zero {a c y : ℝ} (hc : 0 < c) (hy : y ∉ Metric.closedBall a c⁻¹) :
    deriv smoothTransition (c * (y - a)) = 0 := by
  rw [Real.closedBall_eq_Icc, mem_Icc, not_and_or, not_le, not_le] at hy
  rcases hy with hy | hy
  · exact deriv_of_neg (mul_neg_of_pos_of_neg hc (by linarith [inv_pos.2 hc]))
  · refine deriv_of_one_lt ?_
    calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ < c * (y - a) := mul_lt_mul_of_pos_left (by linarith) hc

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

/-- If `u` is locally Lipschitz on `s`, then so is `ψ (c (u - t))` for the smooth transition
function `ψ`. -/
theorem LocallyLipschitzOn.smoothTransition_mul_sub {α : Type*} [PseudoEMetricSpace α]
    {s : Set α} {u : α → ℝ} (hu : LocallyLipschitzOn s u) (c t : ℝ) :
    LocallyLipschitzOn s fun x => Real.smoothTransition (c * (u x - t)) :=
  ((Real.smoothTransition.contDiff (n := 1)).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))).locallyLipschitz
    |>.comp_locallyLipschitzOn hu

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
  rw [← NNReal.coe_le_coe, coe_nnnorm]
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

end TauCeti
