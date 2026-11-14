/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Series

/-!
# Cut-plane holomorphy and the Euler recursion for polylogarithms

The principal domain of the classical polylogarithms is the cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)`, which is open, star-convex at `0`, and
contains the open unit disc. On this domain every integer-weight polylogarithm
`TauCeti.Polylog.polylog n` is complex analytic (`TauCeti.Polylog.analyticOnNhd_polylog`).

For `n ≤ 0`, `polylog n` is already analytic on `ℂ ∖ {1}`. Weight `1` is `-Complex.log (1 - z)`,
and weights `k + 2` are differentiated under the radial integral sign on compact closed balls
inside the cut plane using the uniform slit-plane lower bound
`TauCeti.Polylog.exists_le_norm_one_sub_ofReal_mul` and Goursat's theorem.

Once holomorphy on the connected cut plane is established, the identity principle glues the
open-disc termwise derivative from `TauCeti.Analysis.SpecialFunctions.Polylogarithm.Series` to the
whole cut plane, giving the all-weight Euler differential recursion
`z * deriv (polylog (n + 1)) z = polylog n z` (`TauCeti.Polylog.mul_deriv_polylog_add_one`) and,
by the fundamental theorem of calculus along radial segments `[0, z]`, the all-weight recursive
radial integral `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`
(`TauCeti.Polylog.polylog_add_one_eq_integral`). Finally, `polylog 1` fails to be continuous at
every real point `x > 1`, showing that cut-plane holomorphy cannot extend across `(1, ∞)`.

## Main declarations

* `TauCeti.Polylog.isOpen_one_sub_mem_slitPlane`,
  `TauCeti.Polylog.starConvex_zero_one_sub_mem_slitPlane`,
  `TauCeti.Polylog.isPreconnected_one_sub_mem_slitPlane`: geometry of `{z | 1 - z ∈ slitPlane}`.
* `TauCeti.Polylog.hasDerivAt_polylog_one`, `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`:
  complex derivatives of positive-weight polylogarithms on the cut plane.
* `TauCeti.Polylog.differentiableOn_polylog`, `TauCeti.Polylog.analyticOnNhd_polylog`,
  `TauCeti.Polylog.analyticAt_polylog`: cut-plane holomorphy in every integer weight.
* `TauCeti.Polylog.mul_deriv_polylog_add_one`, `TauCeti.Polylog.deriv_polylog_add_one`,
  `TauCeti.Polylog.hasDerivAt_polylog_add_one`: the Euler differential recursion on the cut plane.
* `TauCeti.Polylog.intervalIntegrable_polylog_div`, `TauCeti.Polylog.polylog_add_one_eq_integral`:
  the recursive radial-integral representation in every integer weight on the cut plane.
* `TauCeti.Polylog.not_continuousAt_polylog_one_of_one_lt`: discontinuity of `polylog 1` at every
  point of the open branch cut `(1, ∞)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* Alexander B. Goncharov, *Polylogarithms in arithmetic and geometry*, Proceedings of the ICM
  (Zürich, 1994), Birkhäuser (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Polylog

/-- The principal polylogarithm domain `{z : ℂ | 1 - z ∈ Complex.slitPlane}` is open. -/
theorem isOpen_one_sub_mem_slitPlane : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

/-- Every point of the open unit disc lies in `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)

/-- The principal domain `{z : ℂ | 1 - z ∈ Complex.slitPlane}` is star-convex at `0`. -/
theorem starConvex_zero_one_sub_mem_slitPlane :
    StarConvex ℝ 0 {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hmem := Complex.starConvex_one_slitPlane.add_smul_mem
    (by simpa [sub_eq_add_neg] using hz : 1 + -z ∈ Complex.slitPlane) hb hb1
  simpa [smul_zero, zero_add, smul_neg, sub_eq_add_neg] using hmem

/-- Radial scaling by `t ∈ [0, 1]` preserves `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
private lemma one_sub_ofReal_mul_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
  have h := starConvex_zero_one_sub_mem_slitPlane hz (a := 1 - t) (b := t)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa [Complex.real_smul] using h

/-- The principal domain `{z : ℂ | 1 - z ∈ Complex.slitPlane}` is preconnected. -/
theorem isPreconnected_one_sub_mem_slitPlane :
    IsPreconnected {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (starConvex_zero_one_sub_mem_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected

/-- Complex derivative of `polylog 1` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
  have h := (((hasDerivAt_id' z).const_sub 1).clog hz).neg
  convert h using 1
  · ext w
    exact polylog_one w
  · ring

/-- Pointwise parameter derivative of the weight-`(k + 2)` radial integrand on the cut plane. -/
private lemma hasDerivAt_radialIntegrand (k : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {w : ℂ}
    (hw : 1 - w ∈ Complex.slitPlane) :
    HasDerivAt
      (fun u : ℂ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * u)) / (t : ℂ))
      (((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)) w := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have htw : 1 - (t : ℂ) * w ∈ Complex.slitPlane :=
    one_sub_ofReal_mul_mem_slitPlane hw (Ioc_subset_Icc_self ht)
  have hlin : HasDerivAt (fun u : ℂ ↦ 1 - (t : ℂ) * u) (-((t : ℂ) * 1)) w :=
    ((hasDerivAt_id' w).const_mul (t : ℂ)).const_sub 1
  have hlog : HasDerivAt (fun u : ℂ ↦ -Complex.log (1 - (t : ℂ) * u))
      (-(-((t : ℂ) * 1) / (1 - (t : ℂ) * w))) w :=
    (hlin.clog htw).neg
  convert (hlog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ) using 1
  field_simp [ht0]

/-- Differentiating the defining radial integral of `polylog (k + 2)` under the integral sign on
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((k.factorial : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_one_sub_mem_slitPlane.mem_nhds hz)
  obtain ⟨δ, hδ, hδball⟩ :=
    exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z ε) hball
  let F : ℂ → ℝ → ℂ := fun w t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun w t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)
  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun t : ℝ ↦ |Real.log t| ^ k / δ)
    (Metric.closedBall_mem_nhds z hε)
    (Eventually.of_forall fun w ↦ (by fun_prop : Measurable (F w)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z)
    (by fun_prop : Measurable (F' z)).aestronglyMeasurable
    (ae_of_all _ fun t ht w hw ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      simp only [F', norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg]
      exact div_le_div_of_nonneg_left (by positivity) hδ
        (hδball w hw t (Ioc_subset_Icc_self ht)))
    (by
      refine (((intervalIntegrable_log_pow k).norm).div_const δ).congr fun t _ ↦ ?_
      simp [Real.norm_eq_abs])
    (ae_of_all _ fun t ht w hw ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      exact hasDerivAt_radialIntegrand k ht (hball hw))
  have hfun : polylog (k + 2 : ℕ) = fun w ↦ (k.factorial : ℂ)⁻¹ * ∫ t : ℝ in 0..1, F w t :=
    funext (polylog_nat_add_two k)
  rw [hfun]
  exact hdom.2.const_mul (k.factorial : ℂ)⁻¹

/-- Every integer-weight polylogarithm is complex differentiable on
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  intro z hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (hasDerivAt_polylog_zero_weight hz1).differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_polylog_nat_add_two k hz).differentiableAt.differentiableWithinAt
  | negSucc r =>
    have hn : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := rfl
    rw [hn]
    exact (analyticAt_polylog_neg_nat (r + 1) hz1).differentiableAt.differentiableWithinAt

/-- **Cut-plane holomorphy of integer-weight polylogarithms**: for every `n : ℤ`, `polylog n` is
complex analytic on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).analyticOnNhd isOpen_one_sub_mem_slitPlane

/-- Pointwise analyticity of `polylog n` at any `z` with `1 - z ∈ Complex.slitPlane`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- Open-disc verification of the Euler differential recursion, used as the seed for analytic
continuation to the cut plane. -/
private lemma mul_deriv_polylog_add_one_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  rw [(hasDerivAt_polylog_of_norm_lt_one (n + 1) hz).deriv, ← tsum_mul_left, polylog_eq_tsum n hz]
  refine tsum_congr fun k ↦ ?_
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [zpow_add_one₀ hk, mul_div_assoc', ← mul_assoc, mul_comm z (k + 1 : ℂ), mul_assoc,
    ← pow_succ', mul_comm (k + 1 : ℂ), mul_div_mul_right _ _ hk]

/-- **Euler differential recursion on the cut plane**: for every `n : ℤ` and every `z` with
`1 - z ∈ Complex.slitPlane` (including `z = 0`), `z * deriv (polylog (n + 1)) z = polylog n z`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  have hf : AnalyticOnNhd ℂ (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w)
      {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    analyticOnNhd_id.mul (analyticOnNhd_polylog (n + 1)).deriv
  have hlocal : (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) =ᶠ[𝓝 (0 : ℂ)] polylog n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)] with w hw
    exact mul_deriv_polylog_add_one_of_norm_lt_one n (mem_ball_zero_iff.mp hw)
  exact hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_polylog n)
    isPreconnected_one_sub_mem_slitPlane (by simp : (0 : ℂ) ∈ {w | 1 - w ∈ Complex.slitPlane})
    hlocal hz

/-- Quotient form of the Euler differential recursion away from `0` on the cut plane. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z := by
  rw [← mul_deriv_polylog_add_one n hz, mul_div_cancel_left₀ _ hz0]

/-- `HasDerivAt` form of the Euler differential recursion away from `0` on the cut plane. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) : HasDerivAt (polylog (n + 1)) (polylog n z / z) z :=
  deriv_polylog_add_one n hz hz0 ▸ (analyticAt_polylog (n + 1) hz).differentiableAt.hasDerivAt

/-- On `[0, 1]`, the radial restriction `t ↦ polylog (n + 1) (t * z)` has real derivative
`z * deriv (polylog (n + 1)) (t * z)` whenever `1 - z ∈ Complex.slitPlane`. -/
private lemma hasDerivAt_polylog_ofReal_mul (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ ↦ polylog (n + 1) ((s : ℂ) * z))
      (z * deriv (polylog (n + 1)) ((t : ℂ) * z)) t := by
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane := one_sub_ofReal_mul_mem_slitPlane hz ht
  have hg : HasDerivAt (polylog (n + 1)) (deriv (polylog (n + 1)) ((t : ℂ) * z)) ((t : ℂ) * z) :=
    (analyticAt_polylog (n + 1) htz).differentiableAt.hasDerivAt
  have hh : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
  simpa only [Function.comp_def, smul_eq_mul] using hg.scomp t hh

/-- On `(0, 1]`, the recursive radial integrand `polylog n (t * z) / t` coincides with the radial
derivative `z * deriv (polylog (n + 1)) (t * z)`. -/
private lemma polylog_div_eq_mul_deriv (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht : t ∈ uIoc (0 : ℝ) 1) :
    polylog n ((t : ℂ) * z) / (t : ℂ) = z * deriv (polylog (n + 1)) ((t : ℂ) * z) := by
  rw [uIoc_of_le zero_le_one] at ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    one_sub_ofReal_mul_mem_slitPlane hz (Ioc_subset_Icc_self ht)
  rw [← mul_deriv_polylog_add_one n htz, mul_assoc, mul_div_cancel_left₀ _ ht0]

/-- Interval integrability of the radial derivative `t ↦ z * deriv (polylog (n + 1)) (t * z)` on
`0..1` for `1 - z ∈ Complex.slitPlane`. -/
private lemma intervalIntegrable_mul_deriv_polylog (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z)) volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z))
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine continuousOn_const.mul (((analyticOnNhd_polylog (n + 1)).deriv.continuousOn).comp
      (Complex.continuous_ofReal.continuousOn.mul continuousOn_const) fun t ht ↦ ?_)
    exact one_sub_ofReal_mul_mem_slitPlane hz ht
  exact hcont.intervalIntegrable

/-- Interval integrability of the recursive radial integrand `t ↦ polylog n (t * z) / t` on `0..1`
for every `n : ℤ` and every `z` in the cut plane. -/
theorem intervalIntegrable_polylog_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 :=
  (intervalIntegrable_mul_deriv_polylog n hz).congr fun _ ht ↦
    (polylog_div_eq_mul_deriv n hz ht).symm

/-- **Recursive radial integral of the polylogarithm**: for every `n : ℤ` and every `z` with
`1 - z ∈ Complex.slitPlane`, `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun _ ht ↦ polylog_div_eq_mul_deriv n hz ht),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ by
      rw [uIcc_of_le zero_le_one] at ht
      exact hasDerivAt_polylog_ofReal_mul n hz ht) (intervalIntegrable_mul_deriv_polylog n hz)]
  simp

/-- At every real point `x > 1` on the open branch cut, `polylog 1` fails to be continuous:
approaching `(x : ℂ)` from the upper half-plane keeps `Im (polylog 1 (x + i y)) ≥ 0`, whereas
`Im (polylog 1 x) = -π`. -/
theorem not_continuousAt_polylog_one_of_one_lt {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog 1) x := by
  intro hc
  have him_at_x : (polylog 1 (x : ℂ)).im = -Real.pi := by
    have hxneg : 1 - x < 0 := sub_neg.mpr hx
    rw [polylog_one, Complex.neg_im, Complex.log_im,
      show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_neg hxneg]
  have hpath : Tendsto (fun y : ℝ ↦ (polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    have hg : Tendsto (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc0 : Continuous (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
      simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [← him_at_x]
    exact Complex.continuous_im.continuousAt.tendsto.comp (hc.tendsto.comp hg)
  have hnonneg : ∀ᶠ y : ℝ in 𝓝[>] 0,
      0 ≤ (polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)).im := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [polylog_one, Complex.neg_im, Complex.log_im, neg_nonneg]
    refine (Complex.arg_neg_iff.mpr ?_).le
    simp [hy]
  linarith [ge_of_tendsto hpath hnonneg, Real.pi_pos]

end TauCeti.Polylog
