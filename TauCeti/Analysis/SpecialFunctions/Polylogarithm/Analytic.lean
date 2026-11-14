/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy and the Euler differential recursion on the principal domain

For every integer weight `n : ℤ`, the principal polylogarithm `Liₙ` is complex analytic on the cut
plane `{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)`:

* Nonpositive weights are rational functions whose sole pole is at `1`.
* Weight `1` is `z ↦ -Complex.log (1 - z)`, which is continuous, complex differentiable, or complex
  analytic at `z` if and only if `1 - z ∈ Complex.slitPlane`.
* Weights `k + 2 ≥ 2` are differentiated under the radial integral sign on closed balls inside the
  cut plane, where `‖1 - t z‖` is bounded away from zero uniformly for `t ∈ [0, 1]`; complex
  differentiability on this open set implies analyticity by Goursat's theorem.

Because `{z : ℂ | 1 - z ∈ Complex.slitPlane}` is star-convex at `0` (hence preconnected) and
contains the open unit disc, the identity principle extends the open-disc Euler recursion to the
entire cut plane:

`z * deriv (polylog (n + 1)) z = polylog n z`

for all `n : ℤ` and `1 - z ∈ Complex.slitPlane`, including `z = 0`. Away from `0` this gives
`deriv (polylog (n + 1)) z = polylog n z / z`. Integrating `t ↦ polylog (n + 1) (t * z)` over
`[0, 1]` via the fundamental theorem of calculus and `dslope (polylog n) 0` then yields the
recursive radial-integral representation `Li_{n+1}(z) = ∫₀¹ Liₙ(t z) / t dt` across all integer
weights on the principal domain.

## Main declarations

* `TauCeti.Polylog.analyticOnNhd_polylog`, `TauCeti.Polylog.analyticAt_polylog`,
  `TauCeti.Polylog.differentiableOn_polylog`, `TauCeti.Polylog.continuousOn_polylog`:
  holomorphy and regularity of `polylog n` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`: parametric derivative of the weight `k + 2`
  radial integral on the principal domain.
* `TauCeti.Polylog.hasDerivAt_polylog_one`, `TauCeti.Polylog.continuousAt_polylog_one_iff`,
  `TauCeti.Polylog.differentiableAt_polylog_one_iff`,
  `TauCeti.Polylog.analyticAt_polylog_one_iff`: derivative of `polylog 1` and exact regularity
  characterization by `1 - z ∈ Complex.slitPlane`.
* `TauCeti.Polylog.mul_deriv_polylog_add_one`, `TauCeti.Polylog.hasDerivAt_polylog_add_one`,
  `TauCeti.Polylog.deriv_polylog_add_one`: the Euler differential recursion on the principal domain.
* `TauCeti.Polylog.intervalIntegrable_polylog_mul_div`,
  `TauCeti.Polylog.polylog_add_one_eq_integral`: the recursive radial-integral identity
  `Li_{n+1}(z) = ∫₀¹ Liₙ(t z) / t dt` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* A. B. Goncharov, *Polylogarithms in arithmetic and geometry*, Proceedings of the International
  Congress of Mathematicians (Zürich, 1994), Birkhäuser (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti.Polylog

private lemma ne_one_of_one_sub_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z ≠ 1 := by
  rintro rfl
  simp at hz

private lemma hasDerivAt_radialIntegrand (k : ℕ) {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : 1 - (t : ℂ) * z ∈ Complex.slitPlane) :
    HasDerivAt
      (fun w : ℂ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ))
      (((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hlin : HasDerivAt (fun w : ℂ ↦ 1 - (t : ℂ) * w) (-(t : ℂ)) z := by
    simpa using ((hasDerivAt_id z).const_mul (t : ℂ)).const_sub (1 : ℂ)
  have hmul := ((((Complex.hasDerivAt_log hz).comp z hlin).neg).const_mul
    (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
  refine (hmul.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv ?_
  have hden : 1 - (t : ℂ) * z ≠ 0 := Complex.slitPlane_ne_zero hz
  field_simp [ht_ne, hden]

/-- Complex derivative of `polylog (k + 2)` on the principal domain, obtained by differentiating
the logarithmic radial integral under the integral sign. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z₀ : ℂ} (hz₀ : 1 - z₀ ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in (0 : ℝ)..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) z₀ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp Complex.isOpen_one_sub_slitPlane z₀ hz₀
  set s : Set ℂ := closedBall z₀ (r / 2)
  have hs_sub : s ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrΩ
  obtain ⟨δ, hδ, hδs⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z₀ (r / 2)) hs_sub
  let F : ℂ → ℝ → ℂ := fun z t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)
  have hbound_int : IntervalIntegrable (fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k) volume 0 1 := by
    refine ((TauCeti.intervalIntegrable_log_pow k).norm.const_mul δ⁻¹).congr_ae ?_
    exact ae_of_all _ fun t ↦ by simp [Real.norm_eq_abs]
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k)
    (closedBall_mem_nhds z₀ (half_pos hr))
    (Eventually.of_forall fun z ↦ (by fun_prop : Measurable (F z)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z₀)
    (by fun_prop : Measurable (F' z₀)).aestronglyMeasurable
    (ae_of_all _ fun t ht z hz ↦ ?_)
    hbound_int
    (ae_of_all _ fun t ht z hz ↦ ?_)).2
  · rw [funext (polylog_nat_add_two k)]
    exact hd.const_mul ((Nat.factorial k : ℂ)⁻¹)
  · rw [uIoc_of_le zero_le_one] at ht
    have hden : δ ≤ ‖1 - (t : ℂ) * z‖ := hδs z hz t (Ioc_subset_Icc_self ht)
    dsimp only [F']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) hδ hden
  · rw [uIoc_of_le zero_le_one] at ht
    exact hasDerivAt_radialIntegrand k ht.1
      (Complex.one_sub_ofReal_mul_mem_slitPlane (hs_sub hz) ht.1.le ht.2)

/-- Holomorphy of the principal polylogarithm on `ℂ ∖ [1, ∞)` in every integer weight. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · intro z hz
      simpa using analyticAt_polylog_neg_nat 0 (ne_one_of_one_sub_mem_slitPlane hz)
    · intro z hz
      rw [Int.ofNat_eq_natCast, Nat.cast_one, funext polylog_one]
      exact ((analyticAt_const.sub analyticAt_id).clog hz).neg
    · rw [Int.ofNat_eq_natCast]
      refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) Complex.isOpen_one_sub_slitPlane
      exact (hasDerivAt_polylog_nat_add_two k hz).differentiableAt.differentiableWithinAt
  | negSucc r =>
    intro z hz
    simpa [Int.negSucc_eq] using
      analyticAt_polylog_neg_nat (r + 1) (ne_one_of_one_sub_mem_slitPlane hz)

/-- Pointwise complex analyticity of `polylog n` on the principal domain. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- Complex differentiability of `polylog n` at every point of the principal domain. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z :=
  (analyticAt_polylog n hz).differentiableAt

/-- Complex differentiability of `polylog n` on the principal domain. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (analyticOnNhd_polylog n).differentiableOn

/-- Continuity of `polylog n` at every point of the principal domain. -/
theorem continuousAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousAt (polylog n) z :=
  (differentiableAt_polylog n hz).continuousAt

/-- Continuity of `polylog n` on the principal domain. -/
theorem continuousOn_polylog (n : ℤ) :
    ContinuousOn (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).continuousOn

/-- Weight one has derivative `1 / (1 - z)` on the principal domain, including at `z = 0`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) (1 / (1 - z)) z := by
  have hsub : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z :=
    (hasDerivAt_id z).const_sub (1 : ℂ)
  rw [funext polylog_one]
  refine (((Complex.hasDerivAt_log hz).comp z hsub).neg).congr_deriv ?_
  ring

/-- Derivative formula for `polylog 1` on the principal domain. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = 1 / (1 - z) :=
  (hasDerivAt_polylog_one hz).deriv

/-- `polylog 1` is continuous at `z` if and only if `1 - z ∈ Complex.slitPlane`: it diverges at
`z = 1` and jumps by `2πi` across `(1, ∞)`. -/
@[simp]
theorem continuousAt_polylog_one_iff {z : ℂ} :
    ContinuousAt (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane := by
  refine ⟨fun hc ↦ ?_, continuousAt_polylog 1⟩
  have hc' : ContinuousAt (polylog 1) (1 - (1 - z)) := by simpa using hc
  have hcomp : ContinuousAt (fun u : ℂ ↦ -(polylog 1 (1 - u))) (1 - z) :=
    (hc'.comp (continuous_const.sub continuous_id).continuousAt).neg
  exact Complex.continuousAt_log_iff.mp
    (hcomp.congr (Eventually.of_forall fun u ↦ by simp [polylog_one]))

/-- `polylog 1` is complex differentiable at `z` if and only if `1 - z ∈ Complex.slitPlane`. -/
@[simp]
theorem differentiableAt_polylog_one_iff {z : ℂ} :
    DifferentiableAt ℂ (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane :=
  ⟨fun hd ↦ continuousAt_polylog_one_iff.mp hd.continuousAt, differentiableAt_polylog 1⟩

/-- `polylog 1` is complex analytic at `z` if and only if `1 - z ∈ Complex.slitPlane`. -/
@[simp]
theorem analyticAt_polylog_one_iff {z : ℂ} :
    AnalyticAt ℂ (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane :=
  ⟨fun ha ↦ continuousAt_polylog_one_iff.mp ha.continuousAt, analyticAt_polylog 1⟩

/-- Weight one is discontinuous on the branch cut, checked at `z = 3`. -/
theorem not_continuousAt_polylog_one_three : ¬ ContinuousAt (polylog 1) 3 := by
  rw [continuousAt_polylog_one_iff, Complex.mem_slitPlane_iff]
  norm_num

/-- The Euler differential recursion `z * Li'_{n+1}(z) = Liₙ(z)` holds in every integer weight on
the principal domain `ℂ ∖ [1, ∞)`, including at `z = 0`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  have h0 : (0 : ℂ) ∈ {w : ℂ | 1 - w ∈ Complex.slitPlane} := by
    simp [Complex.one_mem_slitPlane]
  have hf : AnalyticOnNhd ℂ (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w)
      {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    analyticOnNhd_id.mul (analyticOnNhd_polylog (n + 1)).deriv
  have hfg : (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) =ᶠ[𝓝 (0 : ℂ)] polylog n := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    exact mul_deriv_polylog_add_one_of_norm_lt_one n (mem_ball_zero_iff.mp hw)
  exact hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_polylog n)
    Complex.isPreconnected_one_sub_slitPlane h0 hfg hz

/-- Away from `0` on the principal domain, `polylog (n + 1)` has derivative `polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) : HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  refine (differentiableAt_polylog (n + 1) hz).hasDerivAt.congr_deriv ?_
  rw [← mul_deriv_polylog_add_one n hz, mul_div_cancel_left₀ _ hz0]

/-- Quotient form `Li'_{n+1}(z) = Liₙ(z) / z` for `z ≠ 0` on the principal domain. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z :=
  (hasDerivAt_polylog_add_one n hz hz0).deriv

/-- For every integer weight `n` and `z` in the principal domain, the radial integrand
`t ↦ polylog n (t * z) / t` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_mul_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  have h0 : (0 : ℂ) ∈ {w : ℂ | 1 - w ∈ Complex.slitPlane} := by
    simp [Complex.one_mem_slitPlane]
  have hdslope : ContinuousOn (dslope (polylog n) 0) {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    (continuousOn_dslope (Complex.isOpen_one_sub_slitPlane.mem_nhds h0)).mpr
      ⟨continuousOn_polylog n, differentiableAt_polylog n h0⟩
  have hseg : ContinuousOn (fun t : ℝ ↦ z * dslope (polylog n) 0 ((t : ℂ) * z)) (Icc 0 1) :=
    continuousOn_const.mul
      (hdslope.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
        fun t ht ↦ Complex.one_sub_ofReal_mul_mem_slitPlane hz ht.1 ht.2)
  refine (hseg.intervalIntegrable_of_Icc zero_le_one).congr_ae ?_
  rw [uIoc_of_le zero_le_one]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
  dsimp only
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hmul : ((t : ℂ) * z - 0) • dslope (polylog n) 0 ((t : ℂ) * z) =
      polylog n ((t : ℂ) * z) - polylog n 0 := sub_smul_dslope (polylog n) 0 ((t : ℂ) * z)
  simp only [sub_zero, polylog_zero, smul_eq_mul] at hmul
  rw [← hmul]
  field_simp [ht_ne]

/-- The recursive radial-integral identity `Li_{n+1}(z) = ∫₀¹ Liₙ(t z) / t dt` holds for every
integer weight `n : ℤ` and every `z` in the principal domain `ℂ ∖ [1, ∞)`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in (0 : ℝ)..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ polylog (n + 1) ((t : ℂ) * z)) (Icc 0 1) :=
    (continuousOn_polylog (n + 1)).comp
      ((Complex.continuous_ofReal.mul continuous_const).continuousOn)
      fun t ht ↦ Complex.one_sub_ofReal_mul_mem_slitPlane hz ht.1 ht.2
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ polylog (n + 1) ((s : ℂ) * z))
        (polylog n ((t : ℂ) * z) / (t : ℂ)) t := by
    intro t ht
    have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      Complex.one_sub_ofReal_mul_mem_slitPlane hz ht.1.le ht.2.le
    have hinner : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    have hcomp : HasDerivAt (fun s : ℝ ↦ polylog (n + 1) ((s : ℂ) * z))
        (deriv (polylog (n + 1)) ((t : ℂ) * z) * z) t :=
      (differentiableAt_polylog (n + 1) htz).hasDerivAt.comp t hinner
    refine hcomp.congr_deriv ?_
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have heuler := mul_deriv_polylog_add_one n htz
    rw [← heuler]
    field_simp [ht_ne]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (intervalIntegrable_polylog_mul_div n hz)
  simpa using hint.symm

end TauCeti.Polylog
