/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy and the Euler derivative recursion of polylogarithms

Every integer-weight polylogarithm `Liₙ` is complex analytic on the principal cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)` and satisfies Euler's differential recursion
`z * deriv (polylog n) z = polylog (n - 1) z` throughout that domain (including at `z = 0`, where
both sides vanish), together with the recursive radial-integral representation
`polylog n z = ∫ t in 0..1, polylog (n - 1) (t * z) / t`.

These results establish the principal holomorphic continuation of `polylog n` from the open unit
disc to the cut plane `ℂ ∖ [1, ∞)` and provide the differential and integral recurrences used to
study conjugation symmetry, closed-disc boundary values, monodromy, and single-valued
polylogarithms. In weight one the domain `{z | 1 - z ∈ Complex.slitPlane}` is sharp for continuity
(and hence analyticity): `continuousAt_polylog_one_iff` shows that `polylog 1` is continuous at
`z : ℂ` if and only if `1 - z ∈ Complex.slitPlane`.

## Main results

* `TauCeti.Polylog.hasDerivAt_polylog_one`, `TauCeti.Polylog.deriv_polylog_one`,
  `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`, and
  `TauCeti.Polylog.deriv_polylog_nat_add_two`:
  complex derivatives of weight one and weights `k + 2` on `{z | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.differentiableAt_polylog`, `TauCeti.Polylog.differentiableOn_polylog`,
  `TauCeti.Polylog.analyticAt_polylog`, `TauCeti.Polylog.analyticOnNhd_polylog`,
  `TauCeti.Polylog.continuousAt_polylog`, and `TauCeti.Polylog.continuousOn_polylog`:
  complex differentiability, analyticity, and continuity of `polylog n` on
  `{z | 1 - z ∈ Complex.slitPlane}` for all `n : ℤ`.
* `TauCeti.Polylog.mul_deriv_polylog`, `TauCeti.Polylog.deriv_polylog`, and
  `TauCeti.Polylog.hasDerivAt_polylog` (along with their shifted forms
  `TauCeti.Polylog.mul_deriv_polylog_add_one`, `TauCeti.Polylog.deriv_polylog_add_one`, and
  `TauCeti.Polylog.hasDerivAt_polylog_add_one`): the Euler differential recursion on the principal
  domain (and its quotient form away from `0`).
* `TauCeti.Polylog.intervalIntegrable_polylog_div`, `TauCeti.Polylog.polylog_eq_integral`, and
  `TauCeti.Polylog.polylog_add_one_eq_integral`: the recursive radial integral on the principal
  domain for all `n : ℤ`.
* `TauCeti.Polylog.continuousAt_polylog_one_iff`: `polylog 1` is continuous at `z : ℂ` if and only
  if `1 - z ∈ Complex.slitPlane`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.Polylog

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, `polylog 1` has complex derivative
`(1 - z)⁻¹`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) (1 - z)⁻¹ z := by
  have h := ((Complex.hasDerivAt_log hz).comp z
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z))).neg
  convert h using 1
  · ext w
    simp [polylog_one]
  · ring

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, `deriv (polylog 1) z = (1 - z)⁻¹`. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = (1 - z)⁻¹ :=
  (hasDerivAt_polylog_one hz).deriv

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, `polylog (k + 2)` has complex
derivative `(k !)⁻¹ * ∫ t in 0..1, (-Real.log t) ^ k / (1 - t * z)`. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  rw [funext (polylog_nat_add_two k)]
  exact (hasDerivAt_integral_radialIntegrand k hz).const_mul (Nat.factorial k : ℂ)⁻¹

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`,
`deriv (polylog (k + 2)) z = (k !)⁻¹ * ∫ t in 0..1, (-Real.log t) ^ k / (1 - t * z)`. -/
theorem deriv_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog (k + 2 : ℕ)) z =
      (Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z) :=
  (hasDerivAt_polylog_nat_add_two k hz).deriv

/-- Every integer-weight polylogarithm is complex differentiable at each point of the principal
domain `{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z := by
  have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · simpa using (analyticAt_polylog_neg_nat 0 hz1).differentiableAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt
    · simpa only [Int.ofNat_eq_natCast] using (hasDerivAt_polylog_nat_add_two k hz).differentiableAt
  | negSucc r =>
    have h := (analyticAt_polylog_neg_nat (r + 1) hz1).differentiableAt
    rwa [Nat.cast_add_one, ← Int.negSucc_eq] at h

/-- Every integer-weight polylogarithm is complex differentiable on the principal domain
`{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- Every integer-weight polylogarithm is complex analytic at each point of the principal domain
`{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  (differentiableOn_polylog n).analyticAt (Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds hz)

/-- **Holomorphy of integer-weight polylogarithms.** For every integer weight `n : ℤ`, `polylog n`
is complex analytic on the principal domain `{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ analyticAt_polylog n hz

/-- Every integer-weight polylogarithm is continuous at each point of the principal domain
`{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem continuousAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousAt (polylog n) z :=
  (analyticAt_polylog n hz).continuousAt

/-- Every integer-weight polylogarithm is continuous on the principal domain
`{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem continuousOn_polylog (n : ℤ) :
    ContinuousOn (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (analyticOnNhd_polylog n).continuousOn

/-- **Euler differential recursion for polylogarithms.** For every integer weight `n : ℤ` and every
`z` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, including `z = 0`,
`z * deriv (polylog n) z = polylog (n - 1) z`. -/
theorem mul_deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog n) z = polylog (n - 1) z := by
  have hf : AnalyticOnNhd ℂ (fun w ↦ w * deriv (polylog n) w)
      {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    fun _ hw ↦ analyticAt_id.mul (analyticAt_polylog n hw).deriv
  have hfg : (fun w : ℂ ↦ w * deriv (polylog n) w) =ᶠ[𝓝 (0 : ℂ)] polylog (n - 1) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    rw [mem_ball_zero_iff] at hw
    rw [(hasDerivAt_polylog_tsum_of_norm_lt_one n hw).deriv, polylog_eq_tsum (n - 1) hw,
      ← tsum_mul_left]
    congr 1 with k
    rw [← mul_div_assoc, ← pow_succ']
  exact hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_polylog (n - 1))
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp) hfg hz

/-- Shifted form of Euler's differential recursion: for every integer weight `n : ℤ` and every
`z` in `{z | 1 - z ∈ Complex.slitPlane}`, `z * deriv (polylog (n + 1)) z = polylog n z`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  simpa only [add_sub_cancel_right] using mul_deriv_polylog (n + 1) hz

/-- Away from `0` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`,
`deriv (polylog n) z = polylog (n - 1) z / z`. -/
theorem deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog n) z = polylog (n - 1) z / z :=
  (eq_div_iff hz0).mpr ((mul_comm _ _).trans (mul_deriv_polylog n hz))

/-- Away from `0` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`,
`deriv (polylog (n + 1)) z = polylog n z / z`. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z := by
  simpa only [add_sub_cancel_right] using deriv_polylog (n + 1) hz hz0

/-- Away from `0` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, `polylog n` has
complex derivative `polylog (n - 1) z / z`. -/
theorem hasDerivAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    HasDerivAt (polylog n) (polylog (n - 1) z / z) z :=
  deriv_polylog n hz hz0 ▸ (differentiableAt_polylog n hz).hasDerivAt

/-- Away from `0` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, `polylog (n + 1)` has
complex derivative `polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  simpa only [add_sub_cancel_right] using hasDerivAt_polylog (n + 1) hz hz0

private lemma polylog_sub_one_div_eq_mul_deriv_on_Ioc (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    polylog (n - 1) ((t : ℂ) * z) / (t : ℂ) = z * deriv (polylog n) ((t : ℂ) * z) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    Complex.one_sub_ofReal_mul_mem_slitPlane hz (Ioc_subset_Icc_self ht)
  rw [← mul_deriv_polylog n htz, mul_assoc, mul_div_cancel_left₀ _ ht0]

/-- For every integer weight `n : ℤ` and every `z` in the principal domain
`{z | 1 - z ∈ Complex.slitPlane}`, the radial quotient `t ↦ polylog n (t * z) / t` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    refine continuousOn_const.mul (((analyticOnNhd_polylog (n + 1)).deriv.continuousOn).comp
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
      fun t ht ↦ Complex.one_sub_ofReal_mul_mem_slitPlane hz ht)
  refine hcont.intervalIntegrable.congr ?_
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simpa only [add_sub_cancel_right] using
    (polylog_sub_one_div_eq_mul_deriv_on_Ioc (n + 1) hz ht).symm

/-- **Recursive radial-integral representation of polylogarithms.** For every integer weight `n : ℤ`
and every `z` in the principal domain `{z | 1 - z ∈ Complex.slitPlane}`,
`polylog n z = ∫ t in 0..1, polylog (n - 1) (t * z) / t`. -/
theorem polylog_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n z = ∫ t : ℝ in 0..1, polylog (n - 1) ((t : ℂ) * z) / (t : ℂ) := by
  let g : ℝ → ℂ := fun t ↦ polylog n ((t : ℂ) * z)
  let g' : ℝ → ℂ := fun t ↦ z * deriv (polylog n) ((t : ℂ) * z)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      Complex.one_sub_ofReal_mul_mem_slitPlane hz ht
    have hin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    simpa only [g, g', Function.comp_def, smul_eq_mul] using
      ((differentiableAt_polylog n htz).hasDerivAt).scomp t hin
  have hint_g' : IntervalIntegrable g' volume 0 1 := by
    refine (intervalIntegrable_polylog_div (n - 1) hz).congr ?_
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    exact polylog_sub_one_div_eq_mul_deriv_on_Ioc n hz ht
  have hcongr : (∫ t : ℝ in 0..1, polylog (n - 1) ((t : ℂ) * z) / (t : ℂ)) =
      ∫ t : ℝ in 0..1, g' t := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    exact polylog_sub_one_div_eq_mul_deriv_on_Ioc n hz ht
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_g']
  simp [g]

/-- Shifted form of the recursive radial-integral representation: for every integer weight `n : ℤ`
and every `z` in `{z | 1 - z ∈ Complex.slitPlane}`,
`polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  simpa only [add_sub_cancel_right] using polylog_eq_integral (n + 1) hz

/-- `polylog 1` is continuous at `z : ℂ` if and only if `1 - z ∈ Complex.slitPlane`, characterizing
its maximal domain of continuity across `ℂ` (failing at the logarithmic pole `z = 1` and along the
open branch cut `(1, ∞)`). -/
theorem continuousAt_polylog_one_iff {z : ℂ} :
    ContinuousAt (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane := by
  refine ⟨fun hc ↦ ?_, fun hz ↦ (hasDerivAt_polylog_one hz).continuousAt⟩
  by_contra hns
  have him : z.im = 0 := by simpa using Complex.im_eq_zero_of_notMem_slitPlane hns
  have hre : 1 ≤ z.re := by
    have := mt (fun h ↦ Complex.mem_slitPlane_iff.mpr (Or.inl h)) hns
    simpa only [Complex.sub_re, Complex.one_re, sub_pos, not_lt] using this
  have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  rcases hre.eq_or_lt with h1 | hx
  · have hz1 : z = 1 := by rw [hz_eq, ← h1, Complex.ofReal_one]
    have hlog : ContinuousAt Real.log 0 := by
      have h : ContinuousAt (fun t : ℝ ↦ -(polylog 1 (1 - (t : ℂ))).re) 0 :=
        (Complex.continuous_re.continuousAt.comp
          (hc.comp_of_eq (continuousAt_const.sub Complex.continuous_ofReal.continuousAt)
            (by simp [hz1]))).neg
      exact h.congr (Eventually.of_forall fun t ↦ by simp [polylog_one, Complex.log_re])
    exact Real.continuousAt_log_iff.mp hlog rfl
  · have hw : Tendsto (fun t : ℝ ↦ z + (t : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 z) := by
      have hcont : Continuous (fun t : ℝ ↦ z + (t : ℂ) * Complex.I) := by fun_prop
      simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have him_tendsto : Tendsto (fun t : ℝ ↦ (polylog 1 (z + (t : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 (-Real.pi)) := by
      have him_val : (polylog 1 z).im = -Real.pi := by
        have hsub : (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
        rw [polylog_one, Complex.neg_im, hsub, Complex.log_im,
          Complex.arg_ofReal_of_neg (by linarith)]
      rw [← him_val]
      exact (Complex.continuous_im.continuousAt.comp hc).tendsto.comp hw
    have him_nonneg : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ (polylog 1 (z + (t : ℂ) * Complex.I)).im := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have him_neg : (1 - (z + (t : ℂ) * Complex.I)).im < 0 := by simpa [him] using ht
      rw [polylog_one, Complex.neg_im, Complex.log_im]
      linarith [Complex.arg_neg_iff.mpr him_neg]
    linarith [ge_of_tendsto him_tendsto him_nonneg, Real.pi_pos]

end TauCeti.Polylog
