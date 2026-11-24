/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.MeasureTheory.Function.UniformIntegrable

/-!
# Integrability of the polylogarithm's radial integrand

For `k : ℕ` and `z : ℂ`, the polylogarithm of weight `k + 2` is the logarithmic radial integral
`Li_{k+2}(z) = (1 / k!) ∫₀¹ (-log t) ^ k * (-Log (1 - t z)) / t dt`, where `Log` is Mathlib's
principal complex logarithm. This file proves that the integrand is interval integrable on
`[0, 1]` for **every** complex `z`, that modifying it at the endpoints or at the possible zero of
`1 - t z` does not change the integral, that on a compact subset of the principal domain
`ℂ ∖ [1, ∞) = {z | 1 - z ∈ slitPlane}` it has a single integrable majorant `C * |log t| ^ k`, and
that over any bounded family of parameters `z` the integrands are uniformly integrable on `(0, 1]`.

Near `t = 0` the factor `-Log (1 - t z)` is `O(t z)`, so the integrand is dominated by a multiple
of `|log t| ^ k`. Away from `t = 0` the factor `(-log t) ^ k / t` is continuous, and
`Log (1 - t z)` is integrable even when `1 - t z` vanishes on `[0, 1]` (for real `z ≥ 1`): its
real part has a logarithmic singularity and its imaginary part is bounded by `π`. On a compact
subset of the principal domain, `1 - t z` stays uniformly away from zero for `t ∈ [0, 1]`; this
gives the uniform majorant of the integrand, and the same lower bound controls its derivative
`(-log t) ^ k / (1 - t z)` in `z`. On a general bounded parameter family `‖z‖ ≤ R`, a common
integrable majorant need not exist (for example, on the full ball with `R > 1`, the logarithmic
singularity at `t = 1 / z` moves through `(1 / R, 1)`); instead, translating
`log |t - Re(1 / z)| ^ 2` gives a uniform `L²` bound on `(0, 1]`, which yields
`MeasureTheory.UniformIntegrable` in `L¹` over the finite-measure interval `(0, 1]`.

## Main declarations

* `TauCeti.Polylog.intervalIntegrable_radialIntegrand`: interval integrability on `[0, 1]` for
  every `z`.
* `TauCeti.Polylog.integral_eq_integral_radialIntegrand_of_eqOn`: modifying the radial integrand
  at `0`, `1`, and the possible zero of `1 - t z` leaves the integral unchanged.
* `TauCeti.Polylog.exists_norm_radialIntegrand_le`: the uniform majorant `C * |log t| ^ k` on a
  compact subset of the principal domain.
* `TauCeti.Polylog.exists_setLIntegral_norm_radialIntegrand_sq_le` and
  `TauCeti.Polylog.uniformIntegrable_radialIntegrand`: uniform `L²` bound and uniform
  integrability on `(0, 1]` over bounded parameter families.
* `TauCeti.Polylog.intervalIntegrable_neg_log_pow_div_one_sub_mul`: interval integrability of the
  differentiated kernel `(-log t) ^ k / (1 - t z)` on `[0, 1]` for `z` in the principal domain.
* `TauCeti.Polylog.hasDerivAt_integral_radialIntegrand`: parametric complex derivative of the
  weight-`(k + 2)` radial integral (omitting the factor `(k!)⁻¹`) on the principal domain.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (3), p. 50, and §1.4, p. 51.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Polylog

/-- The norm of the radial integrand at a positive parameter. -/
private lemma norm_radialIntegrand {t : ℝ} (ht : 0 < t) (k : ℕ) (z : ℂ) :
    ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ =
      |Real.log t| ^ k * ‖Complex.log (1 - t * z)‖ / t := by
  rw [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    Complex.norm_real, Real.norm_of_nonneg ht.le]

/-- Near `t = 0` the radial integrand is dominated by `(3 / 2) ‖z‖ |log t| ^ k`. -/
private lemma norm_radialIntegrand_le_of_mul_le {t : ℝ} (ht : 0 < t) (k : ℕ) {z : ℂ}
    (htz : t * ‖z‖ ≤ 1 / 2) :
    ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤
      3 / 2 * ‖z‖ * |Real.log t| ^ k := by
  have hnorm : ‖-((t : ℂ) * z)‖ = t * ‖z‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hlog : ‖Complex.log (1 - t * z)‖ ≤ 3 / 2 * (t * ‖z‖) := by
    have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) (by rwa [hnorm])
    rwa [hnorm, ← sub_eq_add_neg] at h
  rw [norm_radialIntegrand ht, div_le_iff₀ ht]
  calc |Real.log t| ^ k * ‖Complex.log (1 - t * z)‖
      ≤ |Real.log t| ^ k * (3 / 2 * (t * ‖z‖)) := by gcongr
    _ = 3 / 2 * ‖z‖ * |Real.log t| ^ k * t := by ring

/-- The radial integrand `t ↦ (-log t) ^ k * (-Log (1 - t z)) / t` of the polylogarithm of
weight `k + 2` is interval integrable on `[0, 1]` for every `z : ℂ`, including real `z ≥ 1`,
where `1 - t z` vanishes at `t = 1 / z`. -/
theorem intervalIntegrable_radialIntegrand (k : ℕ) (z : ℂ) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t) volume 0 1 := by
  set a : ℝ := 1 / (2 * (‖z‖ + 1)) with ha_def
  have ha0 : 0 < a := by positivity
  have haz : a * ‖z‖ ≤ 1 / 2 := by
    rw [ha_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (by positivity)]
    linarith [norm_nonneg z]
  refine IntervalIntegrable.trans (b := a) ?_ ?_
  · -- On `[0, a]`, dominate by a multiple of `|log t| ^ k`.
    refine (((intervalIntegrable_log_pow k).norm).const_mul (3 / 2 * ‖z‖)).mono_fun'
      (by fun_prop : Measurable _).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_)
    rw [uIoc_of_le ha0.le] at ht
    dsimp only
    rw [Real.norm_eq_abs, abs_pow]
    exact norm_radialIntegrand_le_of_mul_le ht.1 k
      ((mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans haz)
  · -- On `[a, 1]`, the factor `(-log t) ^ k / t` is continuous and `Log (1 - t z)` integrable.
    have hlog : IntervalIntegrable (fun t : ℝ ↦ -Complex.log (1 - t * z)) volume a 1 :=
      (AnalyticOnNhd.intervalIntegrable_clog fun t _ ↦
        analyticAt_const.sub ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)).neg
    have hcont : ContinuousOn (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / t) (uIcc a 1) := by
      intro t ht
      rw [uIcc_of_le ha1] at ht
      have ht0 : t ≠ 0 := (ha0.trans_le ht.1).ne'
      exact ((Complex.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_log ht0).neg).pow k |>.div Complex.continuous_ofReal.continuousAt
        (Complex.ofReal_ne_zero.2 ht0)).continuousWithinAt
    convert hlog.continuousOn_mul hcont using 2 with t
    ring

/-- On a compact subset `K` of the principal domain `ℂ ∖ [1, ∞)`, the radial integrand of the
polylogarithm of weight `k + 2` has the single integrable majorant `C * |log t| ^ k` on `(0, 1]`,
uniformly in `z ∈ K`. -/
theorem exists_norm_radialIntegrand_le (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ C, ∀ z ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤ C * |Real.log t| ^ k := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_le_norm_one_sub_ofReal_mul hKΩ
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R' : ℝ := max R 0
  set a : ℝ := 1 / (2 * (R' + 1)) with ha_def
  have ha0 : 0 < a := by positivity
  have haR : a * R' ≤ 1 / 2 := by
    rw [ha_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith [le_max_right R 0]
  -- Away from `t = 0`, `‖Log (1 - t z)‖ ≤ |log ‖1 - t z‖| + π ≤ M`.
  set M : ℝ := |Real.log δ| + |Real.log (1 + R')| + Real.pi
  refine ⟨3 / 2 * R' + M / a, fun z hz t ht ↦ ?_⟩
  have hzR : ‖z‖ ≤ R' := (hR z hz).trans (le_max_left R 0)
  rcases le_or_gt t a with hta | hta
  · -- Near `t = 0`.
    calc _ ≤ 3 / 2 * ‖z‖ * |Real.log t| ^ k := norm_radialIntegrand_le_of_mul_le ht.1 k
            ((mul_le_mul hta hzR (norm_nonneg z) ha0.le).trans haR)
      _ ≤ (3 / 2 * R' + M / a) * |Real.log t| ^ k := by
            gcongr
            · linarith [div_nonneg (by positivity : 0 ≤ M) ha0.le]
  · -- Away from `t = 0`.
    have hw0 : δ ≤ ‖1 - t * z‖ := hδK z hz t (Ioc_subset_Icc_self ht)
    have hw1 : ‖1 - t * z‖ ≤ 1 + R' := by
      calc ‖1 - t * z‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * z‖ := norm_sub_le _ _
        _ ≤ 1 + R' := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
          nlinarith [ht.2, norm_nonneg z]
    have hlogM : ‖Complex.log (1 - t * z)‖ ≤ M := by
      have hlogw : |Real.log ‖1 - t * z‖| ≤ |Real.log δ| + |Real.log (1 + R')| := by
        have h1 := Real.log_le_log hδ hw0
        have h2 := Real.log_le_log (hδ.trans_le hw0) hw1
        rw [abs_le]
        constructor <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log (1 + R')),
          abs_nonneg (Real.log δ), abs_nonneg (Real.log (1 + R'))]
      calc ‖Complex.log (1 - t * z)‖
          ≤ |(Complex.log (1 - t * z)).re| + |(Complex.log (1 - t * z)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ M := by
            rw [Complex.log_re, Complex.log_im]
            linarith [Complex.abs_arg_le_pi (1 - t * z)]
    rw [norm_radialIntegrand ht.1, div_le_iff₀ ht.1]
    calc |Real.log t| ^ k * ‖Complex.log (1 - t * z)‖ ≤ |Real.log t| ^ k * M := by gcongr
      _ = M / a * |Real.log t| ^ k * a := by field_simp
      _ ≤ (3 / 2 * R' + M / a) * |Real.log t| ^ k * t := by
          gcongr
          · linarith [le_max_right R 0]

/-- Any function agreeing with the polylogarithm's radial integrand on `(0, 1)` away from the
possible zero of `1 - t z` has the same interval integral on `[0, 1]`. -/
theorem integral_eq_integral_radialIntegrand_of_eqOn (k : ℕ) (z : ℂ) {g : ℝ → ℂ}
    (hg : EqOn g (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t)
      {t ∈ Ioo (0 : ℝ) 1 | 1 - (t : ℂ) * z ≠ 0}) :
    (∫ t : ℝ in 0..1, g t) =
      ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le zero_le_one]
  have hIoo : ∀ᵐ t : ℝ ∂volume, t ∈ Ioc (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1) (μ := volume)] with t ht htIoc
    exact ht.mpr htIoc
  filter_upwards [hIoo, Complex.ae_one_sub_ofReal_mul_ne_zero z] with t ht₁ ht₂ htIoc
  exact hg ⟨ht₁ htIoc, ht₂⟩

/-- Away from `t = 0` (`0 < a ≤ 1`), the Lebesgue integral of the `p`-th power of the norm of the
polylogarithm radial integrand on `(a, 1]` is bounded by `(|log a| ^ k / a) ^ p` times that of
`t ↦ Log (1 - t * z)` on `(a, 1]`. -/
private lemma setLIntegral_norm_radialIntegrand_pow_Ioc_le (p k : ℕ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) (z : ℂ) :
    ∫⁻ t in Ioc a 1,
        ENNReal.ofReal (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ p) ≤
      ENNReal.ofReal ((|Real.log a| ^ k / a) ^ p) *
        ∫⁻ t in Ioc a 1, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ p) := by
  rw [← lintegral_const_mul _ (by fun_prop)]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  have ht0 : 0 < t := ha0.trans ht.1
  have hlogt : |Real.log t| ≤ |Real.log a| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le ht.2), abs_of_nonpos (Real.log_nonpos ha0.le ha1)]
    exact neg_le_neg (Real.log_le_log ha0 ht.1.le)
  have h1 : ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤
      (|Real.log a| ^ k / a) * ‖Complex.log (1 - t * z)‖ := by
    rw [norm_radialIntegrand ht0, div_mul_eq_mul_div]
    exact div_le_div₀ (by positivity) (by gcongr) ha0 ht.1.le
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    ((pow_le_pow_left₀ (norm_nonneg _) h1 p).trans_eq (mul_pow _ _ p))

/-- Over any bounded ball `‖z‖ ≤ R`, the radial integrand of weight `k + 2` has a uniform `L²`
bound on `(0, 1]`. -/
theorem exists_setLIntegral_norm_radialIntegrand_sq_le (k : ℕ) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : ℂ, ‖z‖ ≤ R →
      ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2) ≤
          C := by
  set R' : ℝ := max R 0
  set a : ℝ := 1 / (2 * (R' + 1)) with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one (by positivity)]; linarith [le_max_right R 0]
  have haR : a * R' ≤ 1 / 2 := by
    rw [ha_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith [le_max_right R 0]
  set I₁ : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (|Real.log t| ^ (2 * k))
  have hI₁ : I₁ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun t ↦ ?_)
      (intervalIntegrable_log_pow (2 * k) (a := 0) (b := 1)).1.hasFiniteIntegral
    rw [← ofReal_norm, norm_pow, Real.norm_eq_abs]
  obtain ⟨C₂, hC₂, hC₂z⟩ := exists_setLIntegral_norm_clog_one_sub_mul_pow_le 2 a 1 R'
  set Ka : ℝ := |Real.log a| ^ k / a
  refine ⟨ENNReal.ofReal ((3 / 2 * R') ^ 2) * I₁ + ENNReal.ofReal (Ka ^ 2) * C₂,
    by finiteness, fun z hz ↦ ?_⟩
  have hzR : ‖z‖ ≤ R' := hz.trans (le_max_left R 0)
  rw [(Ioc_union_Ioc_eq_Ioc ha0.le ha1).symm]
  refine (lintegral_union_le _ (Ioc 0 a) (Ioc a 1)).trans (add_le_add ?_
    ((setLIntegral_norm_radialIntegrand_pow_Ioc_le 2 k ha0 ha1 z).trans
      (by gcongr; exact hC₂z z hzR)))
  calc ∫⁻ t in Ioc 0 a, ENNReal.ofReal
          (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((3 / 2 * R') ^ 2 * |Real.log t| ^ (2 * k)) := by
        refine (setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ENNReal.ofReal_le_ofReal ?_).trans
          (lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc_right ha1) le_rfl) le_rfl)
        have h1 : ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤
            3 / 2 * R' * |Real.log t| ^ k :=
          (norm_radialIntegrand_le_of_mul_le ht.1 k
            ((mul_le_mul ht.2 hzR (norm_nonneg z) ha0.le).trans haR)).trans (by gcongr)
        exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans_eq
          (by rw [mul_pow, ← pow_mul, mul_comm k 2])
    _ = ENNReal.ofReal ((3 / 2 * R') ^ 2) * I₁ := by
        simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
        exact lintegral_const_mul _ (by fun_prop)

/-- Over any bounded family of complex parameters `z i`, the radial integrands of the polylogarithm
of weight `k + 2` are uniformly integrable (`MeasureTheory.UniformIntegrable`, and hence
`MeasureTheory.UnifIntegrable` via `.unifIntegrable`) on `(0, 1]`. -/
theorem uniformIntegrable_radialIntegrand {ι : Type*} (k : ℕ) {z : ι → ℂ}
    (hz : Bornology.IsBounded (Set.range z)) :
    UniformIntegrable
      (fun (i : ι) (t : ℝ) ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z i)) / t)
      1 (volume.restrict (Ioc 0 1)) := by
  obtain ⟨R, hR⟩ := hz.exists_norm_le
  obtain ⟨C, hC, hCz⟩ := exists_setLIntegral_norm_radialIntegrand_sq_le k R
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Ioc]⟩
  refine MeasureTheory.uniformIntegrable_of_eLpNorm_le (p := 1) (q := 2)
    (C := C ^ (2⁻¹ : ℝ)) (by norm_num) (by finiteness) fun i ↦ ?_
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z i)) / t)
      (volume.restrict (Ioc 0 1)) :=
    (intervalIntegrable_radialIntegrand k (z i)).1.aestronglyMeasurable
  have h2 : eLpNorm
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z i)) / t)
      ((2 : ℝ≥0) : ℝ≥0∞) (volume.restrict (Ioc 0 1)) ^ ((2 : ℝ≥0) : ℝ) ≤ C := by
    rw [eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) two_ne_zero hmeas]
    simp_rw [NNReal.coe_ofNat, ← ofReal_norm, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact hCz (z i) (hR (z i) (mem_range_self i))
  exact (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mpr
    (by simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat] using h2)

/-- Pointwise complex derivative of the radial polylogarithm integrand in `w` away from `t = 0`
whenever `1 - t * w ∈ Complex.slitPlane`. -/
private lemma hasDerivAt_radialIntegrand (k : ℕ) {t : ℝ} (ht : t ≠ 0) {w : ℂ}
    (htw : 1 - (t : ℂ) * w ∈ Complex.slitPlane) :
    HasDerivAt
      (fun x : ℂ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * x)) / (t : ℂ))
      (((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)) w := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have htw0 : 1 - (t : ℂ) * w ≠ 0 := Complex.slitPlane_ne_zero htw
  have hin : HasDerivAt (fun x : ℂ ↦ 1 - (t : ℂ) * x) (0 - (t : ℂ) * 1) w :=
    (hasDerivAt_const w (1 : ℂ)).sub ((hasDerivAt_id w).const_mul (t : ℂ))
  have hlog := (((Complex.hasDerivAt_log htw).comp w hin).neg.const_mul
    (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
  refine hlog.congr_deriv ?_
  field_simp [ht0, htw0]
  ring

/-- Parametric differentiation of the weight-`(k + 2)` radial integral (omitting the factor
`(k!)⁻¹`) on the principal domain, yielding both interval integrability of the differentiated kernel
and `HasDerivAt` of the integral. -/
private lemma intervalIntegrable_and_hasDerivAt_radialIntegrand (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 ∧
    HasDerivAt
      (fun w : ℂ ↦ ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ))
      (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds hz)
  obtain ⟨δ, hδ, hδ_le⟩ := (isCompact_closedBall z ε).exists_le_norm_one_sub_ofReal_mul hball
  let F : ℂ → ℝ → ℂ := fun w t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun w t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)
  let bound : ℝ → ℝ := fun t ↦ δ⁻¹ * |Real.log t| ^ k
  have hbound : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ∀ w ∈ closedBall z ε, ‖F' w t‖ ≤ bound t := by
    refine ae_of_all _ fun t ht w hw_mem ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hw : δ ≤ ‖1 - (t : ℂ) * w‖ := hδ_le w hw_mem t (Ioc_subset_Icc_self ht)
    dsimp only [F', bound]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, div_eq_inv_mul]
    gcongr
  have hbound_int : IntervalIntegrable bound volume 0 1 := by
    have hlog : IntervalIntegrable (fun t : ℝ ↦ |Real.log t| ^ k) volume 0 1 := by
      simpa only [Real.norm_eq_abs, abs_pow] using (intervalIntegrable_log_pow k).norm
    exact hlog.const_mul δ⁻¹
  have hdiff : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ∀ w ∈ closedBall z ε, HasDerivAt (fun x ↦ F x t) (F' w t) w := by
    refine ae_of_all _ fun t ht w hw_mem ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hasDerivAt_radialIntegrand k ht.1.ne'
      (Complex.one_sub_ofReal_mul_mem_slitPlane (hball hw_mem) (Ioc_subset_Icc_self ht))
  exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z hε)
    (Eventually.of_forall fun w ↦ (by fun_prop : Measurable (F w)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z)
    (by fun_prop : Measurable (F' z)).aestronglyMeasurable
    hbound hbound_int hdiff

/-- For every `k : ℕ` and `z` in `{z | 1 - z ∈ Complex.slitPlane}`, the differentiated radial
kernel `t ↦ (-Real.log t) ^ k / (1 - t * z)` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_neg_log_pow_div_one_sub_mul (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 :=
  (intervalIntegrable_and_hasDerivAt_radialIntegrand k hz).1

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, the weight-`(k + 2)` radial
integral (omitting the factor `(k!)⁻¹`) has complex derivative
`∫ t in 0..1, (-Real.log t) ^ k / (1 - t * z)`. -/
theorem hasDerivAt_integral_radialIntegrand (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt
      (fun w : ℂ ↦ ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ))
      (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z :=
  (intervalIntegrable_and_hasDerivAt_radialIntegrand k hz).2

end TauCeti.Polylog
