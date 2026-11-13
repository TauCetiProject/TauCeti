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
import TauCeti.MeasureTheory.Function.DeLaValleePoussin

/-!
# Integrability of the polylogarithm's radial integrand

For `k : ℕ` and `z : ℂ`, the polylogarithm of weight `k + 2` is the logarithmic radial integral
`Li_{k+2}(z) = (1 / k!) ∫₀¹ (-log t) ^ k * (-Log (1 - t z)) / t dt`, where `Log` is Mathlib's
principal complex logarithm. This file proves that the integrand is interval integrable on
`[0, 1]` for **every** complex `z`, that on a compact subset of the principal domain
`ℂ ∖ [1, ∞) = {z | 1 - z ∈ slitPlane}` it has a single integrable majorant `C * |log t| ^ k`,
and that on any bounded parameter set `B ⊆ ℂ` — including points on `[1, ∞)` where `1 - t z` has
a moving zero inside `(0, 1]` — the family of radial integrands is uniformly integrable on
`(0, 1]`.

Near `t = 0` the factor `-Log (1 - t z)` is `O(t z)`, so the integrand is dominated by a multiple
of `|log t| ^ k`. Away from `t = 0` the factor `(-log t) ^ k / t` is continuous, and
`Log (1 - t z)` is integrable even when `1 - t z` vanishes on `[0, 1]` (for real `z ≥ 1`): its
real part has a logarithmic singularity and its imaginary part is bounded by `π`. On a compact
subset of the principal domain, `1 - t z` stays uniformly away from zero for `t ∈ [0, 1]`; this
gives the uniform majorant of the integrand, and the same lower bound controls its derivative
`(-log t) ^ k / (1 - t z)` in `z`.

On a general bounded set `B ⊆ ℂ`, no single integrable pointwise majorant exists as `z` varies
along `[1, ∞)`, because the logarithmic singularity at `t = 1 / z` moves. Splitting `[0, 1]` at a
fixed point `a > 0` puts `|log t| ^ k` in `L²` on `(0, a]`, while on `(a, 1]` the lower bound
`‖1 - t z‖ ≥ (1 / 2) |t - Re (z⁻¹)|` controls `Log (1 - t z)` by a translate of `log |t - s|`
with `|s| ≤ 2`, whose `L²` norm is uniformly bounded by translation invariance of Lebesgue
measure. De la Vallée Poussin's criterion with `Φ(x) = x ^ 2` then yields `UniformIntegrable`, and
Vitali's convergence theorem yields passage to the limit under the radial integral whenever
`Log (1 - t z)` converges almost everywhere on `(0, 1]`.

## Main declarations

* `TauCeti.Polylog.intervalIntegrable_radialIntegrand`: interval integrability on `[0, 1]` for
  every `z`.
* `TauCeti.Polylog.integral_radialIntegrand_eq_of_eqOn`: changing the integrand off `(0, 1)` and
  at the (at most single) real root of `1 - t z = 0` leaves the radial integral unchanged.
* `TauCeti.Polylog.exists_le_norm_one_sub_ofReal_mul`: on a compact subset of the principal
  domain, `‖1 - t z‖` is bounded below by a positive constant for `t ∈ [0, 1]`.
* `TauCeti.Polylog.exists_norm_radialIntegrand_le`: the uniform majorant `C * |log t| ^ k` on a
  compact subset of the principal domain.
* `TauCeti.Polylog.intervalIntegrable_norm_radialIntegrand_sq` and
  `TauCeti.Polylog.exists_integral_norm_radialIntegrand_sq_le`: square-integrability and uniform
  `L²` bound on `[0, 1]` over bounded parameter sets in `ℂ`.
* `TauCeti.Polylog.uniformIntegrable_radialIntegrand`: uniform integrability on `(0, 1]` over
  bounded parameter sets in `ℂ`.
* `TauCeti.Polylog.tendsto_integral_radialIntegrand_of_tendsto_ae`: Vitali limit under the radial
  integral from almost-everywhere convergence of `Log (1 - t * φ a)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (3), p. 50, and §1.4, p. 51.
-/

public section

open Filter MeasureTheory Set
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

/-- On a compact subset `K` of the principal domain `ℂ ∖ [1, ∞)`, the factors `1 - t z` with
`t ∈ [0, 1]` stay uniformly away from zero. -/
theorem exists_le_norm_one_sub_ofReal_mul {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ δ > 0, ∀ z ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖1 - t * z‖ := by
  -- `1 - t z = 1 + t • (-z)` lies on the segment from `1` to `1 - z` in the star-convex slit plane.
  have hpos : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ K, 0 < ‖1 - p.1 * p.2‖ := by
    intro p hp
    have hz : 1 + -p.2 ∈ Complex.slitPlane := by simpa [sub_eq_add_neg] using hKΩ hp.2
    have hmem := Complex.starConvex_one_slitPlane.add_smul_mem hz hp.1.1 hp.1.2
    rw [Complex.real_smul, mul_neg, ← sub_eq_add_neg] at hmem
    exact norm_pos_iff.2 (Complex.slitPlane_ne_zero hmem)
  obtain ⟨δ, hδ, h⟩ := (isCompact_Icc.prod hK).exists_forall_le' (by fun_prop) hpos
  exact ⟨δ, hδ, fun z hz t ht ↦ h (t, z) ⟨ht, hz⟩⟩

/-- On a compact subset `K` of the principal domain `ℂ ∖ [1, ∞)`, the radial integrand of the
polylogarithm of weight `k + 2` has the single integrable majorant `C * |log t| ^ k` on `(0, 1]`,
uniformly in `z ∈ K`. -/
theorem exists_norm_radialIntegrand_le (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ C, ∀ z ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤ C * |Real.log t| ^ k := by
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_ofReal_mul hK hKΩ
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

/-- Changing a function off the open unit interval `(0, 1)` and at the (at most single) real root
of `1 - t * z = 0` leaves its `[0, 1]` integral against the polylogarithm's radial integrand
unchanged. -/
theorem integral_radialIntegrand_eq_of_eqOn (k : ℕ) (z : ℂ) {g : ℝ → ℂ}
    (hg : ∀ t ∈ Ioo (0 : ℝ) 1, 1 - (t : ℂ) * z ≠ 0 →
      g t = ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t) :
    ∫ t : ℝ in 0..1, g t =
      ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t := by
  have hsub : ({t : ℝ | 1 - (t : ℂ) * z = 0} : Set ℝ).Subsingleton := by
    intro t₁ ht₁ t₂ ht₂
    have h₁ : (t₁ : ℂ) * z = 1 := (sub_eq_zero.mp ht₁).symm
    have h₂ : (t₂ : ℂ) * z = 1 := (sub_eq_zero.mp ht₂).symm
    have hz : z ≠ 0 := right_ne_zero_of_mul_eq_one h₁
    exact Complex.ofReal_injective (mul_right_cancel₀ hz (h₁.trans h₂.symm))
  have hfin : (({1} ∪ {t : ℝ | 1 - (t : ℂ) * z = 0}) : Set ℝ).Finite :=
    (finite_singleton 1).union hsub.finite
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (hfin.measure_zero volume)] with t ht htu
  rw [uIoc_of_le zero_le_one] at htu
  have ht1 : t ≠ 1 := fun h ↦ ht (Or.inl h)
  have htz : 1 - (t : ℂ) * z ≠ 0 := fun h ↦ ht (Or.inr h)
  exact hg t ⟨htu.1, lt_of_le_of_ne htu.2 ht1⟩ htz

/-- On `(0, 1]` away from the real part `s` of `z⁻¹` (when `1 / 2 ≤ ‖z‖`, and `0` otherwise),
`‖Log (1 - t z)‖` is controlled by a constant depending only on `R ≥ ‖z‖` plus `|log (t - s)|`. -/
private lemma norm_log_one_sub_ofReal_mul_le_of_norm_le {R : ℝ} (hR : 1 ≤ R) {z : ℂ}
    (hzR : ‖z‖ ≤ R) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (hts : t ≠ if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0) :
    ‖Complex.log (1 - t * z)‖ ≤
      Real.log 2 + Real.log (1 + R) + Real.pi +
        |Real.log (t - if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0)| := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  by_cases hz : 1 / 2 ≤ ‖z‖
  · simp only [hz, ↓reduceIte] at hts ⊢
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hlow : 1 / 2 * |t - (z⁻¹).re| ≤ ‖1 - (t : ℂ) * z‖ := by
      have hfact : 1 - (t : ℂ) * z = -z * ((t : ℂ) - z⁻¹) := by field_simp; ring
      rw [hfact, norm_mul, norm_neg]
      calc 1 / 2 * |t - (z⁻¹).re| = 1 / 2 * |((t : ℂ) - z⁻¹).re| := by simp
        _ ≤ ‖z‖ * ‖(t : ℂ) - z⁻¹‖ := by gcongr; exact Complex.abs_re_le_norm _
    have hupp : ‖1 - (t : ℂ) * z‖ ≤ 1 + R := by
      calc ‖1 - (t : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * z‖ := norm_sub_le _ _
        _ ≤ 1 + R := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
          nlinarith [ht.2, norm_nonneg z]
    have habs_pos : 0 < |t - (z⁻¹).re| := abs_pos.2 (sub_ne_zero.2 hts)
    have hpos_low : 0 < 1 / 2 * |t - (z⁻¹).re| := by positivity
    have hlog_low : -Real.log 2 + Real.log (t - (z⁻¹).re) ≤ Real.log ‖1 - (t : ℂ) * z‖ := by
      have h1 := Real.log_le_log hpos_low hlow
      rwa [Real.log_mul (by positivity) habs_pos.ne', one_div, Real.log_inv, Real.log_abs] at h1
    have hlog_upp : Real.log ‖1 - (t : ℂ) * z‖ ≤ Real.log (1 + R) :=
      Real.log_le_log (hpos_low.trans_le hlow) hupp
    have hre : |Real.log ‖1 - (t : ℂ) * z‖| ≤
        Real.log 2 + Real.log (1 + R) + |Real.log (t - (z⁻¹).re)| :=
      abs_le.2 ⟨by linarith [neg_abs_le (Real.log (t - (z⁻¹).re))],
        by linarith [abs_nonneg (Real.log (t - (z⁻¹).re))]⟩
    calc ‖Complex.log (1 - t * z)‖
        ≤ |(Complex.log (1 - t * z)).re| + |(Complex.log (1 - t * z)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Real.log 2 + Real.log (1 + R) + Real.pi + |Real.log (t - (z⁻¹).re)| := by
          rw [Complex.log_re, Complex.log_im]
          linarith [Complex.abs_arg_le_pi (1 - t * z)]
  · simp only [hz, ↓reduceIte]
    have hnorm : ‖-((t : ℂ) * z)‖ ≤ 1 / 2 := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.2, norm_nonneg z, lt_of_not_ge hz]
    have hlog : ‖Complex.log (1 - t * z)‖ ≤ 3 / 4 := by
      have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) hnorm
      rw [← sub_eq_add_neg] at h
      linarith
    linarith [Real.two_le_pi, abs_nonneg (Real.log (t - 0))]

/-- Uniform `L²` integrability and bound on the near-zero subinterval `[0, a]`. -/
private lemma norm_radialIntegrand_sq_integrable_zero_to_a (k : ℕ) {R a : ℝ} (ha0 : 0 < a)
    (haR : a * R ≤ 1 / 2) {z : ℂ} (hzR : ‖z‖ ≤ R) :
    IntervalIntegrable
      (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      volume 0 a ∧
    ∫ t : ℝ in 0..a, ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
      ∫ t : ℝ in 0..a, (3 / 2 * R) ^ 2 * Real.log t ^ (2 * k) := by
  have hg : IntervalIntegrable (fun t : ℝ ↦ (3 / 2 * R) ^ 2 * Real.log t ^ (2 * k)) volume 0 a :=
    (intervalIntegrable_log_pow (2 * k)).const_mul _
  have hle : ∀ t ∈ Ioc 0 a,
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
        (3 / 2 * R) ^ 2 * Real.log t ^ (2 * k) := by
    intro t ht
    have h1 : ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤
        3 / 2 * R * |Real.log t| ^ k :=
      (norm_radialIntegrand_le_of_mul_le ht.1 k
        ((mul_le_mul ht.2 hzR (norm_nonneg z) ha0.le).trans haR)).trans (by gcongr)
    have h0 : 0 ≤ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ := norm_nonneg _
    calc ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2
        ≤ (3 / 2 * R * |Real.log t| ^ k) ^ 2 := sq_le_sq' (by linarith) h1
      _ = (3 / 2 * R) ^ 2 * Real.log t ^ (2 * k) := by
          rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, sq_abs, ← pow_mul]
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      volume 0 a := by
    refine hg.mono_fun' (by fun_prop : Measurable _).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_
    rw [uIoc_of_le ha0.le] at ht
    dsimp only
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle t ht
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_of_le ha0.le, intervalIntegral.integral_of_le ha0.le]
  exact setIntegral_mono_ae_restrict hint.1 hg.1 (ae_restrict_of_forall_mem measurableSet_Ioc hle)

/-- Pointwise squared-norm bound for the radial integrand on `(a, 1]` away from the shifted
logarithmic singularity `s`. -/
private lemma norm_radialIntegrand_sq_le_of_mem_Ioc (k : ℕ) {R a : ℝ} (hR : 1 ≤ R) (ha0 : 0 < a)
    (ha1 : a ≤ 1) {z : ℂ} (hzR : ‖z‖ ≤ R) {t : ℝ} (ht : t ∈ Ioc a 1)
    (hts : t ≠ if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0) :
    ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
      2 * (|Real.log a| ^ k / a) ^ 2 * (Real.log 2 + Real.log (1 + R) + Real.pi) ^ 2 +
        2 * (|Real.log a| ^ k / a) ^ 2 *
          Real.log (t - if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0) ^ 2 := by
  set K₀ : ℝ := |Real.log a| ^ k / a
  set M₁ : ℝ := Real.log 2 + Real.log (1 + R) + Real.pi
  set s : ℝ := if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0
  have ht0 : 0 < t := ha0.trans ht.1
  have hlog_t : |Real.log t| ≤ |Real.log a| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le ht.2), abs_of_nonpos (Real.log_nonpos ha0.le ha1)]
    exact neg_le_neg (Real.log_le_log ha0 ht.1.le)
  have hK : |Real.log t| ^ k / t ≤ K₀ :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hlog_t k) ha0 ht.1.le
  have : 0 ≤ M₁ := add_nonneg (add_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg (by linarith))) Real.pi_pos.le
  have hprod : ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ≤
      K₀ * (M₁ + |Real.log (t - s)|) := by
    rw [norm_radialIntegrand ht0, mul_div_right_comm]
    exact mul_le_mul hK (norm_log_one_sub_ofReal_mul_le_of_norm_le hR hzR ⟨ht0, ht.2⟩ hts)
      (norm_nonneg _) (by positivity)
  have h0 : 0 ≤ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ := norm_nonneg _
  calc ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2
      ≤ (K₀ * (M₁ + |Real.log (t - s)|)) ^ 2 := sq_le_sq' (by linarith) hprod
    _ ≤ 2 * K₀ ^ 2 * M₁ ^ 2 + 2 * K₀ ^ 2 * Real.log (t - s) ^ 2 := by
        have : |Real.log (t - s)| ^ 2 = Real.log (t - s) ^ 2 := sq_abs _
        nlinarith [sq_nonneg (K₀ * (M₁ - |Real.log (t - s)|))]

/-- Uniform `L²` integrability and bound on `[a, 1]` away from `t = 0`. -/
private lemma norm_radialIntegrand_sq_integrable_a_to_one (k : ℕ) {R a : ℝ} (hR : 1 ≤ R)
    (ha0 : 0 < a) (ha1 : a ≤ 1) {z : ℂ} (hzR : ‖z‖ ≤ R) :
    IntervalIntegrable
      (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      volume a 1 ∧
    ∫ t : ℝ in a..1, ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
      2 * (|Real.log a| ^ k / a) ^ 2 * (Real.log 2 + Real.log (1 + R) + Real.pi) ^ 2 +
        2 * (|Real.log a| ^ k / a) ^ 2 * ∫ u : ℝ in (-3 : ℝ)..3, Real.log u ^ 2 := by
  set K₀ : ℝ := |Real.log a| ^ k / a
  set M₁ : ℝ := Real.log 2 + Real.log (1 + R) + Real.pi
  set s : ℝ := if 1 / 2 ≤ ‖z‖ then (z⁻¹).re else 0 with hs_def
  have hs_abs : |s| ≤ 2 := by
    rw [hs_def]; split_ifs with hz
    · exact (Complex.abs_re_le_norm _).trans ((norm_inv z).trans_le
        ((inv_anti₀ (by norm_num) hz).trans_eq (by norm_num)))
    · norm_num
  have hlog_sub : IntervalIntegrable (fun t : ℝ ↦ Real.log (t - s) ^ 2) volume a 1 := by
    simpa only [sub_add_cancel] using
      (intervalIntegrable_log_pow 2 (a := a - s) (b := 1 - s)).comp_sub_right s
  have hg : IntervalIntegrable
      (fun t : ℝ ↦ 2 * K₀ ^ 2 * M₁ ^ 2 + 2 * K₀ ^ 2 * Real.log (t - s) ^ 2) volume a 1 :=
    intervalIntegrable_const.add (hlog_sub.const_mul _)
  have hle : ∀ᵐ t ∂volume.restrict (Ioc a 1),
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
        2 * K₀ ^ 2 * M₁ ^ 2 + 2 * K₀ ^ 2 * Real.log (t - s) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton s))] with t ht hts
    exact norm_radialIntegrand_sq_le_of_mem_Ioc k hR ha0 ha1 hzR ht hts
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      volume a 1 := by
    refine hg.mono_fun' (by fun_prop : Measurable _).aestronglyMeasurable ?_
    rw [uIoc_of_le ha1]
    filter_upwards [hle] with t ht
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨hint, ?_⟩
  have hmono : ∫ t : ℝ in a..1,
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤
      ∫ t : ℝ in a..1, (2 * K₀ ^ 2 * M₁ ^ 2 + 2 * K₀ ^ 2 * Real.log (t - s) ^ 2) := by
    rw [intervalIntegral.integral_of_le ha1, intervalIntegral.integral_of_le ha1]
    exact setIntegral_mono_ae_restrict hint.1 hg.1 hle
  rw [intervalIntegral.integral_add intervalIntegrable_const (hlog_sub.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun u ↦ Real.log u ^ 2) s, smul_eq_mul] at hmono
  have hsub_le : ∫ u : ℝ in a - s..1 - s, Real.log u ^ 2 ≤
      ∫ u : ℝ in (-3 : ℝ)..3, Real.log u ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith [(abs_le.mp hs_abs).2])
      (by linarith) (by linarith [(abs_le.mp hs_abs).1])
      (ae_of_all _ fun _ ↦ sq_nonneg _) (intervalIntegrable_log_pow 2)
  exact hmono.trans (add_le_add (mul_le_of_le_one_left (by positivity) (by linarith))
    (mul_le_mul_of_nonneg_left hsub_le (by positivity)))

/-- Uniform `L²` integrability and bound on `[0, 1]` for `‖z‖ ≤ R`. -/
private lemma norm_radialIntegrand_sq_integrable_and_le (k : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C ≥ 0, ∀ z : ℂ, ‖z‖ ≤ R →
      IntervalIntegrable
        (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
        volume 0 1 ∧
      ∫ t : ℝ in 0..1,
        ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤ C := by
  set a : ℝ := 1 / (2 * (R + 1)) with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one (by positivity)]; linarith
  have haR : a * R ≤ 1 / 2 := by
    rw [ha_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  set C₁ : ℝ := ∫ t : ℝ in 0..a, (3 / 2 * R) ^ 2 * Real.log t ^ (2 * k)
  set C₂ : ℝ := 2 * (|Real.log a| ^ k / a) ^ 2 * (Real.log 2 + Real.log (1 + R) + Real.pi) ^ 2 +
    2 * (|Real.log a| ^ k / a) ^ 2 * ∫ u : ℝ in (-3 : ℝ)..3, Real.log u ^ 2
  refine ⟨max (C₁ + C₂) 0, le_max_right _ _, fun z hzR ↦ ?_⟩
  obtain ⟨hint₁, hval₁⟩ := norm_radialIntegrand_sq_integrable_zero_to_a k ha0 haR hzR
  obtain ⟨hint₂, hval₂⟩ := norm_radialIntegrand_sq_integrable_a_to_one k hR ha0 ha1 hzR
  refine ⟨hint₁.trans hint₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
  exact (add_le_add hval₁ hval₂).trans (le_max_left _ _)

/-- For every `k : ℕ` and `z : ℂ`, the squared norm of the polylogarithm's radial integrand is
interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_norm_radialIntegrand_sq (k : ℕ) (z : ℂ) :
    IntervalIntegrable
      (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)
      volume 0 1 := by
  obtain ⟨_, _, h⟩ := norm_radialIntegrand_sq_integrable_and_le k (le_max_right ‖z‖ 1)
  exact (h z (le_max_left ‖z‖ 1)).1

/-- On any bounded parameter set `B ⊆ ℂ`, the `L²` integrals of the polylogarithm's radial
integrand over `[0, 1]` are uniformly bounded. -/
theorem exists_integral_norm_radialIntegrand_sq_le (k : ℕ) {B : Set ℂ}
    (hB : Bornology.IsBounded B) :
    ∃ C ≥ 0, ∀ z ∈ B,
      ∫ t : ℝ in 0..1,
        ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2 ≤ C := by
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  obtain ⟨C, hC0, hC⟩ := norm_radialIntegrand_sq_integrable_and_le k (le_max_right R 1)
  exact ⟨C, hC0, fun z hz ↦ (hC z ((hR z hz).trans (le_max_left R 1))).2⟩

/-- On any bounded parameter set `B ⊆ ℂ` (including points on the cut `[1, ∞)`), the family of
radial integrands of the weight-`(k + 2)` polylogarithm is uniformly integrable on `(0, 1]`. -/
theorem uniformIntegrable_radialIntegrand (k : ℕ) {B : Set ℂ} (hB : Bornology.IsBounded B) :
    UniformIntegrable
      (fun (z : B) (t : ℝ) ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t)
      1 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  obtain ⟨C, _, hC⟩ := exists_integral_norm_radialIntegrand_sq_le k hB
  have hsuper : Tendsto (fun x : ℝ ↦ x ^ 2 / x) atTop atTop :=
    tendsto_id.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp [sq, mul_div_cancel_right₀ x hx.ne'])
  have hlint : ∀ z : B,
      ∫⁻ t, ENNReal.ofReal
        (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2) ∂μ ≤
        ENNReal.ofReal C := by
    intro z
    have hint : Integrable
        (fun t : ℝ ↦ ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2) μ :=
      (intervalIntegrable_norm_radialIntegrand_sq k z).1
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
      ← intervalIntegral.integral_of_le zero_le_one]
    exact ENNReal.ofReal_le_ofReal (hC z z.2)
  have hunif : UnifIntegrable
      (fun (z : B) (t : ℝ) ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t) 1 μ :=
    unifIntegrable_of_lintegral_ofReal_le hsuper
      (fun _ ↦ (by fun_prop : Measurable _).aestronglyMeasurable) ENNReal.ofReal_ne_top hlint
  refine ⟨hunif, lt_of_le_of_lt (b := μ univ + ENNReal.ofReal C) (iSup_le fun z ↦ ?_)
    (by finiteness)⟩
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t) μ :=
    (by fun_prop : Measurable _).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_eNorm hmeas]
  calc ∫⁻ t, ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ₑ ∂μ
      ≤ ∫⁻ t, (1 + ENNReal.ofReal
          (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2)) ∂μ := by
        refine lintegral_mono fun t ↦ ?_
        rw [← ofReal_norm]
        set x := ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖
        calc ENNReal.ofReal x ≤ ENNReal.ofReal (1 + x ^ 2) :=
              ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - 1)])
          _ = 1 + ENNReal.ofReal (x ^ 2) := by
              rw [ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one]
    _ = μ univ + ∫⁻ t, ENNReal.ofReal
          (‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t‖ ^ 2) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_one]
    _ ≤ μ univ + ENNReal.ofReal C := by gcongr; exact hlint z

/-- **Vitali convergence for the polylogarithm's radial integral.** Along any countably generated
filter `l`, if `φ` is eventually bounded and `Log (1 - t * φ a)` converges almost everywhere on
`(0, 1]` to `L t`, then the radial integrals converge to the corresponding integral of `L`. -/
theorem tendsto_integral_radialIntegrand_of_tendsto_ae {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] (k : ℕ) {φ : α → ℂ} (hφ : ∃ R : ℝ, ∀ᶠ a in l, ‖φ a‖ ≤ R)
    {L : ℝ → ℂ}
    (hL : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun a ↦ Complex.log (1 - (t : ℂ) * φ a)) l (𝓝 (L t))) :
    Tendsto
      (fun a ↦ ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * φ a)) / t)
      l (𝓝 (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-L t) / t)) := by
  rcases eq_or_neBot l with rfl | _
  · exact tendsto_bot
  obtain ⟨R, hR⟩ := hφ
  set B : Set ℂ := Metric.closedBall 0 R
  have hUI := uniformIntegrable_radialIntegrand k (Metric.isBounded_closedBall (x := (0 : ℂ))
    (r := R))
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  set g : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-L t) / t
  refine tendsto_iff_seq_tendsto.2 fun u hu ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hR)
  rw [← tendsto_add_atTop_iff_nat N]
  set zSeq : ℕ → B := fun n ↦
    ⟨φ (u (n + N)), by simpa [B, dist_zero_right] using hN (n + N) (Nat.le_add_left N n)⟩
  set F : ℕ → ℝ → ℂ := fun n t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * (zSeq n : ℂ))) / t
  have hF_UI : UniformIntegrable F 1 μ :=
    ⟨hUI.unifIntegrable.comp zSeq, (iSup_comp_le _ zSeq).trans_lt hUI.iSup_eLpNorm_lt⟩
  have hF_ae : ∀ᵐ t ∂μ, Tendsto (fun n ↦ F n t) atTop (𝓝 (g t)) := by
    filter_upwards [hL] with t ht
    have hlog : Tendsto (fun n ↦ Complex.log (1 - (t : ℂ) * (zSeq n : ℂ))) atTop (𝓝 (L t)) :=
      ht.comp (hu.comp (tendsto_add_atTop_nat N))
    exact (tendsto_const_nhds.mul hlog.neg).div_const (t : ℂ)
  have hg_mem : MemLp g 1 μ := hF_UI.memLp_of_ae_tendsto hF_ae
  have hLp : Tendsto (fun n ↦ eLpNorm (F n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hF_UI.aestronglyMeasurable
      hg_mem hF_UI.unifIntegrable hF_ae
  have hint : ∀ n, Integrable (F n) μ := fun n ↦
    (intervalIntegrable_radialIntegrand k (zSeq n : ℂ)).1
  simpa only [intervalIntegral.integral_of_le zero_le_one, μ, F, zSeq, g, Function.comp_def] using
    tendsto_integral_of_L1' g (Eventually.of_forall hint) hLp

end TauCeti.Polylog
