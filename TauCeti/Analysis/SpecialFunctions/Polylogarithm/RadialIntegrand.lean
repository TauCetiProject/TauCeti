/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Analysis.SpecialFunctions.Integrability.Log

/-!
# Integrability of the polylogarithm's radial integrand

For `k : ℕ` and `z : ℂ`, the polylogarithm of weight `k + 2` is the logarithmic radial integral
`Li_{k+2}(z) = (1 / k!) ∫₀¹ (-log t) ^ k * (-Log (1 - t z)) / t dt`, where `Log` is Mathlib's
principal complex logarithm. This file proves that the integrand is interval integrable on
`[0, 1]` for **every** complex `z`, and that on a compact subset of the principal domain
`ℂ ∖ [1, ∞) = {z | 1 - z ∈ slitPlane}` it has a single integrable majorant `C * |log t| ^ k`.

Near `t = 0` the factor `-Log (1 - t z)` is `O(t z)`, so the integrand is dominated by a multiple
of `|log t| ^ k`. Away from `t = 0` the factor `(-log t) ^ k / t` is continuous, and
`Log (1 - t z)` is integrable even when `1 - t z` vanishes on `[0, 1]` (for real `z ≥ 1`): its
real part has a logarithmic singularity and its imaginary part is bounded by `π`. On a compact
subset of the principal domain, `1 - t z` stays uniformly away from zero for `t ∈ [0, 1]`; this
gives the uniform majorant of the integrand, and the same lower bound controls its derivative
`(-log t) ^ k / (1 - t z)` in `z`.

## Main declarations

* `TauCeti.Polylog.intervalIntegrable_radialIntegrand`: interval integrability on `[0, 1]` for
  every `z`.
* `TauCeti.Polylog.exists_le_norm_one_sub_ofReal_mul`: on a compact subset of the principal
  domain, `‖1 - t z‖` is bounded below by a positive constant for `t ∈ [0, 1]`.
* `TauCeti.Polylog.exists_norm_radialIntegrand_le`: the uniform majorant `C * |log t| ^ k` on a
  compact subset of the principal domain.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (3), p. 50, and §1.4, p. 51.
-/

public section

open MeasureTheory Set

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

end TauCeti.Polylog
