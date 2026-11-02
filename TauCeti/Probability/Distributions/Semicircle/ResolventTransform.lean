/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
public import TauCeti.Probability.Distributions.Semicircle.Moments
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.SpecificLimits.Catalan

/-!
# The resolvent transform of the semicircle law

For the semicircle law `semicircleReal a v` with centre `a` and variance `v`, the resolvent
transform `m(z) = ∫ (x - z)⁻¹ d(semicircleReal a v)(x)` (Mathlib's
`MeasureTheory.resolventTransform` with base field `ℝ`, values in `ℂ`) satisfies the quadratic
equation

`v * (m(z) * m(z)) + (z - a) * m(z) + 1 = 0`

at every `z` off the support `[a - 2√v, a + 2√v]`. For the standard law `semicircleReal 0 1` this
is `m² + z m + 1 = 0`. In the upper half-plane `m(z)` is the unique root with positive imaginary
part: for `v > 0` the other root `1 / (v m(z))` has negative imaginary part, and for zero variance
the equation is linear, with `m(z) = 1 / (a - z)` its only root. This is the self-consistent
equation that the resolvent method for Wigner matrices identifies in the limit; the sign of the
imaginary part selects the root without a pointwise choice of complex square root. The quadratic
is written as `v * (m * m) + (z - a) * m + 1`, the shape used by Mathlib's `discrim` API.

## Main results

* `TauCeti.Probability.hasSum_resolventTransform_semicircleReal`: the expansion of `m` at infinity,
  `m(z) = -∑ₙ vⁿ Cₙ (z - a)^(-(2n+1))` for `|z - a| > 2√v`, whose coefficients are the
  Catalan moments.
* `TauCeti.Probability.resolventTransform_semicircleReal_quadratic_eq_zero`: the quadratic
  equation off the support.
* `TauCeti.Probability.eq_resolventTransform_semicircleReal_iff`: in the upper half-plane, `m(z)`
  is the only root of the quadratic with positive imaginary part.
* `TauCeti.Probability.resolventTransform_semicircleReal_zero_one_I`: for the standard law,
  `m(i) = i (√5 - 1) / 2`.

## Implementation notes

Outside the disc `|z - a| ≤ 2√v` the transform is the integral of a geometric series, and the
quadratic equation is the quadratic equation of the Catalan generating function. The transform is
analytic off the support, so the identity theorem on each half-plane, which meets the exterior of
the disc, extends the equation to every non-real `z`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter
open scoped NNReal Topology

namespace TauCeti.Probability

variable {a : ℝ} {v : ℝ≥0} {z : ℂ}

/-- Outside the disc `|z - a| ≤ 2√v`, the resolvent transform of `semicircleReal a v` is the
Laurent series `-∑ₙ vⁿ Cₙ (z - a)^(-(2n+1))` whose coefficients are the even central moments. -/
theorem hasSum_resolventTransform_semicircleReal (hz : 2 * √(v : ℝ) < ‖z - a‖) :
    HasSum (fun n ↦ -((v : ℂ) ^ n * catalan n) * (z - a)⁻¹ ^ (2 * n + 1))
      (resolventTransform (semicircleReal a v) z) := by
  have hnorm : ∀ᵐ x : ℝ ∂semicircleReal a v, ‖(x : ℂ) - a‖ ≤ 2 * √(v : ℝ) := by
    filter_upwards [ae_mem_Icc_semicircleReal a v] with x hx
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2]
  have hint := hasSum_resolventTransform_of_ae_norm_le hnorm hz
  -- Compute each term from the central moments; the odd ones vanish.
  have hterm (n : ℕ) : -(∫ x, ((x : ℂ) - a) ^ n ∂semicircleReal a v) * (z - a)⁻¹ ^ (n + 1) =
      -((∫ x, (x - a) ^ n ∂semicircleReal a v : ℝ) : ℂ) * (z - a)⁻¹ ^ (n + 1) := by
    simp only [← integral_complex_ofReal, ofReal_pow, ofReal_sub]
  simp only [hterm] at hint
  refine ((Function.Injective.hasSum_iff (g := fun n ↦ 2 * n)
    (fun _ _ h ↦ by simpa using h) fun n hn ↦ ?_).2 hint).congr_fun fun n ↦ ?_
  · obtain ⟨k, rfl⟩ := (Nat.even_or_odd n).resolve_left fun ⟨k, hk⟩ ↦ hn ⟨k, by dsimp only; omega⟩
    simp
  · simp

/-- The quadratic equation outside the disc `|z - a| ≤ 2√v`, from the Catalan generating
function. -/
private lemma quadratic_eq_zero_of_lt_norm (hz : 2 * √(v : ℝ) < ‖z - a‖) :
    (v : ℂ) * (resolventTransform (semicircleReal a v) z *
      resolventTransform (semicircleReal a v) z) +
      (z - a) * resolventTransform (semicircleReal a v) z + 1 = 0 := by
  set w := z - a
  set q := (v : ℂ) * w⁻¹ ^ 2 with hqdef
  have hw : w ≠ 0 := norm_pos_iff.1 ((by positivity : 0 ≤ 2 * √(v : ℝ)).trans_lt hz)
  have hq : ‖q‖ < 4⁻¹ := by
    have h4 : 4 * (v : ℝ) < ‖w‖ ^ 2 := by
      have := pow_lt_pow_left₀ hz (by positivity) two_ne_zero
      rw [mul_pow, Real.sq_sqrt v.coe_nonneg] at this
      linarith
    have hqn : ‖q‖ = v / ‖w‖ ^ 2 := by simp [q, div_eq_mul_inv]
    rw [hqn, div_lt_iff₀ (by positivity)]
    linarith
  set c := ∑' n, (catalan n : ℂ) * q ^ n
  have hm : resolventTransform (semicircleReal a v) z = -w⁻¹ * c := by
    refine (hasSum_resolventTransform_semicircleReal hz).unique ?_
    convert ((Summable.of_norm (summable_norm_catalan_mul_pow hq)).hasSum.mul_left (-w⁻¹))
      using 2 with n
    simp only [q]
    ring
  have hc : c ^ 2 * q + 1 = c := tsum_catalan_mul_pow_sq_mul_add_one hq
  rw [hqdef] at hc
  have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [hm]
  linear_combination hc - c * hww

/-- The quadratic equation propagates by analytic continuation through an open convex set of
non-real points which meets the exterior of the disc `|z - a| ≤ 2√v`. -/
private lemma quadratic_eq_zero_of_convex {H : Set ℂ} (hHo : IsOpen H) (hHc : Convex ℝ H)
    (hHim : ∀ z ∈ H, z.im ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ H) (hR₀ : 2 * √(v : ℝ) < ‖z₀ - a‖)
    (hz : z ∈ H) :
    (v : ℂ) * (resolventTransform (semicircleReal a v) z *
      resolventTransform (semicircleReal a v) z) +
      (z - a) * resolventTransform (semicircleReal a v) z + 1 = 0 := by
  have hHU : H ⊆ (algebraMap ℝ ℂ '' (semicircleReal a v).support)ᶜ := by
    rintro z hz ⟨x, -, rfl⟩
    exact hHim _ hz (by simp)
  have hm : AnalyticOnNhd ℂ (resolventTransform (semicircleReal a v) : ℂ → ℂ) H :=
    hHo.analyticOn_iff_analyticOnNhd.1 (analyticOn_resolventTransform.mono hHU)
  have hext : {z : ℂ | 2 * √(v : ℝ) < ‖z - a‖} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hR₀
  simpa using ((analyticOnNhd_const.mul (hm.mul hm)).add
    ((analyticOnNhd_id.sub analyticOnNhd_const).mul hm) |>.add analyticOnNhd_const)
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHc.isPreconnected hz₀
      (Filter.eventually_of_mem hext fun _ ↦ quadratic_eq_zero_of_lt_norm) hz

/-- The point `a + t i` lies outside the disc `|z - a| ≤ 2√v` when `2√v < |t|`. -/
private lemma lt_norm_mk_sub {t : ℝ} (ht : 2 * √(v : ℝ) < |t|) :
    2 * √(v : ℝ) < ‖(⟨a, t⟩ : ℂ) - a‖ := by
  simpa [mk_eq_add_mul_I] using ht

/-- The resolvent transform `m` of `semicircleReal a v` satisfies
`v * (m * m) + (z - a) * m + 1 = 0` off the support `[a - 2√v, a + 2√v]`; for the standard law
this is `m² + z m + 1 = 0`. -/
theorem resolventTransform_semicircleReal_quadratic_eq_zero
    (hz : z ∉ ((↑) : ℝ → ℂ) '' Icc (a - 2 * √(v : ℝ)) (a + 2 * √(v : ℝ))) :
    (v : ℂ) * (resolventTransform (semicircleReal a v) z *
      resolventTransform (semicircleReal a v) z) +
      (z - a) * resolventTransform (semicircleReal a v) z + 1 = 0 := by
  set R := 2 * √(v : ℝ)
  by_cases hzR : R < ‖z - a‖
  · exact quadratic_eq_zero_of_lt_norm hzR
  -- A point inside the disc is not real, so it lies in a half-plane meeting the exterior.
  have hR0 : 0 ≤ R := by positivity
  rcases lt_trichotomy z.im 0 with him | him | him
  · refine quadratic_eq_zero_of_convex (isOpen_lt continuous_im continuous_const)
      (convex_halfSpace_im_lt 0) (fun _ h ↦ h.ne) (z₀ := ⟨a, -(R + 1)⟩)
      (show -(R + 1) < (0 : ℝ) by linarith) (lt_norm_mk_sub (lt_abs.2 (.inr (by linarith)))) him
  · refine absurd ⟨z.re, ?_, Complex.ext rfl (by simp [him])⟩ hz
    have h := abs_le.1 ((abs_re_le_norm (z - a)).trans (not_lt.1 hzR))
    simp only [sub_re, ofReal_re] at h
    constructor <;> linarith [h.1, h.2]
  · refine quadratic_eq_zero_of_convex (isOpen_lt continuous_const continuous_im)
      (convex_halfSpace_im_gt 0) (fun _ h ↦ h.ne') (z₀ := ⟨a, R + 1⟩)
      (show (0 : ℝ) < R + 1 by linarith) (lt_norm_mk_sub (lt_abs.2 (.inl (by linarith)))) him

/-- In the upper half-plane, the resolvent transform of `semicircleReal a v` is the unique root of
`v * (w * w) + (z - a) * w + 1 = 0` with positive imaginary part. -/
theorem eq_resolventTransform_semicircleReal_iff (hz : 0 < z.im) {w : ℂ} :
    w = resolventTransform (semicircleReal a v) z ↔
      0 < w.im ∧ (v : ℂ) * (w * w) + (z - a) * w + 1 = 0 := by
  set m := resolventTransform (semicircleReal a v) z
  have hzU : z ∉ ((↑) : ℝ → ℂ) '' Icc (a - 2 * √(v : ℝ)) (a + 2 * √(v : ℝ)) := by
    rintro ⟨x, -, rfl⟩
    simp at hz
  have hm : (v : ℂ) * (m * m) + (z - a) * m + 1 = 0 :=
    resolventTransform_semicircleReal_quadratic_eq_zero hzU
  have hmim : 0 < m.im := im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz
  refine ⟨fun h ↦ h ▸ ⟨hmim, hm⟩, fun ⟨hwim, hw⟩ ↦ ?_⟩
  by_contra hne
  -- The other root `w` satisfies `w * (v * m) = 1`, so its imaginary part is not positive.
  have hprod : w * ((v : ℂ) * m) = 1 := by
    have h : (w - m) * ((v : ℂ) * (w + m) + (z - a)) = 0 := by linear_combination hw - hm
    have h' := (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)
    linear_combination m * h' - hm
  have hinv : w = ((v : ℂ) * m)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have : w.im ≤ 0 := by
    rw [hinv, inv_im, im_ofReal_mul]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (mul_nonneg v.coe_nonneg hmim.le))
      (normSq_nonneg _)
  linarith

/-- The transform of the standard semicircle law at `i` is `i (√5 - 1) / 2`, the root of
`m² + i m + 1 = 0` with positive imaginary part; the other root is `-i (√5 + 1) / 2`. -/
theorem resolventTransform_semicircleReal_zero_one_I :
    resolventTransform (semicircleReal 0 1) I = ((√5 - 1) / 2 : ℝ) * I := by
  have h5 : (1 : ℝ) < √5 := (Real.lt_sqrt zero_le_one).2 (by norm_num)
  have h5c : ((√5 : ℝ) : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  refine ((eq_resolventTransform_semicircleReal_iff (by simp)).2
    ⟨by rw [mul_I_im, ofReal_re]; linarith, ?_⟩).symm
  push_cast
  linear_combination (-1 / 4 : ℂ) * h5c + (((√5 : ℂ) - 1) / 2 * (((√5 : ℂ) - 1) / 2) +
    ((√5 : ℂ) - 1) / 2) * I_sq

end TauCeti.Probability
