/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
public import TauCeti.Probability.Distributions.Semicircle.Moments
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import TauCeti.Basic.Complex.OfRealSub
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
* `TauCeti.Probability.tendsto_resolventTransform_semicircleReal_boundary`: the complex boundary
  value on the support of a positive-variance semicircle law.

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

/-- On the positive imaginary axis through its centre, the semicircle resolvent has zero real
part and its imaginary part satisfies the quadratic equation. -/
theorem re_eq_zero_and_sq_im_add_mul_eq_one_resolventTransform_semicircleReal_mul_I
    (a t : ℝ) (v : ℝ≥0) (ht : 0 < t) :
    (resolventTransform (semicircleReal a v) ((a : ℂ) + t * Complex.I)).re = 0 ∧
      (v : ℝ) * (resolventTransform (semicircleReal a v)
        ((a : ℂ) + t * Complex.I)).im ^ 2 +
        t * (resolventTransform (semicircleReal a v)
          ((a : ℂ) + t * Complex.I)).im = 1 := by
  set z : ℂ := (a : ℂ) + t * Complex.I
  have hz : 0 < z.im := by simp [z, ht]
  have hznot : z ∉ ((↑) : ℝ → ℂ) '' Icc (a - 2 * √(v : ℝ)) (a + 2 * √(v : ℝ)) :=
    Complex.notMem_image_ofReal_of_im_ne_zero hz.ne'
  have hquad := resolventTransform_semicircleReal_quadratic_eq_zero
    (a := a) (v := v) (z := z) hznot
  let m := resolventTransform (semicircleReal a v) z
  let b := m.im
  have hquad' : (v : ℂ) * (m * m) + (z - a) * m + 1 = 0 := by
    simpa [m] using hquad
  have hb : 0 < b :=
    im_resolventTransform_pos (μ := semicircleReal a v) (IsProbabilityMeasure.ne_zero _) hz
  have hmval : m = (m.re : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [b]
  have him := congrArg Complex.im hquad'
  have hre := congrArg Complex.re hquad'
  have hzval : z = (a : ℂ) + t * Complex.I := rfl
  rw [hzval, hmval] at him hre
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.add_re,
    Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    mul_zero, sub_zero, add_zero, one_re, one_im, zero_im] at him hre
  have hmre : m.re = 0 := by
    have hfactor : 0 < 2 * (v : ℝ) * b + t := by positivity
    nlinarith
  constructor
  · simp [z, m, hmre]
  · simp [z, m, hmre] at hre
    nlinarith

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

private def standardSemicircleResolvent (z : ℂ) : ℂ :=
  resolventTransform (semicircleReal 0 1) z

private theorem standardSemicircleResolvent_quad (hz : 0 < z.im) :
    standardSemicircleResolvent z * standardSemicircleResolvent z +
      z * standardSemicircleResolvent z + 1 = 0 := by
  have h := resolventTransform_semicircleReal_quadratic_eq_zero (a := 0) (v := 1) (z := z) (by
    rintro ⟨x, -, hx⟩
    have h : z.im = 0 := by rw [← hx]; simp
    linarith)
  simpa [standardSemicircleResolvent] using h

private theorem standardSemicircleResolvent_im_pos (hz : 0 < z.im) :
    0 < (standardSemicircleResolvent z).im :=
  im_resolventTransform_pos (μ := semicircleReal 0 1) (IsProbabilityMeasure.ne_zero _) hz

private def standardSemicircleResolventAt (x ε : ℝ) : ℂ :=
  standardSemicircleResolvent ((x : ℂ) + (ε : ℂ) * Complex.I)

private def standardSemicircleResolventNormSq (x ε : ℝ) : ℝ :=
  Complex.normSq (standardSemicircleResolventAt x ε)

private theorem standard_boundary_identities (x ε : ℝ) (hε : 0 < ε) :
    (standardSemicircleResolventAt x ε).re * (standardSemicircleResolventNormSq x ε + 1) =
        -x * standardSemicircleResolventNormSq x ε ∧
      (standardSemicircleResolventAt x ε).im * (1 - standardSemicircleResolventNormSq x ε) =
        ε * standardSemicircleResolventNormSq x ε := by
  let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
  let a : ℝ := (standardSemicircleResolvent z).re
  let b : ℝ := (standardSemicircleResolvent z).im
  let q : ℝ := a ^ 2 + b ^ 2
  have hz : 0 < z.im := by simp [z, hε]
  have hmval : standardSemicircleResolvent z = (a : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [a, b]
    · simp [a, b]
  let c : ℂ := star (standardSemicircleResolvent z)
  have hmc : standardSemicircleResolvent z * c = (q : ℂ) := by
    dsimp only [c]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_apply]
    simp [a, b, q]
    ring
  have hmul := congrArg (fun w : ℂ ↦ w * c) (standardSemicircleResolvent_quad hz)
  have hrelmul : (q : ℂ) * standardSemicircleResolvent z + z * (q : ℂ) + c =
      (standardSemicircleResolvent z * standardSemicircleResolvent z +
        z * standardSemicircleResolvent z + 1) * c := by
    rw [← hmc]
    ring
  have hrel : (q : ℂ) * standardSemicircleResolvent z + z * (q : ℂ) + c = 0 := by
    rw [hrelmul]
    simpa using hmul
  rw [hmval] at hrel
  have hreal : q * a + x * q + a = 0 := by
    have h := congrArg Complex.re hrel
    simp [z, c, q, hmval, Complex.add_re, Complex.mul_re, Complex.mul_im] at h
    norm_cast at h
    nlinarith
  have himag : q * b + ε * q - b = 0 := by
    have h := congrArg Complex.im hrel
    simp [z, c, q, hmval, Complex.add_im, Complex.mul_re, Complex.mul_im] at h
    norm_cast at h
    nlinarith
  have hq : standardSemicircleResolventNormSq x ε = q := by
    change Complex.normSq (standardSemicircleResolventAt x ε) = q
    rw [Complex.normSq_apply]
    dsimp [q, a, b, z, standardSemicircleResolventAt, standardSemicircleResolvent]
    ring
  have hresult : a * (q + 1) = -x * q ∧ b * (1 - q) = ε * q := by
    constructor <;> nlinarith [hreal, himag]
  constructor
  · simpa [standardSemicircleResolventAt, standardSemicircleResolventNormSq,
      standardSemicircleResolvent, a, b, z, ← hq] using hresult.1
  · simpa [standardSemicircleResolventAt, standardSemicircleResolventNormSq,
      standardSemicircleResolvent, a, b, z, ← hq] using hresult.2

private theorem standard_boundary_normSq_lt_one {x ε : ℝ} (hε : 0 < ε) :
    standardSemicircleResolventNormSq x ε < 1 := by
  let b : ℝ := (standardSemicircleResolventAt x ε).im
  let q : ℝ := standardSemicircleResolventNormSq x ε
  have hids := standard_boundary_identities x ε hε
  have himag : b * (1 - q) = ε * q := by simpa [b, q] using hids.2
  have hb : 0 < b := by
    simpa [b, standardSemicircleResolventAt] using
      standardSemicircleResolvent_im_pos (by simpa [standardSemicircleResolventAt] using hε)
  have hq : 0 < q := by
    rw [show q = Complex.normSq (standardSemicircleResolventAt x ε) by rfl,
      Complex.normSq_apply]
    have hb2 : 0 < (standardSemicircleResolventAt x ε).im ^ 2 := sq_pos_of_pos hb
    nlinarith [sq_nonneg (standardSemicircleResolventAt x ε).re]
  by_contra h
  have hle : 1 - q ≤ 0 := by linarith
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hb.le hle
  have hpos : 0 < ε * q := mul_pos hε hq
  rw [himag] at hnonpos
  linarith

private theorem standard_boundary_normSq_bound_of_mem_Icc {x ε : ℝ}
    (hx : x ∈ Icc (-2) 2) (hε : 0 < ε) :
    (1 - standardSemicircleResolventNormSq x ε) ^ 2 ≤ 2 * ε := by
  let a : ℝ := (standardSemicircleResolventAt x ε).re
  let b : ℝ := (standardSemicircleResolventAt x ε).im
  let q : ℝ := standardSemicircleResolventNormSq x ε
  have hids := standard_boundary_identities x ε hε
  have hreal : a * (q + 1) = -x * q := by simpa [a, q] using hids.1
  have himag : b * (1 - q) = ε * q := by simpa [b, q] using hids.2
  have hb : 0 < b := by
    simpa [b, standardSemicircleResolventAt] using
      standardSemicircleResolvent_im_pos (by simpa [standardSemicircleResolventAt] using hε)
  have hqdef : q = a ^ 2 + b ^ 2 := by
    rw [show q = Complex.normSq (standardSemicircleResolventAt x ε) by rfl,
      Complex.normSq_apply]
    simp [a, b]
    ring
  have hq : 0 < q := by rw [hqdef]; positivity
  have hq_lt : q < 1 := by
    have := standard_boundary_normSq_lt_one (x := x) hε
    simpa [q] using this
  have hx2 : x ^ 2 ≤ 4 := by
    have hxleft : 0 ≤ 2 + x := by linarith [hx.1]
    have hxright : 0 ≤ 2 - x := by linarith [hx.2]
    nlinarith [mul_nonneg hxleft hxright]
  have hreal_sq : a ^ 2 * (q + 1) ^ 2 = x ^ 2 * q ^ 2 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) hreal
    nlinarith [h]
  have hfactor :
      b ^ 2 * (q + 1) ^ 2 = q * ((q + 1) ^ 2 - x ^ 2 * q) := by
    nlinarith [hreal_sq, hqdef]
  have hfactor_le : (1 - q) ^ 2 ≤ (q + 1) ^ 2 - x ^ 2 * q := by
    have h4x : 0 ≤ 4 - x ^ 2 := by linarith
    nlinarith [mul_nonneg (le_of_lt hq) h4x]
  have hbound_b : q * (1 - q) ^ 2 ≤ b ^ 2 * (q + 1) ^ 2 := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hfactor_le hq.le
  have himag_sq : b ^ 2 * (1 - q) ^ 2 = ε ^ 2 * q ^ 2 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) himag
    nlinarith [h]
  have hfour : (1 - q) ^ 4 ≤ ε ^ 2 * q * (q + 1) ^ 2 := by
    apply le_of_mul_le_mul_left ?_ hq
    calc
      q * (1 - q) ^ 4 ≤ b ^ 2 * (q + 1) ^ 2 * (1 - q) ^ 2 := by
        calc
          q * (1 - q) ^ 4 = (q * (1 - q) ^ 2) * (1 - q) ^ 2 := by ring
          _ ≤ (b ^ 2 * (q + 1) ^ 2) * (1 - q) ^ 2 :=
            mul_le_mul_of_nonneg_right hbound_b (sq_nonneg _)
          _ = b ^ 2 * (q + 1) ^ 2 * (1 - q) ^ 2 := by ring
      _ = (b ^ 2 * (1 - q) ^ 2) * (q + 1) ^ 2 := by ring
      _ = (ε ^ 2 * q ^ 2) * (q + 1) ^ 2 := by rw [himag_sq]
      _ = q * (ε ^ 2 * q * (q + 1) ^ 2) := by ring
  have hprod : q * (q + 1) ^ 2 ≤ 4 := by nlinarith [hq.le, hq_lt.le]
  have hfour' : (1 - q) ^ 4 ≤ (2 * ε) ^ 2 := by
    calc
      (1 - q) ^ 4 ≤ ε ^ 2 * (q * (q + 1) ^ 2) := by nlinarith [hfour]
      _ ≤ ε ^ 2 * 4 := mul_le_mul_of_nonneg_left hprod (sq_nonneg ε)
      _ = (2 * ε) ^ 2 := by ring
  have hfour'' : ((1 - q) ^ 2) ^ 2 ≤ (2 * ε) ^ 2 := by
    convert hfour' using 1
    ring
  exact (sq_le_sq₀ (sq_nonneg (1 - q)) (by positivity)).1 hfour''

private theorem tendsto_standard_resolvent_normSq_of_mem_Icc {x : ℝ}
    (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ standardSemicircleResolventNormSq x ε) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · have hδ : 0 < 1 - c := sub_pos.mpr hc
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0 : ℝ) < (1 - c) ^ 2 / 2 from
          div_pos (sq_pos_of_pos hδ) (by norm_num)))]
      with ε hε hεsmall
    let q : ℝ := standardSemicircleResolventNormSq x ε
    have hqpos : 0 < 1 - q := by
      have h := standard_boundary_normSq_lt_one (x := x) hε
      simpa [q] using sub_pos.mpr h
    have hqbound : (1 - q) ^ 2 ≤ 2 * ε := by
      simpa [q] using standard_boundary_normSq_bound_of_mem_Icc hx hε
    simp only [Set.mem_Iio] at hεsmall
    have hεsq : 2 * ε < (1 - c) ^ 2 := by linarith
    have hsq : (1 - q) ^ 2 < (1 - c) ^ 2 := lt_of_le_of_lt hqbound hεsq
    have hdelta : 1 - q < 1 - c := by
      by_contra hn
      have hle : 1 - c ≤ 1 - q := le_of_not_gt hn
      have hsquare : (1 - c) ^ 2 ≤ (1 - q) ^ 2 := by
        have hsum : 0 ≤ (1 - q) + (1 - c) := by linarith [hqpos]
        nlinarith [mul_nonneg (sub_nonneg.mpr hle) hsum]
      linarith [hsq]
    have hqgt : c < q := by linarith
    simpa [q] using hqgt
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    let q : ℝ := standardSemicircleResolventNormSq x ε
    have hqbound : q < 1 := by
      simpa [q] using standard_boundary_normSq_lt_one (x := x) hε
    have hc1 : 1 < c := by linarith
    have : q < c := hqbound.trans hc1
    simpa [q] using this

/-- The real part of the standard semicircle resolvent tends to `-x / 2` on its support. -/
private theorem tendsto_standard_resolvent_re_of_mem_Icc {x : ℝ}
    (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ (standardSemicircleResolventAt x ε).re)
      (𝓝[>] 0) (𝓝 (-x / 2)) := by
  let Q : ℝ → ℝ := fun ε ↦ standardSemicircleResolventNormSq x ε
  let A : ℝ → ℝ := fun ε ↦ (standardSemicircleResolventAt x ε).re
  let F : ℝ → ℝ := fun t ↦ -x * t / (t + 1)
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 1) := tendsto_standard_resolvent_normSq_of_mem_Icc hx
  have hcont : ContinuousAt F 1 := by
    fun_prop (disch := norm_num)
  have hF := hcont.tendsto.comp hQ
  have hEq : ∀ᶠ ε : ℝ in 𝓝[>] 0, A ε = F (Q ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let a : ℝ := (standardSemicircleResolventAt x ε).re
    let q : ℝ := standardSemicircleResolventNormSq x ε
    have hids := standard_boundary_identities x ε hε
    have hreal : a * (q + 1) = -x * q := by simpa [a, q] using hids.1
    have hqnonneg : 0 ≤ q := by
      dsimp [q, standardSemicircleResolventNormSq]
      exact Complex.normSq_nonneg _
    have hformula : a = -x * q / (q + 1) := by
      have hqp : q + 1 ≠ 0 := by linarith
      field_simp [hqp]
      nlinarith [hreal]
    simpa [A, F, Q, a, q, standardSemicircleResolventAt] using hformula
  have hA := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hF
  have hF1 : F 1 = -x / 2 := by dsimp [F]; ring
  rw [← hF1]
  simpa [A] using hA

/-- The imaginary part of the standard semicircle resolvent tends to its boundary value on the
support. -/
private theorem tendsto_standard_resolvent_im_of_mem_Icc {x : ℝ}
    (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ (standardSemicircleResolventAt x ε).im)
      (𝓝[>] 0) (𝓝 (Real.sqrt (1 - x ^ 2 / 4))) := by
  let Q : ℝ → ℝ := fun ε ↦ standardSemicircleResolventNormSq x ε
  let A : ℝ → ℝ := fun ε ↦ (standardSemicircleResolventAt x ε).re
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 1) :=
    tendsto_standard_resolvent_normSq_of_mem_Icc hx
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (-x / 2)) :=
    tendsto_standard_resolvent_re_of_mem_Icc hx
  have hsq : Tendsto (fun ε : ℝ ↦ Q ε - A ε ^ 2) (𝓝[>] 0)
      (𝓝 (1 - x ^ 2 / 4)) := by
    convert hQ.sub (hA.mul hA) using 1 <;> ring_nf
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hEq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (standardSemicircleResolventAt x ε).im = Real.sqrt (Q ε - A ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let a : ℝ := (standardSemicircleResolventAt x ε).re
    let b : ℝ := (standardSemicircleResolventAt x ε).im
    let q : ℝ := standardSemicircleResolventNormSq x ε
    have hids := standard_boundary_identities x ε hε
    have hb : 0 < b := by
      simpa [b, standardSemicircleResolventAt] using
        standardSemicircleResolvent_im_pos
          (by simpa [standardSemicircleResolventAt] using hε)
    have hq : q = a ^ 2 + b ^ 2 := by
      rw [show q = Complex.normSq (standardSemicircleResolventAt x ε) by rfl,
        Complex.normSq_apply]
      simp [a, b]
      ring
    have hEq' : b = Real.sqrt (q - a ^ 2) := by
      rw [show q - a ^ 2 = b ^ 2 by nlinarith [hq],
        Real.sqrt_sq_eq_abs, abs_of_pos hb]
    simpa [A, Q, a, b, q] using hEq'
  exact Filter.Tendsto.congr' (EventuallyEq.symm hEq) hroot

/-- On `[-2, 2]`, the standard semicircle resolvent has boundary value
`-x / 2 + i √(1 - x² / 4)` when approached from the upper half-plane. -/
theorem tendsto_resolventTransform_semicircleReal_zero_one_boundary {x : ℝ}
    (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦ resolventTransform (semicircleReal 0 1)
        ((x : ℂ) + (ε : ℂ) * Complex.I))
      (𝓝[>] 0)
      (𝓝 (((-x / 2 : ℝ) : ℂ) + (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I)) := by
  have hRe := tendsto_standard_resolvent_re_of_mem_Icc hx
  have hIm := tendsto_standard_resolvent_im_of_mem_Icc hx
  have hpair : Tendsto (fun ε : ℝ ↦
      ((standardSemicircleResolventAt x ε).re, (standardSemicircleResolventAt x ε).im))
      (𝓝[>] 0) (𝓝 (-x / 2, Real.sqrt (1 - x ^ 2 / 4))) := by
    simpa [nhds_prod_eq] using hRe.prodMk hIm
  have hcomplex : Tendsto
      (fun ε : ℝ ↦ Complex.equivRealProdCLM (standardSemicircleResolventAt x ε))
      (𝓝[>] 0)
      (𝓝 ((-x / 2, Real.sqrt (1 - x ^ 2 / 4)) : ℝ × ℝ)) := by
    simpa [standardSemicircleResolventAt] using hpair
  have h := Complex.equivRealProdCLM.symm.continuous.continuousAt.tendsto.comp hcomplex
  have hEq : (fun ε : ℝ ↦
      Complex.equivRealProdCLM.symm
        (Complex.equivRealProdCLM (standardSemicircleResolventAt x ε))) =
      fun ε ↦ standardSemicircleResolventAt x ε := by
    funext ε
    exact Complex.equivRealProdCLM.symm_apply_apply _
  have h' := Filter.Tendsto.congr' (EventuallyEq.symm (Filter.EventuallyEq.of_eq hEq)) h
  simpa [Complex.equivRealProdCLM_symm_apply, standardSemicircleResolventAt,
    standardSemicircleResolvent] using h'

/-- On the support of a positive-variance semicircle law, the resolvent transform has the
boundary value obtained from the standard semicircle law by affine transport. -/
theorem tendsto_resolventTransform_semicircleReal_boundary {a x : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hx : x ∈ Icc (a - 2 * Real.sqrt v) (a + 2 * Real.sqrt v)) :
    Tendsto
      (fun ε : ℝ ↦ resolventTransform (semicircleReal a v)
        ((x : ℂ) + (ε : ℂ) * Complex.I))
      (𝓝[>] 0)
      (𝓝 (((Real.sqrt v : ℂ)⁻¹) *
        (((-((x - a) / Real.sqrt v) / 2 : ℝ) : ℂ) +
          (Real.sqrt (1 - ((x - a) / Real.sqrt v) ^ 2 / 4) : ℂ) * Complex.I))) := by
  let s : ℝ := Real.sqrt v
  let x₀ : ℝ := (x - a) / s
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hs2 : s ^ 2 = v := by
    dsimp [s]
    exact Real.sq_sqrt v.coe_nonneg
  have hvar : Real.toNNReal (s ^ 2) * (1 : ℝ≥0) = v := by
    apply NNReal.coe_injective
    simp [hs2]
  have hmap : (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
      semicircleReal a v := by
    calc
      (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
          semicircleReal (a + s * 0) (Real.toNNReal (s ^ 2) * 1) :=
        map_affine_semicircleReal 0 a s 1
      _ = semicircleReal a v := by simp [hvar]
  have hx₀ : x₀ ∈ Icc (-2) 2 := by
    constructor
    · apply (le_div_iff₀ hs).2
      dsimp [x₀, s]
      nlinarith [hx.1]
    · apply (div_le_iff₀ hs).2
      dsimp [x₀, s]
      nlinarith [hx.2]
  have hId : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hscale0 : Tendsto (fun ε : ℝ ↦ ε / s) (𝓝[>] 0) (𝓝 0) :=
    by simpa using hId.div_const s
  have hscale_pos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε / s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hs
  have hscale : Tendsto (fun ε : ℝ ↦ ε / s) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hscale0, hscale_pos⟩
  have hstd := (tendsto_resolventTransform_semicircleReal_zero_one_boundary hx₀).comp hscale
  have hmul := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ (s : ℂ)⁻¹) (𝓝[>] 0) (𝓝 ((s : ℂ)⁻¹))).mul hstd
  have hmul' : Tendsto
      (fun ε : ℝ ↦ (s : ℂ)⁻¹ *
        resolventTransform (semicircleReal 0 1)
          ((x₀ : ℂ) + ((ε : ℂ) / (s : ℂ)) * Complex.I))
      (𝓝[>] 0)
      (𝓝 ((s : ℂ)⁻¹ *
        (((-x₀ / 2 : ℝ) : ℂ) + (Real.sqrt (1 - x₀ ^ 2 / 4) : ℂ) * Complex.I))) := by
    simpa only [Function.comp_apply, Complex.ofReal_div] using hmul
  have harg (ε : ℝ) :
      (((x : ℂ) + (ε : ℂ) * Complex.I) - a) / (s : ℂ) =
        (x₀ : ℂ) + ((ε : ℂ) / (s : ℂ)) * Complex.I := by
    dsimp [x₀, s]
    push_cast
    field_simp [ne_of_gt hs]
    ring
  have hEq : ∀ ε : ℝ,
      resolventTransform (semicircleReal a v) ((x : ℂ) + (ε : ℂ) * Complex.I) =
        (s : ℂ)⁻¹ *
          resolventTransform (semicircleReal 0 1)
            ((x₀ : ℂ) + (ε / s : ℂ) * Complex.I) := by
    intro ε
    rw [← hmap, resolventTransform_map_affine a s (ne_of_gt hs), harg]
  have hfinal := Filter.Tendsto.congr' (EventuallyEq.symm
    (Filter.Eventually.of_forall hEq)) hmul'
  simpa [s, x₀] using hfinal

end TauCeti.Probability
