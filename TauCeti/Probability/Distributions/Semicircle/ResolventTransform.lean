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
* `TauCeti.Probability.tendsto_semicircleResolventBoundaryNormSq` and
  `TauCeti.Probability.tendsto_semicircleResolventBoundary_re`: boundary values on the support.

## Implementation notes

Outside the disc `|z - a| ≤ 2√v` the transform is the integral of a geometric series, and the
quadratic equation is the quadratic equation of the Catalan generating function. The transform is
analytic off the support, so the identity theorem on each half-plane, which meets the exterior of
the disc, extends the equation to every non-real `z`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

@[expose] public section

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

/-- The resolvent transform of the standard semicircle law. -/
def semicircleResolvent (z : ℂ) : ℂ := resolventTransform (semicircleReal 0 1) z

private theorem m_quad (hz : 0 < z.im) :
    semicircleResolvent z * semicircleResolvent z + z * semicircleResolvent z + 1 = 0 := by
  have h := resolventTransform_semicircleReal_quadratic_eq_zero (a := 0) (v := 1) (z := z) (by
    rintro ⟨x, -, hx⟩
    have h : z.im = 0 := by rw [← hx]; simp
    linarith)
  simpa [semicircleResolvent] using h

private theorem m_im_pos (hz : 0 < z.im) : 0 < (semicircleResolvent z).im :=
  im_resolventTransform_pos (μ := semicircleReal 0 1) (IsProbabilityMeasure.ne_zero _) hz

/-- The standard semicircle resolvent is purely imaginary on the positive imaginary axis. -/
theorem semicircleResolvent_at_imaginary_axis (t : ℝ) (ht : 0 < t) :
    (semicircleResolvent ((t : ℂ) * Complex.I)).re = 0 ∧
      (semicircleResolvent ((t : ℂ) * Complex.I)).im ^ 2 +
        t * (semicircleResolvent ((t : ℂ) * Complex.I)).im = 1 := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hz : 0 < z.im := by simp [z, ht]
  have hzre : z.re = 0 := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hquad := m_quad hz
  have him : (2 * (semicircleResolvent z).im + t) * (semicircleResolvent z).re = 0 := by
    have h := congrArg Complex.im hquad
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im,
      hzre, hzim] at h
    nlinarith
  have hfactor : 0 < 2 * (semicircleResolvent z).im + t := by
    have hb := m_im_pos hz
    linarith
  have hre : (semicircleResolvent z).re = 0 := (mul_eq_zero.mp him).resolve_left (ne_of_gt hfactor)
  have hm : semicircleResolvent z = (semicircleResolvent z).im * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hr := congrArg Complex.re hquad
  rw [hm] at hr
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.zero_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, hzre, hzim] at hr
  constructor
  · exact hre
  · -- Unfold the local abbreviation for the point on the imaginary axis.
    change (semicircleResolvent z).im ^ 2 + t * (semicircleResolvent z).im = 1
    nlinarith

/-- The imaginary part of the resolvent is asymptotic to `1 / t` on the imaginary axis. -/
theorem tendsto_mul_semicircleResolvent_im_atTop :
    Tendsto (fun t : ℝ ↦ t * (semicircleResolvent (t * Complex.I)).im) atTop (𝓝 1) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_mul_I_mul_resolventTransform (μ := semicircleReal 0 1))
  simpa [semicircleResolvent, Complex.mul_re] using h.neg

/-- The standard semicircle resolvent at height `ε` above a real point. -/
def semicircleResolventBoundary (x ε : ℝ) : ℂ :=
  semicircleResolvent ((x : ℂ) + (ε : ℂ) * Complex.I)

/-- The squared norm of the standard semicircle resolvent near the real axis. -/
def semicircleResolventBoundaryNormSq (x ε : ℝ) : ℝ :=
  (semicircleResolventBoundary x ε).re ^ 2 + (semicircleResolventBoundary x ε).im ^ 2

private theorem m_boundary_identities (x ε : ℝ) (hε : 0 < ε) :
    (semicircleResolventBoundary x ε).re * (semicircleResolventBoundaryNormSq x ε + 1) =
        -x * semicircleResolventBoundaryNormSq x ε ∧
      (semicircleResolventBoundary x ε).im * (1 - semicircleResolventBoundaryNormSq x ε) =
        ε * semicircleResolventBoundaryNormSq x ε := by
  let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
  let a : ℝ := (semicircleResolvent z).re
  let b : ℝ := (semicircleResolvent z).im
  let q : ℝ := a ^ 2 + b ^ 2
  have hz : 0 < z.im := by simp [z, hε]
  have hmval : semicircleResolvent z = (a : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [a, b]
    · simp [a, b]
  let c : ℂ := star (semicircleResolvent z)
  have hmc : semicircleResolvent z * c = (q : ℂ) := by
    dsimp only [c]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_apply]
    simp [a, b, q]
    ring
  have hmul := congrArg (fun w : ℂ ↦ w * c) (m_quad hz)
  have hrelmul : (q : ℂ) * semicircleResolvent z + z * (q : ℂ) + c =
      (semicircleResolvent z * semicircleResolvent z + z * semicircleResolvent z + 1) * c := by
    rw [← hmc]
    ring
  have hrel : (q : ℂ) * semicircleResolvent z + z * (q : ℂ) + c = 0 := by
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
  -- Restate the boundary abbreviations using the local real and imaginary parts.
  change a * (q + 1) = -x * q ∧ b * (1 - q) = ε * q
  constructor <;> nlinarith [hreal, himag]

private theorem m_boundary_q_estimate {x ε : ℝ} (hx : x ∈ Icc (-2) 2)
    (hε : 0 < ε) :
    0 < 1 - semicircleResolventBoundaryNormSq x ε ∧
      (1 - semicircleResolventBoundaryNormSq x ε) ^ 2 ≤ 2 * ε := by
  let a : ℝ := (semicircleResolventBoundary x ε).re
  let b : ℝ := (semicircleResolventBoundary x ε).im
  let q : ℝ := semicircleResolventBoundaryNormSq x ε
  have hids := m_boundary_identities x ε hε
  have hreal : a * (q + 1) = -x * q := by simpa [a, q] using hids.1
  have himag : b * (1 - q) = ε * q := by simpa [b, q] using hids.2
  have hb : 0 < b := by
    simpa [b, semicircleResolventBoundary] using
      m_im_pos (by simpa [semicircleResolventBoundary] using hε)
  have hqdef : q = a ^ 2 + b ^ 2 := by
    dsimp [q, a, b, semicircleResolventBoundaryNormSq]
  have hq : 0 < q := by rw [hqdef]; positivity
  have hq_lt : q < 1 := by
    by_contra hn
    have hle : 1 - q ≤ 0 := by linarith
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hb.le hle
    have hpos : 0 < ε * q := mul_pos hε hq
    rw [himag] at hnonpos
    linarith
  have hq_le : q ≤ 1 := hq_lt.le
  -- The quadratic identities bound q(1-q)^2 by b^2(q+1)^2; the imaginary
  -- identity then yields a fourth-power bound and hence the desired estimate.
  have hxabs : |x| ≤ 2 := abs_le.mpr hx
  have hx2 : x ^ 2 ≤ 4 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 2)).2 hxabs
    nlinarith [sq_abs x]
  have hreal_sq : a ^ 2 * (q + 1) ^ 2 = x ^ 2 * q ^ 2 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) hreal
    nlinarith [h]
  have hfactor :
      b ^ 2 * (q + 1) ^ 2 = q * ((q + 1) ^ 2 - x ^ 2 * q) := by
    nlinarith [hreal_sq, hqdef]
  have hfactor_le : (1 - q) ^ 2 ≤ (q + 1) ^ 2 - x ^ 2 * q := by
    have hq0 : 0 ≤ q := le_of_lt hq
    have h4x : 0 ≤ 4 - x ^ 2 := by linarith
    nlinarith [mul_nonneg hq0 h4x]
  have hbound_b :
      q * (1 - q) ^ 2 ≤ b ^ 2 * (q + 1) ^ 2 := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hfactor_le hq.le
  have himag_sq : b ^ 2 * (1 - q) ^ 2 = ε ^ 2 * q ^ 2 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) himag
    nlinarith [h]
  have hbound_mul :
      q * (1 - q) ^ 4 ≤ b ^ 2 * (q + 1) ^ 2 * (1 - q) ^ 2 := by
    calc
      q * (1 - q) ^ 4 = (q * (1 - q) ^ 2) * (1 - q) ^ 2 := by ring
      _ ≤ (b ^ 2 * (q + 1) ^ 2) * (1 - q) ^ 2 :=
        mul_le_mul_of_nonneg_right hbound_b (sq_nonneg _)
      _ = b ^ 2 * (q + 1) ^ 2 * (1 - q) ^ 2 := by ring
  have hfour : (1 - q) ^ 4 ≤ ε ^ 2 * q * (q + 1) ^ 2 := by
    apply le_of_mul_le_mul_left ?_ hq
    calc
      q * (1 - q) ^ 4 ≤ b ^ 2 * (q + 1) ^ 2 * (1 - q) ^ 2 := hbound_mul
      _ = (b ^ 2 * (1 - q) ^ 2) * (q + 1) ^ 2 := by ring
      _ = (ε ^ 2 * q ^ 2) * (q + 1) ^ 2 := by rw [himag_sq]
      _ = q * (ε ^ 2 * q * (q + 1) ^ 2) := by ring
  have hprod : q * (q + 1) ^ 2 ≤ 4 := by
    have hqplus : 0 ≤ q + 1 ∧ q + 1 ≤ 2 := by
      constructor
      · linarith
      · linarith
    have hqplus_sq : (q + 1) ^ 2 ≤ 4 := by
      have hsquare := (sq_le_sq₀ hqplus.1 (by norm_num : (0 : ℝ) ≤ 2)).2 hqplus.2
      nlinarith
    calc
      q * (q + 1) ^ 2 ≤ 1 * (q + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hq_le (sq_nonneg _)
      _ ≤ 1 * 4 := by rw [one_mul, one_mul]; exact hqplus_sq
      _ = 4 := by ring
  have hfour' : (1 - q) ^ 4 ≤ (2 * ε) ^ 2 := by
    calc
      (1 - q) ^ 4 ≤ ε ^ 2 * (q * (q + 1) ^ 2) := by
        calc
          (1 - q) ^ 4 ≤ ε ^ 2 * q * (q + 1) ^ 2 := hfour
          _ = ε ^ 2 * (q * (q + 1) ^ 2) := by ring
      _ ≤ ε ^ 2 * 4 := mul_le_mul_of_nonneg_left hprod (sq_nonneg ε)
      _ = (2 * ε) ^ 2 := by ring
  have hfour'' : ((1 - q) ^ 2) ^ 2 ≤ (2 * ε) ^ 2 := by
    convert hfour' using 1
    ring
  have hsmall : (1 - q) ^ 2 ≤ 2 * ε :=
    (sq_le_sq₀ (sq_nonneg (1 - q)) (by positivity)).1 hfour''
  exact ⟨by simpa [q] using sub_pos.mpr hq_lt, by simpa [q] using hsmall⟩

/-- The squared norm of the resolvent tends to one on the support. -/
theorem tendsto_semicircleResolventBoundaryNormSq {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ semicircleResolventBoundaryNormSq x ε) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · have hδ : 0 < 1 - c := sub_pos.mpr hc
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0 : ℝ) < (1 - c) ^ 2 / 2 from
          div_pos (sq_pos_of_pos hδ) (by norm_num)))]
      with ε hε hεsmall
    let q : ℝ := semicircleResolventBoundaryNormSq x ε
    have hest := m_boundary_q_estimate hx hε
    have hqpos : 0 < 1 - q := by simpa [q] using hest.1
    have hqbound : (1 - q) ^ 2 ≤ 2 * ε := by simpa [q] using hest.2
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
    let q : ℝ := semicircleResolventBoundaryNormSq x ε
    have hest := m_boundary_q_estimate hx hε
    have hqbound : q < 1 := by
      have hqpos : 0 < 1 - q := hest.1
      linarith [hqpos]
    have hc1 : 1 < c := by linarith
    have : q < c := hqbound.trans hc1
    simpa [q] using this

/-- The real part of the upper boundary value is `-x / 2` on the support. -/
theorem tendsto_semicircleResolventBoundary_re {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ (semicircleResolventBoundary x ε).re) (𝓝[>] 0) (𝓝 (-x / 2)) := by
  let Q : ℝ → ℝ := fun ε ↦ semicircleResolventBoundaryNormSq x ε
  let A : ℝ → ℝ := fun ε ↦ (semicircleResolventBoundary x ε).re
  let F : ℝ → ℝ := fun t ↦ -x * t / (t + 1)
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 1) := tendsto_semicircleResolventBoundaryNormSq hx
  have hcont : ContinuousAt F 1 := by
    fun_prop (disch := norm_num)
  have hF := hcont.tendsto.comp hQ
  have hEq : ∀ᶠ ε : ℝ in 𝓝[>] 0, A ε = F (Q ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let a : ℝ := (semicircleResolventBoundary x ε).re
    let q : ℝ := semicircleResolventBoundaryNormSq x ε
    have hids := m_boundary_identities x ε hε
    have hreal : a * (q + 1) = -x * q := by simpa [a, q] using hids.1
    have hqnonneg : 0 ≤ q := by
      dsimp [q, semicircleResolventBoundaryNormSq]
      positivity
    have hformula : a = -x * q / (q + 1) := by
      have hqp : q + 1 ≠ 0 := by linarith
      field_simp [hqp]
      nlinarith [hreal]
    simpa [A, F, Q, a, q] using hformula
  have hA := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hF
  have hF1 : F 1 = -x / 2 := by dsimp [F]; ring
  rw [← hF1]
  simpa [A] using hA

/-- The height times the imaginary part of the resolvent tends to zero on the support. -/
theorem tendsto_eps_mul_semicircleResolventBoundary_im {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ ε * (semicircleResolventBoundary x ε).im) (𝓝[>] 0) (𝓝 0) := by
  have hε : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  refine Filter.Tendsto.squeeze' tendsto_const_nhds hε ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb : 0 < (semicircleResolventBoundary x ε).im :=
      m_im_pos (by simpa [semicircleResolventBoundary] using hε)
    exact mul_nonneg (le_of_lt hε) hb.le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    let a : ℝ := (semicircleResolventBoundary x ε).re
    let b : ℝ := (semicircleResolventBoundary x ε).im
    let q : ℝ := semicircleResolventBoundaryNormSq x ε
    have hest := m_boundary_q_estimate hx hε
    have hq_lt : q < 1 := by
      have hqpos : 0 < 1 - q := by simpa [q] using hest.1
      linarith [hqpos]
    have hb : 0 < b := by
      simpa [b, semicircleResolventBoundary] using
        m_im_pos (by simpa [semicircleResolventBoundary] using hε)
    have hqdef : q = a ^ 2 + b ^ 2 := by
      dsimp [q, a, b, semicircleResolventBoundaryNormSq]
    have hb_sq : b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg a, hqdef, hq_lt]
    have hb_le : b ≤ 1 :=
      (sq_le_sq₀ hb.le (by norm_num : (0 : ℝ) ≤ 1)).1 (by simpa using hb_sq)
    simpa [b] using mul_le_mul_of_nonneg_left hb_le (le_of_lt hε)

end TauCeti.Probability
