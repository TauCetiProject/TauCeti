/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.MeasureTheory.Measure.TightNormed
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Pick.Herglotz.Finite
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Basic.Complex.OfRealSub
import TauCeti.MeasureTheory.Measure.ResolventTransform.Density
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# The companion equation for population covariance spectra

For a finite population measure `ν` on the real line and an aspect ratio `y ≥ 0`, the
equation `z = -1 / w + y ∫ t / (1 + t * w) dν(t)` has a unique solution in the open
upper half-plane for each `z` there. The change of variable `u = -1 / w` turns the
imaginary part of the equation into a bound on the integral of `‖t / (u - t)‖²`.
This gives strict uniqueness and bounds the homotopy solutions for the fixed-point
argument. Only finiteness of the population measure is needed, so its support may be
unbounded. The solution is the resolvent transform of a unique probability measure.
When the population measure is concentrated on the nonnegative reals, the companion
measure is concentrated there as well. The normalization is `i t * w (i t) → -1`
as `t → ∞`.

## References

* Z. D. Bai, *Methodologies in Spectral Analysis of Large Dimensional Random Matrices,
  A Review*, Statistica Sinica 9 (1999), Theorem 3.4 and equation (3.9).
* J. W. Silverstein and S. I. Choi, *Analysis of the Limiting Spectral Distribution
  of Large Dimensional Random Matrices*, J. Multivariate Anal. 54 (1995), 295–309.
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

private def companionRatio (u : ℂ) (t : ℝ) : ℂ := t / (u - t)

private def companionKernel (u : ℂ) (t : ℝ) : ℂ := u * companionRatio u t

private theorem companionRatio_eq_resolvent {u : ℂ} {t : ℝ} (h : (t : ℂ) - u ≠ 0) :
    companionRatio u t = -u * resolvent (R := ℝ) u t - 1 := by
  rw [companionRatio, Complex.resolvent_real_eq_inv, ← neg_sub (t : ℂ) u]
  field_simp [h]
  ring

private theorem norm_companionRatio_le {u : ℂ} (hu : u.im ≠ 0) (t : ℝ) :
    ‖companionRatio u t‖ ≤ ‖u‖ / |u.im| + 1 := by
  rw [companionRatio_eq_resolvent (ofReal_sub_ne_zero_of_im_ne_zero hu t)]
  calc
    _ ≤ ‖u‖ * ‖resolvent (R := ℝ) u t‖ + 1 := by
      simpa using norm_sub_le (-u * resolvent (R := ℝ) u t) 1
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      gcongr
      exact Complex.norm_resolvent_real_le u t hu

private theorem integrable_companionRatio {u : ℂ} (hu : u.im ≠ 0) :
    Integrable (companionRatio u) ν :=
  (((integrable_resolvent_of_im_ne_zero hu).const_mul (-u)).sub (integrable_const 1)).congr
    (.of_forall fun t ↦ (companionRatio_eq_resolvent
      (ofReal_sub_ne_zero_of_im_ne_zero hu t)).symm)

private theorem integrable_companionKernel {u : ℂ} (hu : u.im ≠ 0) :
    Integrable (companionKernel u) ν :=
  (integrable_companionRatio hu).const_mul u

private theorem integrable_sq_norm_companionRatio {u : ℂ} (hu : u.im ≠ 0) :
    Integrable (fun t ↦ ‖companionRatio u t‖ ^ 2) ν :=
  (integrable_const ((‖u‖ / |u.im| + 1) ^ 2)).mono'
    ((integrable_companionRatio hu).aestronglyMeasurable.norm.pow 2) (.of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      gcongr
      exact norm_companionRatio_le hu t)

private theorem integral_companionKernel_eq {u : ℂ} (hu : u.im ≠ 0) :
    (∫ t, companionKernel u t ∂ν) =
      -(u ^ 2 * resolventTransform ν u) - ν.real univ • u := by
  have h := integrable_resolvent_of_im_ne_zero (μ := ν) hu
  have heq (t : ℝ) : companionKernel u t = -(u ^ 2 * resolvent (R := ℝ) u t) - u := by
    rw [companionKernel, companionRatio_eq_resolvent (ofReal_sub_ne_zero_of_im_ne_zero hu t)]
    ring
  simp_rw [heq]
  rw [integral_sub (f := fun t ↦ -(u ^ 2 * resolvent (R := ℝ) u t))
    ((h.const_mul _).neg) (integrable_const _), integral_neg, integral_const_mul, integral_const,
    resolventTransform_apply]

private theorem sq_norm_companionRatio (u : ℂ) (t : ℝ) :
    ‖companionRatio u t‖ ^ 2 = t ^ 2 / Complex.normSq (u - t) := by
  rw [← Complex.normSq_eq_norm_sq, companionRatio, Complex.normSq_div,
    Complex.normSq_ofReal, pow_two]

private theorem im_companionKernel (u : ℂ) (t : ℝ) :
    (companionKernel u t).im = -(u.im * ‖companionRatio u t‖ ^ 2) := by
  rw [sq_norm_companionRatio]
  simp [companionKernel, companionRatio, Complex.mul_im, Complex.div_im, Complex.div_re]
  ring

private theorem im_integral_companionKernel {u : ℂ} (hu : u.im ≠ 0) :
    (∫ t, companionKernel u t ∂ν).im =
      -(u.im * ∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) := by
  calc
    _ = ∫ t, (companionKernel u t).im ∂ν := by
      simpa only [RCLike.im_eq_complex_im] using (integral_im (integrable_companionKernel hu)).symm
    _ = _ := by simp_rw [im_companionKernel, integral_neg, integral_const_mul]

private theorem companionKernel_sub {u v : ℂ} {t : ℝ}
    (hu : (t : ℂ) - u ≠ 0) (hv : (t : ℂ) - v ≠ 0) :
    companionKernel u t - companionKernel v t =
      -(u - v) * (companionRatio u t * companionRatio v t) := by
  simp only [companionKernel, companionRatio, ← neg_sub (t : ℂ) u, ← neg_sub (t : ℂ) v]
  field_simp [hu, hv]
  ring

private theorem norm_integral_companionKernel_sub_le {u v : ℂ}
    (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    ‖(∫ t, companionKernel u t ∂ν) - ∫ t, companionKernel v t ∂ν‖ ≤
      ‖u - v‖ * (((∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) +
        ∫ t, ‖companionRatio v t‖ ^ 2 ∂ν) / 2) := by
  have hiu := integrable_sq_norm_companionRatio (ν := ν) hu
  have hiv := integrable_sq_norm_companionRatio (ν := ν) hv
  rw [← integral_sub (integrable_companionKernel hu) (integrable_companionKernel hv),
    ← integral_add hiu hiv,
    ← integral_div, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hiu.add hiv).div_const _).const_mul _) (.of_forall ?_)
  intro t
  rw [companionKernel_sub (ofReal_sub_ne_zero_of_im_ne_zero hu t)
    (ofReal_sub_ne_zero_of_im_ne_zero hv t), norm_mul, norm_neg, norm_mul]
  have hsq := sq_nonneg (‖companionRatio u t‖ - ‖companionRatio v t‖)
  exact mul_le_mul_of_nonneg_left (by nlinarith only [hsq]) (norm_nonneg _)

private theorem im_companionEquation {z u : ℂ} {a : ℝ} (hu : 0 < u.im)
    (h : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν) :
    z.im = u.im * (1 - a * ∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) := by
  rw [h, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, im_integral_companionKernel hu.ne']
  ring

private theorem mul_integral_sq_norm_companionRatio_lt_one {u z : ℂ} {a : ℝ}
    (hu : 0 < u.im) (hz : 0 < z.im)
    (h : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν) :
    a * (∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) < 1 := by
  have him := im_companionEquation hu h
  have hpos : 0 < u.im * (1 - a * ∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) := him ▸ hz
  exact sub_pos.mp (pos_of_mul_pos_right hpos hu.le)

private theorem im_le_of_companionEquation {u z : ℂ} {a : ℝ} (ha : 0 ≤ a) (hu : 0 < u.im)
    (h : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν) : z.im ≤ u.im := by
  rw [im_companionEquation hu h]
  have hnonneg := integral_nonneg (μ := ν) (fun t ↦ sq_nonneg ‖companionRatio u t‖)
  exact mul_le_of_le_one_right hu.le (by linarith [mul_nonneg ha hnonneg])

private theorem eq_of_companionEquation {u v z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hz : 0 < z.im) (hu : 0 < u.im) (hv : 0 < v.im)
    (hzu : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν)
    (hzv : z = v + (a : ℂ) * ∫ t, companionKernel v t ∂ν) : u = v := by
  have hdiff : u - v = -(a : ℂ) *
      ((∫ t, companionKernel u t ∂ν) - ∫ t, companionKernel v t ∂ν) := by
    linear_combination hzv - hzu
  by_contra hne
  have hdpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have heq : ‖u - v‖ = a *
      ‖(∫ t, companionKernel u t ∂ν) - ∫ t, companionKernel v t ∂ν‖ := by
    rw [hdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha]
  have hbound :=
    mul_le_mul_of_nonneg_left (norm_integral_companionKernel_sub_le (ν := ν) hu.ne' hv.ne') ha
  rw [← heq, mul_left_comm] at hbound
  exact (lt_irrefl _ (hbound.trans_lt (mul_lt_of_lt_one_right hdpos
    (by linarith [mul_integral_sq_norm_companionRatio_lt_one hu hz hzu,
      mul_integral_sq_norm_companionRatio_lt_one hv hz hzv]))))

private theorem mul_norm_companionRatio_le_of_norm_ge {u : ℂ} {t r a c : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (ht : ‖t‖ ≤ r) (hu : r + a * r / c < ‖u‖) :
    a * ‖companionRatio u t‖ ≤ c := by
  have hr := (norm_nonneg t).trans ht
  have hden := norm_sub_norm_le u (t : ℂ)
  rw [Complex.norm_real] at hden
  have hpos : 0 < ‖u - (t : ℂ)‖ := by
    linarith [show 0 ≤ a * r / c by positivity]
  have hbound : a * r / c ≤ ‖u - (t : ℂ)‖ := by linarith
  rw [companionRatio, norm_div, Complex.norm_real, ← mul_div_assoc, div_le_iff₀ hpos]
  calc
    a * ‖t‖ ≤ a * r := mul_le_mul_of_nonneg_left ht ha
    _ ≤ c * ‖u - (t : ℂ)‖ := by
      simpa only [mul_comm _ c] using (div_le_iff₀ hc).mp hbound

private theorem exists_companionRatio_pointwise_bound {y d : ℝ} (hy : 0 ≤ y) (hd : 0 < d) :
    ∃ R r : ℝ, 0 < R ∧ ν.real {t | r < ‖t‖} ≤ d ^ 2 / (y + 1) ∧
      ∀ {u : ℂ} {a : ℝ}, 0 ≤ a → a ≤ y → R ≤ ‖u‖ → ∀ t : ℝ,
        a * ‖companionRatio u t‖ ≤ d / (ν.real univ + 1) +
          (d * a * ‖companionRatio u t‖ ^ 2 +
            {t | r < ‖t‖}.indicator (fun _ ↦ (y + 1) / d) t) := by
  let ε := d ^ 2 / (y + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have htail : Tendsto (fun r : ℝ ↦ ν {t | r < ‖t‖}) atTop (𝓝 0) := by
    simpa using tendsto_measure_norm_gt_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := ν))
  obtain ⟨r, hr, ht⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε)))).exists
  have hmass : ν.real {t | r < ‖t‖} ≤ ε := by
    simpa [measureReal_def, ENNReal.toReal_ofReal hε.le] using
      ENNReal.toReal_mono (by simp) (show ν {t | r < ‖t‖} ≤ ENNReal.ofReal ε from ht.le)
  have hr0 : 0 ≤ r := by linarith
  let c := d / (ν.real univ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let R := r + y * r / c + 1
  refine ⟨R, r, by dsimp [R]; positivity, hmass, ?_⟩
  intro u a ha hay hu t
  -- The bounded part uses the denominator directly. The tail uses the square of the ratio.
  by_cases ht : r < ‖t‖
  · rw [Set.indicator_of_mem ht]
    have hYoung : ‖companionRatio u t‖ ≤ d * ‖companionRatio u t‖ ^ 2 + 1 / d := by
      apply (mul_le_mul_iff_left₀ hd).mp
      rw [add_mul, one_div_mul_eq_div, div_self hd.ne']
      nlinarith [sq_nonneg (d * ‖companionRatio u t‖ - 1),
        mul_nonneg hd.le (norm_nonneg (companionRatio u t))]
    have ha' : a / d ≤ (y + 1) / d := by gcongr; linarith
    have hm := mul_le_mul_of_nonneg_left hYoung ha
    rw [mul_add, ← mul_assoc, mul_comm a d, mul_one_div] at hm
    exact (hm.trans (add_le_add_right ha' _)).trans (le_add_of_nonneg_left hc.le)
  · rw [Set.indicator_of_notMem ht]
    have hle := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hay hr0) hc.le
    have hu' : r + a * r / c < ‖u‖ := by dsimp [R] at hu; linarith
    exact (mul_norm_companionRatio_le_of_norm_ge hc ha (le_of_not_gt ht) hu').trans
      (le_add_of_nonneg_right (by positivity))

private theorem exists_mul_norm_integral_companionRatio_le {y ε : ℝ}
    (hy : 0 ≤ y) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {u : ℂ} {a : ℝ}, 0 < u.im → 0 ≤ a → a ≤ y →
      a * (∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) ≤ 1 → R ≤ ‖u‖ →
      a * ‖∫ t, companionRatio u t ∂ν‖ ≤ ε := by
  let d := ε / 3
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨R, r, hR, htail, hpoint⟩ := exists_companionRatio_pointwise_bound (ν := ν) hy hd
  let B : Set ℝ := {t | r < ‖t‖}
  have hB : MeasurableSet B := measurableSet_lt measurable_const continuous_norm.measurable
  refine ⟨R, hR, ?_⟩
  intro u a hu ha hay henergy huR
  have hχ : Integrable (B.indicator (fun _ ↦ (y + 1) / d)) ν :=
    (integrable_const _).indicator hB
  have hsq := (integrable_sq_norm_companionRatio (ν := ν) hu.ne').const_mul (d * a)
  have hright : (∫ t, d / (ν.real univ + 1) +
      (d * a * ‖companionRatio u t‖ ^ 2 + B.indicator (fun _ ↦ (y + 1) / d) t) ∂ν) =
      ν.real univ * (d / (ν.real univ + 1)) +
        ((d * a) * (∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) + ν.real B * ((y + 1) / d)) := by
    calc
      _ = (∫ _ : ℝ, d / (ν.real univ + 1) ∂ν) +
          ∫ t, d * a * ‖companionRatio u t‖ ^ 2 + B.indicator (fun _ ↦ (y + 1) / d) t ∂ν :=
        integral_add (integrable_const _) (hsq.add hχ)
      _ = _ := by
        simp [integral_add hsq hχ, integral_const_mul, integral_indicator_const _ hB, smul_eq_mul]
  have hfirst : ν.real univ * (d / (ν.real univ + 1)) ≤ d := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith
  have hlast : ν.real B * ((y + 1) / d) ≤ d := by
    rw [← mul_div_assoc, div_le_iff₀ hd]
    simpa [B, pow_two] using (le_div_iff₀ (show 0 < y + 1 by positivity)).mp htail
  have hmiddle : (d * a) * (∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) ≤ d := by
    rw [mul_assoc]
    exact mul_le_of_le_one_right hd.le henergy
  calc
    _ ≤ a * ∫ t, ‖companionRatio u t‖ ∂ν :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) ha
    _ ≤ ε := by
      have hbound := integral_mono ((integrable_companionRatio (ν := ν) hu.ne').norm.const_mul a)
        ((integrable_const _).add (hsq.add hχ)) (hpoint ha hay huR)
      simp only [Pi.add_apply, integral_const_mul, hright] at hbound
      have hd' : 3 * d = ε := by dsimp [d]; ring
      linarith only [hbound, hfirst, hmiddle, hlast, hd']

private theorem exists_norm_sub_le_of_companionEquation {y : ℝ} (hy : 0 ≤ y) :
    ∃ R : ℝ, 0 < R ∧ ∀ {z u : ℂ} {a : ℝ},
      0 < z.im → 0 < u.im → 0 ≤ a → a ≤ y →
        z = u + (a : ℂ) * (∫ t, companionKernel u t ∂ν) → ‖u - z‖ ≤ R + ‖z‖ := by
  obtain ⟨R, hR, hsmall⟩ := exists_mul_norm_integral_companionRatio_le (ν := ν)
    hy (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨R, hR, ?_⟩
  intro z u a hz hu ha hay heq
  by_cases hlarge : R ≤ ‖u‖
  · have hs := (mul_integral_sq_norm_companionRatio_lt_one hu hz heq).le
    have hsmall' := hsmall hu ha hay hs hlarge
    have hnorm : ‖u - z‖ = ‖u‖ * (a * ‖∫ t, companionRatio u t ∂ν‖) := by
      have heq' : u - z = -(a : ℂ) * (u * ∫ t, companionRatio u t ∂ν) := by
        simp only [companionKernel, integral_const_mul] at heq
        linear_combination -heq
      rw [heq', norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha]
      ring
    have hbound : ‖u - z‖ ≤ ‖u‖ / 2 := by
      rw [hnorm, div_eq_mul_inv, ← one_div]
      gcongr
    have htri : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by simpa using norm_add_le (u - z) z
    linarith
  · exact (norm_sub_le u z).trans (add_le_add_left (le_of_not_ge hlarge) _)

private theorem exists_companionEquation (y : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∃ u : ℂ, 0 < u.im ∧ z = u + ((y : ℝ) : ℂ) * ∫ t, companionKernel u t ∂ν := by
  -- Translate the fixed point by z and extend the map to the plane by clamping its input height.
  -- The homotopy solutions have nonnegative imaginary displacement, so the clamp fixes them.
  let p : ℂ → ℂ := fun v ↦ (v.re : ℂ) + (max z.im v.im : ℝ) * I
  have him (v : ℂ) : (p v).im = max z.im v.im := by simp [p, Complex.mul_im]
  have hp (v : ℂ) : 0 < (p v).im := by rw [him]; exact hz.trans_le (le_max_left _ _)
  have hp_id (v : ℂ) (hv : z.im ≤ v.im) : p v = v := by
    apply Complex.ext <;> simp [p, max_eq_right hv]
  let T : ℂ → ℂ := fun x ↦ -((y : ℝ) : ℂ) * ∫ t, companionKernel (p (z + x)) t ∂ν
  have hT : Continuous T := by
    have hc : Continuous fun x : ℂ ↦ p (z + x) := by unfold p; fun_prop
    have ht : Continuous fun x : ℂ ↦ resolventTransform ν (p (z + x)) := by
      exact continuous_iff_continuousAt.2 fun x ↦
        (continuousAt_resolventTransform_of_im_ne_zero (hp (z + x)).ne').comp_of_eq
          (hc.continuousAt (x := x)) rfl
    simp only [T, integral_companionKernel_eq (hp _).ne']
    fun_prop
  have hTi (x : ℂ) : 0 ≤ (T x).im := by
    simp only [T, neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, im_integral_companionKernel (hp _).ne', mul_neg, neg_neg]
    exact mul_nonneg y.coe_nonneg <| mul_nonneg (hp _).le (integral_nonneg fun _ ↦ sq_nonneg _)
  obtain ⟨R, hR, hbound⟩ := exists_norm_sub_le_of_companionEquation (ν := ν) y.coe_nonneg
  let L := R + ‖z‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hK := (isCompact_closedBall (0 : ℂ) L).image hT
  obtain ⟨x, -, hx⟩ := leraySchauderFixedPoint_closedBall hL hT.continuousOn
    (by rwa [hK.isClosed.closure_eq]) (fun x hx θ hθ hxθ ↦ by
      have hxi : 0 ≤ x.im := by
        rw [hxθ, Complex.smul_im]
        exact mul_nonneg hθ.1.le (hTi x)
      have hxi' : z.im ≤ (z + x).im := by simp [Complex.add_im, hxi]
      have hEq : z = (z + x) + ((θ * y : ℝ) : ℂ) * ∫ t, companionKernel (z + x) t ∂ν := by
        have heq := hxθ
        simp only [T, hp_id _ hxi', Complex.real_smul, Complex.ofReal_mul] at heq ⊢
        linear_combination -heq
      have ha : 0 ≤ θ * (y : ℝ) := mul_nonneg hθ.1.le y.coe_nonneg
      have hay : θ * (y : ℝ) ≤ y := mul_le_of_le_one_left y.coe_nonneg hθ.2.le
      have hle := hbound hz (hz.trans_le hxi') ha hay hEq
      rw [add_sub_cancel_left] at hle
      dsimp [L] at hx
      linarith)
  have hxi : 0 ≤ x.im := hx.eq ▸ hTi x
  have hxi' : z.im ≤ (z + x).im := by simp [Complex.add_im, hxi]
  refine ⟨z + x, hz.trans_le hxi', ?_⟩
  have heq := hx.eq
  simp only [T, hp_id _ hxi'] at heq
  linear_combination heq

private theorem companionKernel_neg_inv {w : ℂ} (hw : w ≠ 0) (t : ℝ) :
    companionKernel (-w⁻¹) t = t / (1 + (t : ℂ) * w) := by
  have heq : -w⁻¹ - (t : ℂ) = -(1 + (t : ℂ) * w) / w := by
    field_simp
    ring
  rw [companionKernel, companionRatio, heq, div_div_eq_mul_div, ← mul_div_assoc]
  simp only [neg_mul, div_neg, neg_div, neg_neg]
  rw [mul_left_comm, inv_mul_cancel₀ hw, mul_one]

private theorem companionEquation_iff {ν : Measure ℝ} {z w a : ℂ} (hw : w ≠ 0) :
    (z = -w⁻¹ + a * ∫ t, companionKernel (-w⁻¹) t ∂ν) ↔
      z = -w⁻¹ + a * ∫ t, (t : ℂ) / (1 + (t : ℂ) * w) ∂ν := by
  simp only [companionKernel_neg_inv hw]

/-- The integral kernel of the population covariance companion equation is integrable
against any finite population measure at a nonreal transform variable. -/
theorem integrable_populationCovarianceCompanionKernel_of_im_ne_zero {w : ℂ}
    (hw : w.im ≠ 0) : Integrable (fun t : ℝ ↦ (t : ℂ) / (1 + (t : ℂ) * w)) ν := by
  have hw₀ : w ≠ 0 := fun h ↦ hw (by simp [h])
  have hu : (-w⁻¹).im ≠ 0 := by
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_ne_zero hw (Complex.normSq_pos.mpr hw₀).ne'
  exact (integrable_companionKernel hu).congr (.of_forall (companionKernel_neg_inv hw₀))

/-- For every upper-half-plane parameter `z` there is exactly one upper-half-plane
solution of the companion equation with population measure `ν` and aspect ratio `y`. -/
theorem existsUnique_populationCovarianceCompanion (ν : Measure ℝ) [IsFiniteMeasure ν]
    (y : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∃! w : ℂ, 0 < w.im ∧
      z = -w⁻¹ + ((y : ℝ) : ℂ) * ∫ t, (t : ℂ) / (1 + (t : ℂ) * w) ∂ν := by
  obtain ⟨u, hu, heq⟩ := exists_companionEquation (ν := ν) y hz
  refine ⟨-u⁻¹, ⟨im_neg_inv_pos.mpr hu, ?_⟩, ?_⟩
  · have hw₀ := UpperHalfPlane.ne_zero ⟨-u⁻¹, im_neg_inv_pos.mpr hu⟩
    exact (companionEquation_iff hw₀).mp (by simpa using heq)
  · intro w hw
    have hw' := im_neg_inv_pos.mpr hw.1
    have heq' := (companionEquation_iff (UpperHalfPlane.ne_zero ⟨w, hw.1⟩)).mpr hw.2
    have h := eq_of_companionEquation y.coe_nonneg hz hw' hu heq' heq
    simpa only [inv_neg, inv_inv, neg_neg] using congrArg (fun v : ℂ ↦ -v⁻¹) h

private theorem exists_differentiableOn_companionReciprocal (y : ℝ≥0) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        0 < (u z).im ∧ z = u z + ((y : ℝ) : ℂ) * ∫ t, companionKernel (u z) t ∂ν := by
  let H := UpperHalfPlane.upperHalfPlaneSet
  let f : ℂ → ℂ := fun u ↦ u + ((y : ℝ) : ℂ) * ∫ t, companionKernel u t ∂ν
  -- The inverse is holomorphic on the image of the open domain where both u and f u lie in H.
  let D := H ∩ f ⁻¹' H
  have hH : IsOpen H := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hd : DifferentiableOn ℂ f H := by
    let g : ℂ → ℂ := fun u ↦ u + ((y : ℝ) : ℂ) *
      (-(u ^ 2 * resolventTransform ν u) - (ν.real univ : ℂ) * u)
    have hm : DifferentiableOn ℂ (resolventTransform ν) H :=
      analyticOnNhd_resolventTransform_setOf_im_pos.differentiableOn
    have hg : DifferentiableOn ℂ g H := by unfold g; fun_prop
    exact hg.congr fun u hu ↦ by
      simp [f, g, integral_companionKernel_eq (ne_of_gt hu), Complex.real_smul]
  have hD : IsOpen D := hd.continuousOn.isOpen_inter_preimage hH hH
  have hf : BijOn f D H := by
    refine ⟨fun _ hu ↦ hu.2, ?_, ?_⟩
    · intro u hu v hv heq
      exact eq_of_companionEquation y.coe_nonneg hu.2 hu.1 hv.1 rfl heq
    · intro z hz
      obtain ⟨u, hu, heq⟩ := exists_companionEquation (ν := ν) y hz
      have heq' : f u = z := heq.symm
      exact ⟨u, ⟨hu, show f u ∈ H from heq' ▸ hz⟩, heq'⟩
  have hdiff := DifferentiableOn.invFunOn (hd.mono inter_subset_left) hD hf.injOn
  rw [hf.image_eq] at hdiff
  refine ⟨invFunOn f D, hdiff, fun z hz ↦ ?_⟩
  exact ⟨(hf.surjOn.mapsTo_invFunOn hz).1, (hf.surjOn.rightInvOn_invFunOn hz).symm⟩

private theorem tendsto_mul_neg_inv_companionReciprocal {u : ℂ → ℂ} (y : ℝ≥0)
    (h : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      0 < (u z).im ∧ z = u z + ((y : ℝ) : ℂ) * ∫ t, companionKernel (u z) t ∂ν) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) * I * (-(u (t * I))⁻¹)) atTop (𝓝 (-1)) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨R, hR, hsmall⟩ := exists_mul_norm_integral_companionRatio_le (ν := ν)
    y.coe_nonneg (show 0 < ε / 2 by positivity)
  refine ⟨R, fun t ht ↦ ?_⟩
  let z := (t : ℂ) * I
  have hzim : z.im = t := by simp [z, Complex.mul_im]
  have hz : 0 < z.im := hzim.symm ▸ hR.trans_le ht
  obtain ⟨hu, heq⟩ := h z hz
  have he := (mul_integral_sq_norm_companionRatio_lt_one hu hz heq).le
  have hnorm : R ≤ ‖u z‖ :=
    (ht.trans (hzim ▸ im_le_of_companionEquation y.coe_nonneg hu heq)).trans
      (le_abs_self _ |>.trans (Complex.abs_im_le_norm _))
  have hu0 : u z ≠ 0 := fun hh ↦ hu.ne' (by simp [hh])
  have heq' : z * (-(u z)⁻¹) - (-1) =
      -(((y : ℝ) : ℂ) * ∫ t, companionRatio (u z) t ∂ν) := by
    nth_rw 1 [heq]
    simp only [companionKernel, integral_const_mul]
    field_simp
    ring
  rw [dist_eq_norm]
  calc
    _ = (y : ℝ) * ‖∫ t, companionRatio (u z) t ∂ν‖ := by
      rw [heq', norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg y.coe_nonneg]
    _ ≤ ε / 2 := hsmall hu y.coe_nonneg le_rfl he hnorm
    _ < ε := by linarith

/-- A probability measure solves the population covariance companion equation if its
Stieltjes transform satisfies the equation throughout the upper half-plane. -/
def IsPopulationCovarianceCompanion (ν : Measure ℝ) (y : ℝ≥0)
    (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    z = -(resolventTransform (μ : Measure ℝ) z)⁻¹ +
      ((y : ℝ) : ℂ) *
        ∫ t, (t : ℂ) / (1 + (t : ℂ) * resolventTransform (μ : Measure ℝ) z) ∂ν

/-- The companion solution predicate is characterized by the Stieltjes transform equation. -/
theorem isPopulationCovarianceCompanion_iff {ν : Measure ℝ} {y : ℝ≥0} {μ : ProbabilityMeasure ℝ} :
    IsPopulationCovarianceCompanion ν y μ ↔ ∀ z : ℂ, 0 < z.im →
      z = -(resolventTransform (μ : Measure ℝ) z)⁻¹ +
        ((y : ℝ) : ℂ) *
          ∫ t, (t : ℂ) / (1 + (t : ℂ) * resolventTransform (μ : Measure ℝ) z) ∂ν :=
  Iff.rfl

private theorem exists_populationCovarianceCompanionMeasure (y : ℝ≥0) :
    ∃ μ : ProbabilityMeasure ℝ, IsPopulationCovarianceCompanion ν y μ := by
  obtain ⟨u, hdu, hu⟩ := exists_differentiableOn_companionReciprocal (ν := ν) y
  let w : ℂ → ℂ := fun z ↦ -(u z)⁻¹
  have hwpos (z) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) : 0 < (w z).im :=
    im_neg_inv_pos.mpr (hu z hz).1
  have hdu0 (z) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) : u z ≠ 0 :=
    fun heq ↦ (hu z hz).1.ne' (by simp [heq])
  have hwd : DifferentiableOn ℂ w UpperHalfPlane.upperHalfPlaneSet := (hdu.inv hdu0).neg
  have hnorm : ∀ᶠ t : ℝ in atTop, t * ‖w (t * I)‖ ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hz : (t : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using ht
    have hsmall := im_le_of_companionEquation y.coe_nonneg (hu _ hz).1 (hu _ hz).2
    have hle : t ≤ ‖u (t * I)‖ := by
      simpa using hsmall.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
    simp only [w, norm_neg, norm_inv, ← div_eq_mul_inv, div_le_one (ht.trans_le hle)]
    exact hle
  obtain ⟨b, μ, -, hmfin, hrep⟩ := exists_eq_subtractedResolventKernel_add hwd
    (fun z hz ↦ (hwpos z hz).le)
  have hfinite : IsFiniteMeasure μ :=
    isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hmfin hrep (by
      filter_upwards [hnorm, eventually_ge_atTop (0 : ℝ)] with t ht ht0
      exact (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) ht0).trans ht)
  have hres := eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound hrep hnorm
  have hm : Tendsto (fun t : ℝ ↦ (t : ℂ) * I * resolventTransform μ (t * I))
      atTop (𝓝 (-1)) :=
    (tendsto_mul_neg_inv_companionReciprocal y hu).congr' (by
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact congrArg (((t : ℂ) * I) * ·) (hres _ (by simpa using ht)))
  have hmass := tendsto_nhds_unique (tendsto_mul_I_mul_resolventTransform (μ := μ)) hm
  have hone : μ.real univ = 1 := by exact_mod_cast neg_injective hmass
  have hprob : IsProbabilityMeasure μ := ⟨by
    rw [← ofReal_measureReal, hone, ENNReal.ofReal_one]⟩
  refine ⟨⟨μ, hprob⟩, isPopulationCovarianceCompanion_iff.mpr fun z hz ↦ ?_⟩
  rw [ProbabilityMeasure.coe_mk, ← hres z hz]
  have hw₀ := UpperHalfPlane.ne_zero ⟨w z, hwpos z hz⟩
  exact (companionEquation_iff hw₀).mp (by simpa [w] using (hu z hz).2)

/-- The companion equation determines the Stieltjes transform of a unique probability
measure on the real line. -/
theorem existsUnique_populationCovarianceCompanionMeasure (ν : Measure ℝ) [IsFiniteMeasure ν]
    (y : ℝ≥0) :
    ∃! μ : ProbabilityMeasure ℝ, IsPopulationCovarianceCompanion ν y μ := by
  obtain ⟨μ, hμ⟩ := exists_populationCovarianceCompanionMeasure (ν := ν) y
  refine ⟨μ, hμ, ?_⟩
  intro κ hκ
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_resolventTransform fun z hz ↦ ?_
  obtain ⟨w, -, hw⟩ := existsUnique_populationCovarianceCompanion ν y hz
  exact (hw _ ⟨im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz,
    isPopulationCovarianceCompanion_iff.mp hκ z hz⟩).trans
    (hw _ ⟨im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz,
      isPopulationCovarianceCompanion_iff.mp hμ z hz⟩).symm

/-- The probability measure whose Stieltjes transform solves the population covariance
companion equation at aspect ratio `y`. -/
def populationCovarianceCompanionMeasure (ν : Measure ℝ) [IsFiniteMeasure ν]
    (y : ℝ≥0) : ProbabilityMeasure ℝ :=
  (existsUnique_populationCovarianceCompanionMeasure ν y).choose

/-- The population covariance companion measure satisfies the companion equation. -/
@[simp]
theorem populationCovarianceCompanionMeasure_spec (ν : Measure ℝ) [IsFiniteMeasure ν]
    (y : ℝ≥0) : IsPopulationCovarianceCompanion ν y (populationCovarianceCompanionMeasure ν y) :=
  (existsUnique_populationCovarianceCompanionMeasure ν y).choose_spec.1

/-- Every probability measure satisfying the companion equation is the population covariance
companion measure. -/
theorem eq_populationCovarianceCompanionMeasure {y : ℝ≥0} {μ : ProbabilityMeasure ℝ}
    (hμ : IsPopulationCovarianceCompanion ν y μ) : μ = populationCovarianceCompanionMeasure ν y :=
  (existsUnique_populationCovarianceCompanionMeasure ν y).choose_spec.2 μ hμ

private theorem re_companionKernel_add_nonneg (u : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (companionKernel u t).re + u.re * ‖companionRatio u t‖ ^ 2 := by
  have heq : (companionKernel u t).re + u.re * ‖companionRatio u t‖ ^ 2 =
      t * Complex.normSq u / Complex.normSq (u - t) := by
    rw [sq_norm_companionRatio]
    simp [companionKernel, companionRatio, Complex.mul_re, Complex.div_im, Complex.div_re,
      Complex.normSq_apply u]
    ring
  rw [heq]
  exact div_nonneg (mul_nonneg ht (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)

private theorem re_mul_le_of_companionEquation {z u : ℂ} {a : ℝ} (ha : 0 ≤ a) (hu : 0 < u.im)
    (hν : ∀ᵐ t : ℝ ∂ν, 0 ≤ t)
    (h : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν) :
    u.re * (1 - a * ∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) ≤ z.re := by
  have hk := integrable_companionKernel (ν := ν) hu.ne'
  have hre : (∫ t, companionKernel u t ∂ν).re = ∫ t, (companionKernel u t).re ∂ν := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hk).symm
  have hnonneg : 0 ≤ (∫ t, (companionKernel u t).re ∂ν) +
      u.re * (∫ t, ‖companionRatio u t‖ ^ 2 ∂ν) := by
    rw [← integral_const_mul, ← integral_add
      (show Integrable (fun t ↦ (companionKernel u t).re) ν from hk.re)
      ((integrable_sq_norm_companionRatio hu.ne').const_mul _)]
    exact integral_nonneg_of_ae (hν.mono fun _ ht ↦ re_companionKernel_add_nonneg u ht)
  rw [h, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hre]
  linarith [mul_nonneg ha hnonneg]

private theorem im_neg_inv_le_of_companionEquation {z u : ℂ} {a B : ℝ} (ha : 0 ≤ a)
    (hz : 0 < z.im) (hx : z.re < 0) (hu : 0 < u.im) (hB : ‖u‖ ≤ B)
    (hν : ∀ᵐ t : ℝ ∂ν, 0 ≤ t)
    (h : z = u + (a : ℂ) * ∫ t, companionKernel u t ∂ν) :
    (-u⁻¹).im ≤ B * z.im / (-z.re) ^ 3 := by
  let q := 1 - a * ∫ t, ‖companionRatio u t‖ ^ 2 ∂ν
  have hq : 0 < q := sub_pos.mpr (mul_integral_sq_norm_companionRatio_lt_one hu hz h)
  have hq' : q ≤ 1 := sub_le_self _ (mul_nonneg ha (integral_nonneg fun _ ↦ sq_nonneg _))
  have hreal : u.re * q ≤ z.re := re_mul_le_of_companionEquation ha hu hν h
  have hur : u.re < 0 := neg_of_mul_neg_left (hreal.trans_lt hx) hq.le
  have hnorm : -z.re ≤ ‖u‖ := by
    have hle : u.re * 1 ≤ u.re * q := mul_le_mul_of_nonpos_left hq' hur.le
    have habs := (neg_le_abs u.re).trans (Complex.abs_re_le_norm u)
    linarith
  have hBq : -z.re ≤ B * q := by
    have hnegu : -u.re ≤ B := ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans hB
    linarith [mul_le_mul_of_nonneg_right hnegu hq.le]
  have him : u.im ≤ B * z.im / (-z.re) := by
    refine (le_div_iff₀ (neg_pos.mpr hx)).2 ?_
    calc
      _ ≤ u.im * (B * q) := mul_le_mul_of_nonneg_left hBq hu.le
      _ = B * z.im := by rw [im_companionEquation hu h]; ring
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, Complex.normSq_eq_norm_sq]
  calc
    _ ≤ u.im / (-z.re) ^ 2 :=
      div_le_div_of_nonneg_left hu.le (pow_pos (neg_pos.mpr hx) _) (by
        exact pow_le_pow_left₀ (neg_nonneg.mpr hx.le) hnorm _)
    _ ≤ (B * z.im / (-z.re)) / (-z.re) ^ 2 := div_le_div_of_nonneg_right him (by positivity)
    _ = _ := by rw [div_div]; congr 1; ring

/-- When the population measure is concentrated on the nonnegative reals, any probability
measure solving the companion equation is concentrated there as well. -/
theorem measure_Iio_zero_of_populationCovarianceCompanion {ν : Measure ℝ} [IsFiniteMeasure ν]
    {μ : ProbabilityMeasure ℝ} (hν : ∀ᵐ t : ℝ ∂ν, 0 ≤ t) (y : ℝ≥0)
    (hμ : IsPopulationCovarianceCompanion ν y μ) :
    (μ : Measure ℝ) (Iio 0) = 0 := by
  obtain ⟨R, -, hbound⟩ := exists_norm_sub_le_of_companionEquation (ν := ν) y.coe_nonneg
  refine measure_eq_zero_of_tendsto_im_resolventTransform_zero (fun x hx ↦ ?_)
  let B := R + 2 * (|x| + 1)
  have hη₀ : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hη₁ : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  have hη := hη₀.and hη₁
  have hlim : Tendsto (fun η : ℝ ↦ B * η / (-x) ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun η : ℝ ↦ B * η / (-x) ^ 3) := by fun_prop
    simpa only [mul_zero, zero_div] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hη] with η hη
    exact (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) (by simpa using hη.1)).le
  · filter_upwards [hη] with η hη
    let z := (x : ℂ) + (η : ℂ) * I
    have hzim : z.im = η := by simp [z, Complex.mul_im]
    have hzre : z.re = x := by simp [z, Complex.mul_re]
    have hz : 0 < z.im := hzim.symm ▸ hη.1
    let w : ℂ := resolventTransform (μ : Measure ℝ) z
    let u := -w⁻¹
    have hw : 0 < w.im := im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz
    have hu : 0 < u.im := im_neg_inv_pos.mpr hw
    have heq := (companionEquation_iff (UpperHalfPlane.ne_zero ⟨w, hw⟩)).mpr
      (isPopulationCovarianceCompanion_iff.mp hμ z hz)
    have hunorm := hbound hz hu y.coe_nonneg le_rfl heq
    have hznorm : ‖z‖ ≤ |x| + 1 := calc
      _ ≤ ‖(x : ℂ)‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + η := by simp [abs_of_pos hη.1]
      _ ≤ |x| + 1 := by linarith [hη.2]
    have huB : ‖u‖ ≤ B := by
      have htri : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by simpa using norm_add_le (u - z) z
      dsimp [B]
      linarith
    have hle := im_neg_inv_le_of_companionEquation y.coe_nonneg hz
      (by simpa only [hzre, mem_Iio] using hx) hu huB hν heq
    simpa only [u, inv_neg, inv_inv, neg_neg, hzim, hzre] using hle

end TauCeti.Probability
