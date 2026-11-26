/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import TauCeti.Basic.Complex.OfRealSub
import Mathlib.Tactic.Positivity

/-!
# The resolvent transform on the real line

For a finite measure on the real line, the imaginary part of its resolvent transform
is the integral of the kernel `im z / ((x - re z)² + (im z)²)`.
This kernel is positive in the upper half-plane, so the imaginary part of the transform
is strictly positive there for every nonzero finite measure. We also give uniform bounds
away from the real axis, the continuity of the kernel there, the Lipschitz bound
`‖m_μ(z) - m_μ(w)‖ ≤ ‖z - w‖ / (|Im z| |Im w|) · μ(ℝ)` from the resolvent identity, the
continuity of the transform off the real axis
(`MeasureTheory.continuousAt_resolventTransform_of_im_ne_zero`), and prove
affine covariance under pushforward. No moment assumptions are needed. Conversely, off the real
axis the transform of a measure `μ` without finite weighted mass `∫ (1 + x ^ 2)⁻¹ dμ` is `0`, since
the kernel `‖(x - z)⁻¹‖` dominates `(1 + x ^ 2)⁻¹` up to a constant and so is not integrable.

Off the real axis the transform is analytic with derivative `∫ (x - z)⁻² dμ(x)`, bounded by
`|Im z|⁻² μ(ℝ)`, and its first-order Taylor expansion at `z` has remainder at most
`‖w - z‖² / (|Im z|² |Im w|) · μ(ℝ)`; these bounds are uniform over all measures of a given mass.
For real `t` the map `z ↦ z - t m_μ(z)` maps `{Im z > |t| μ(ℝ) + 1}` injectively into the upper
half-plane, so two functions analytic in the upper half-plane that agree at the points
`z - t m_μ(z)` agree there.

For a function `h` integrable for a measure on the real line, the integrands `h(x) / (x - z)`
(off the real axis) and `x h(x) / (1 + x ^ 2)` are integrable too
(`TauCeti.integrable_div_ofReal_sub`, `TauCeti.integrable_div_one_add_sq_mul`).

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`; the Stieltjes transform `∫ (z - x)⁻¹ dμ(x)` is its negative.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  for the Stieltjes transform and its inversion (Theorem 2.4.3).
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace Complex

/-- The real resolvent kernel is `(x - z)⁻¹`. -/
theorem resolvent_real_eq_inv (z : ℂ) (x : ℝ) : resolvent (R := ℝ) z x = ((x : ℂ) - z)⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv', coe_algebraMap]

/-- The imaginary part of the real resolvent kernel, with sign `(x - z)⁻¹`. -/
theorem im_resolvent_real (z : ℂ) (x : ℝ) :
    (resolvent z x).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
  simp [resolvent, Ring.inverse_eq_inv', Complex.inv_im, Complex.normSq_apply, sq]

/-- The real resolvent kernel is bounded by the reciprocal distance to the real axis. -/
theorem norm_resolvent_real_le (z : ℂ) (x : ℝ) (hz : z.im ≠ 0) :
    ‖resolvent z x‖ ≤ |z.im|⁻¹ := by
  rw [resolvent_real_eq_inv, norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa using abs_im_le_norm ((x : ℂ) - z)

/-- A real number lies in the real resolvent set of every complex number off the real axis. -/
theorem mem_resolventSet_real {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) : x ∈ resolventSet ℝ z := by
  rw [spectrum.mem_resolventSet_iff, isUnit_iff_ne_zero]
  exact fun h ↦ hz (by simpa using congrArg Complex.im h)

/-- Off the real axis the real resolvent kernel is continuous. -/
theorem continuous_resolvent_real {z : ℂ} (hz : z.im ≠ 0) : Continuous (resolvent (R := ℝ) z) :=
  continuous_iff_continuousAt.2 fun x ↦
    (spectrum.hasDerivAt_resolvent_const_left (mem_resolventSet_real hz x)).continuousAt

/-- As a function of the real input, the resolvent kernel is Lipschitz with constant
`|Im z|⁻²`. -/
theorem lipschitzWith_resolvent_real {z : ℂ} (hz : z.im ≠ 0) :
    LipschitzWith (‖z.im‖₊⁻¹ ^ 2) (resolvent (R := ℝ) z) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hx : (x : ℂ) - z ≠ 0 := fun h ↦ hz (by simpa using congrArg Complex.im h)
  have hy : (y : ℂ) - z ≠ 0 := fun h ↦ hz (by simpa using congrArg Complex.im h)
  have hlow (t : ℝ) : |z.im| ≤ ‖(t : ℂ) - z‖ := by
    simpa using abs_im_le_norm ((t : ℂ) - z)
  calc
    dist (resolvent z x) (resolvent z y) =
        |x - y| / (‖(x : ℂ) - z‖ * ‖(y : ℂ) - z‖) := by
      rw [resolvent_real_eq_inv, resolvent_real_eq_inv, dist_inv_inv₀ hx hy,
        dist_sub_right, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    _ ≤ |x - y| / (|z.im| * |z.im|) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (mul_le_mul (hlow x) (hlow y) (abs_nonneg _) (norm_nonneg _))
    _ = ((‖z.im‖₊⁻¹ ^ 2 : NNReal) : ℝ) * dist x y := by
      simp only [NNReal.coe_pow, NNReal.coe_inv, coe_nnNorm, Real.norm_eq_abs, Real.dist_eq]
      ring

end Complex

namespace MeasureTheory

/-- Conjugating the spectral parameter conjugates the resolvent transform of a real measure.
No finiteness assumption is needed, since the Bochner integral commutes with conjugation. -/
@[simp]
theorem Measure.resolventTransform_conj (μ : Measure ℝ) (z : ℂ) :
    resolventTransform μ (conj z) = conj (resolventTransform μ z) := by
  simp only [Complex.star_def.symm]
  rw [resolventTransform_apply, resolventTransform_apply]
  calc
    (∫ x, resolvent (R := ℝ) (star z) x ∂μ) =
        ∫ x, star (resolvent (R := ℝ) z x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            simp [resolvent, Ring.inverse_eq_inv']
    _ = _ := by
      simpa only [RCLike.star_def] using (integral_conj (f := resolvent (R := ℝ) z))

/-- Conjugating the spectral parameter conjugates the derivative of the resolvent transform of a
real measure. -/
@[simp]
theorem Measure.deriv_resolventTransform_conj (μ : Measure ℝ) (z : ℂ) :
    deriv (resolventTransform μ) (conj z) = conj (deriv (resolventTransform μ) z) := by
  have h : (resolventTransform μ : ℂ → ℂ) = conj ∘ resolventTransform μ ∘ conj := by
    funext w
    simp
  conv_lhs => rw [h, deriv_conj_conj]
  simp

/-- The resolvent transform is `-∫ (z - x)⁻¹ dμ(x)`, the negative of the Cauchy–Stieltjes transform
in the convention `(z - x)⁻¹`. -/
theorem resolventTransform_eq_neg_integral_inv_sub (μ : Measure ℝ) (z : ℂ) :
    resolventTransform μ z = -∫ x : ℝ, (z - x)⁻¹ ∂μ := by
  rw [resolventTransform_apply, ← integral_neg]
  congr 1 with x
  rw [Complex.resolvent_real_eq_inv, ← inv_neg, neg_sub]

/-- The resolvent transform subtracts a dominated finite measure at points where the
resolvent is integrable for the larger measure. -/
theorem Measure.resolventTransform_sub (μ : Measure ℝ) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {z : ℂ} (hz : Integrable (resolvent (R := ℝ) z) μ) :
    resolventTransform (μ - ν) z = resolventTransform μ z - resolventTransform ν z := by
  apply eq_sub_of_add_eq
  simp only [resolventTransform_apply]
  rw [← integral_add_measure (hz.mono_measure Measure.sub_le) (hz.mono_measure hν),
    Measure.sub_add_cancel_of_le hν]

/-- At a nonreal point, the resolvent transform of a measure `μ` without finite weighted mass
`∫ (1 + x ^ 2)⁻¹ dμ` is `0`, since the resolvent kernel is not integrable. -/
theorem resolventTransform_eq_zero_of_not_lintegral_lt_top {μ : Measure ℝ}
    (hμ : ¬∫⁻ x, ENNReal.ofReal (1 + x ^ 2)⁻¹ ∂μ < ⊤) {z : ℂ} (hz : z.im ≠ 0) :
    resolventTransform μ z = 0 := by
  rw [resolventTransform_apply]
  refine integral_undef fun h ↦ hμ (Integrable.lintegral_lt_top ?_)
  refine (h.norm.const_mul (1 + ‖z‖)).mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hx : 0 < ‖(x : ℂ) - z‖ :=
    norm_pos_iff.2 fun h ↦ hz (by simpa using congrArg Complex.im h)
  have hle : ‖(x : ℂ) - z‖ ≤ (1 + x ^ 2) * (1 + ‖z‖) := by
    have h1 : ‖(x : ℂ) - z‖ ≤ |x| + ‖z‖ := by simpa using norm_sub_le (x : ℂ) z
    nlinarith [abs_nonneg x, sq_abs x, norm_nonneg z, sq_nonneg (|x| - 1), mul_nonneg
      (sq_nonneg x) (norm_nonneg z)]
  rw [Real.norm_of_nonneg (by positivity), Complex.resolvent_real_eq_inv, norm_inv,
    ← div_eq_mul_inv, le_div_iff₀ hx, inv_mul_le_iff₀ (by positivity)]
  exact hle

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The resolvent transform of a finite measure on `ℝ` is continuous off the real axis, by
Mathlib's `hasDerivAt_resolventTransform`. -/
theorem continuousAt_resolventTransform_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt (resolventTransform μ) z :=
  (hasDerivAt_resolventTransform z (Complex.notMem_image_ofReal_of_im_ne_zero hz)).continuousAt

/-- The real resolvent kernel is integrable for a finite measure off the real axis. -/
theorem integrable_resolvent_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (resolvent (R := ℝ) z) μ := by
  apply integrable_resolvent
  rintro ⟨x, _, hx⟩
  exact hz (by simpa using (congrArg Complex.im hx).symm)

/-- The imaginary part of the transform is the integral of the kernel
`z.im / ((x - z.re)² + z.im²)`, which is the Poisson kernel without the factor `π⁻¹`
when `0 < z.im`. -/
theorem im_resolventTransform {z : ℂ} :
    (resolventTransform μ z).im =
      ∫ x, z.im / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  by_cases hz : z.im = 0
  · by_cases hi : Integrable (resolvent (R := ℝ) z) μ
    · simpa only [resolventTransform_apply, RCLike.im_eq_complex_im,
        Complex.im_resolvent_real] using (integral_im hi).symm
    · simp [resolventTransform_apply, integral_undef hi, hz]
  · simpa only [resolventTransform_apply, RCLike.im_eq_complex_im,
      Complex.im_resolvent_real] using
      (integral_im (integrable_resolvent_of_im_ne_zero (μ := μ) hz)).symm

/-- A uniform bound for the transform of a finite measure away from the real axis. -/
theorem norm_resolventTransform_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform μ z‖ ≤ |z.im|⁻¹ * μ.real Set.univ := by
  rw [resolventTransform_apply]
  exact norm_integral_le_of_norm_le_const
    (ae_of_all _ fun x => Complex.norm_resolvent_real_le z x hz)

/-- Along the imaginary axis, `y ‖m_μ(i y)‖ ≤ μ(ℝ)` for `y > 0`. -/
theorem mul_norm_resolventTransform_ofReal_mul_I_le {y : ℝ} (hy : 0 < y) :
    y * ‖resolventTransform μ (y * I)‖ ≤ μ.real Set.univ := by
  have h := norm_resolventTransform_le (μ := μ) (z := y * I) (by simpa using hy.ne')
  rw [show ((y : ℂ) * I).im = y by simp, abs_of_pos hy] at h
  calc y * ‖resolventTransform μ (y * I)‖ ≤ y * (y⁻¹ * μ.real Set.univ) := by gcongr
    _ = μ.real Set.univ := by field_simp

/-- The transform of a finite measure is Lipschitz away from the real axis:
`‖m_μ(z) - m_μ(w)‖ ≤ ‖z - w‖ / (|Im z| |Im w|) · μ(ℝ)`. -/
theorem norm_resolventTransform_sub_le {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖resolventTransform μ z - resolventTransform μ w‖ ≤
      ‖z - w‖ / (|z.im| * |w.im|) * μ.real Set.univ := by
  rw [resolventTransform_apply, resolventTransform_apply, ← integral_sub
    (integrable_resolvent_of_im_ne_zero hz) (integrable_resolvent_of_im_ne_zero hw)]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ ?_)
  rw [spectrum.resolvent_sub_resolvent (Complex.mem_resolventSet_real hz x)
    (Complex.mem_resolventSet_real hw x), norm_mul, norm_mul,
    div_eq_mul_inv, mul_inv, mul_comm ‖resolvent z x‖, mul_assoc]
  gcongr
  · exact Complex.norm_resolvent_real_le z x hz
  · exact Complex.norm_resolvent_real_le w x hw

/-- The resolvent identity for the transform of a finite measure off the real axis:
`m_μ(z) - m_μ(w) = (z - w) ∫ (x - z)⁻¹ (x - w)⁻¹ dμ(x)`. -/
theorem resolventTransform_sub_resolventTransform {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolventTransform μ z - resolventTransform μ w =
      (z - w) * ∫ x, resolvent z x * resolvent w x ∂μ := by
  rw [resolventTransform_apply, resolventTransform_apply, ← integral_sub
    (integrable_resolvent_of_im_ne_zero hz) (integrable_resolvent_of_im_ne_zero hw),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [spectrum.resolvent_sub_resolvent (Complex.mem_resolventSet_real hz x)
    (Complex.mem_resolventSet_real hw x)]
  ring

/-- Off the real axis the transform of a finite measure is complex differentiable, with
derivative `∫ (x - z)⁻² dμ(x)`. -/
theorem hasDerivAt_resolventTransform_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (resolventTransform μ) (∫ x, resolvent z x ^ 2 ∂μ) z :=
  hasDerivAt_resolventTransform z (Complex.notMem_image_ofReal_of_im_ne_zero hz)

/-- Off the real axis the transform of a finite measure is analytic. -/
theorem analyticOnNhd_resolventTransform :
    AnalyticOnNhd ℂ (resolventTransform μ) {z : ℂ | z.im ≠ 0} :=
  (IsOpen.analyticOn_iff_analyticOnNhd
    (isOpen_ne_fun Complex.continuous_im continuous_const)).1 <|
    analyticOn_resolventTransform.mono fun _ hz ↦ Complex.notMem_image_ofReal_of_im_ne_zero hz

/-- In the upper half-plane the transform of a finite measure is analytic. -/
theorem analyticOnNhd_resolventTransform_setOf_im_pos :
    AnalyticOnNhd ℂ (resolventTransform μ) {z : ℂ | 0 < z.im} :=
  analyticOnNhd_resolventTransform.mono fun _ hz ↦ ne_of_gt hz

/-- A uniform bound for the derivative of the transform of a finite measure away from the real
axis. -/
theorem norm_deriv_resolventTransform_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖deriv (resolventTransform μ) z‖ ≤ (|z.im|⁻¹) ^ 2 * μ.real Set.univ := by
  rw [(hasDerivAt_resolventTransform_of_im_ne_zero hz).deriv]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ ?_)
  rw [norm_pow]
  gcongr
  exact Complex.norm_resolvent_real_le z x hz

/-- A uniform bound for the transform of a finite measure times its derivative away from the real
axis: `‖m_μ(z) m_μ'(z)‖ ≤ |Im z|⁻³ μ(ℝ)²`. -/
theorem norm_resolventTransform_mul_deriv_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform μ z * deriv (resolventTransform μ) z‖ ≤
      (|z.im|⁻¹) ^ 3 * μ.real Set.univ ^ 2 := by
  rw [norm_mul]
  calc _ ≤ (|z.im|⁻¹ * μ.real Set.univ) * ((|z.im|⁻¹) ^ 2 * μ.real Set.univ) :=
        mul_le_mul (norm_resolventTransform_le hz) (norm_deriv_resolventTransform_le hz)
          (norm_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
    _ = _ := by ring

/-- The second-order Taylor remainder of the transform of a finite measure off the real axis:
`‖m_μ(w) - m_μ(z) - (w - z) m_μ'(z)‖ ≤ ‖w - z‖² / (|Im z|² |Im w|) · μ(ℝ)`. -/
theorem norm_resolventTransform_sub_sub_mul_deriv_le {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖resolventTransform μ w - resolventTransform μ z - (w - z) * deriv (resolventTransform μ) z‖
      ≤ ‖w - z‖ ^ 2 / (|z.im| ^ 2 * |w.im|) * μ.real Set.univ := by
  have hrem : resolventTransform μ w - resolventTransform μ z -
      (w - z) * deriv (resolventTransform μ) z =
        ∫ x, (w - z) ^ 2 * (resolvent z x ^ 2 * resolvent w x) ∂μ := by
    rw [(hasDerivAt_resolventTransform_of_im_ne_zero hz).deriv,
      resolventTransform_sub_resolventTransform hw hz, ← integral_const_mul,
      ← integral_const_mul, ← integral_sub]
    · refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      have h := spectrum.resolvent_sub_resolvent (Complex.mem_resolventSet_real hw x)
        (Complex.mem_resolventSet_real hz x)
      linear_combination (w - z) * (resolvent z x) * h
    · exact ((integrable_resolvent_of_im_ne_zero hz).bdd_mul
        (continuous_resolvent_real hw).aestronglyMeasurable
        (ae_of_all _ fun x ↦ Complex.norm_resolvent_real_le w x hw)).const_mul _
    · simpa only [sq] using ((integrable_resolvent_of_im_ne_zero hz).bdd_mul
        (continuous_resolvent_real hz).aestronglyMeasurable
        (ae_of_all _ fun x ↦ Complex.norm_resolvent_real_le z x hz)).const_mul (w - z)
  rw [hrem]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ ?_)
  simp only [norm_mul, norm_pow]
  calc _ ≤ ‖w - z‖ ^ 2 * ((|z.im|⁻¹) ^ 2 * |w.im|⁻¹) := by
        gcongr
        · exact Complex.norm_resolvent_real_le z x hz
        · exact Complex.norm_resolvent_real_le w x hw
    _ = _ := by ring

/-- The difference quotient of the transform of a finite measure off the real axis is close to its
derivative: `‖(w - z)⁻¹ (m_μ(w) - m_μ(z)) - m_μ'(z)‖ ≤ ‖w - z‖ / (|Im z|² |Im w|) · μ(ℝ)`. -/
theorem norm_slope_resolventTransform_sub_deriv_le {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwz : w ≠ z) :
    ‖slope (resolventTransform μ) z w - deriv (resolventTransform μ) z‖ ≤
      ‖w - z‖ / (|z.im| ^ 2 * |w.im|) * μ.real Set.univ := by
  have hwz' : w - z ≠ 0 := sub_ne_zero.2 hwz
  have hrw : slope (resolventTransform μ) z w - deriv (resolventTransform μ) z =
      (w - z)⁻¹ * (resolventTransform μ w - resolventTransform μ z -
        (w - z) * deriv (resolventTransform μ) z) := by
    rw [slope_def_field]
    field_simp
  rw [hrw, norm_mul, norm_inv]
  calc _ ≤ ‖w - z‖⁻¹ * (‖w - z‖ ^ 2 / (|z.im| ^ 2 * |w.im|) * μ.real Set.univ) := by
        gcongr
        exact norm_resolventTransform_sub_sub_mul_deriv_le hz hw
    _ = _ := by field_simp [norm_ne_zero_iff.2 hwz']

/-- A nonzero finite measure has strictly positive imaginary transform in the upper half-plane. -/
theorem im_resolventTransform_pos (hμ : μ ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (resolventTransform μ z).im := by
  have hi := integrable_resolvent_of_im_ne_zero (μ := μ) hz.ne'
  have hp (x : ℝ) : 0 < z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
    exact div_pos hz (by positivity)
  rw [im_resolventTransform]
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) ?_).2
  · simpa [Function.support, ne_of_gt (hp _)] using (Measure.measure_univ_pos.mpr hμ)
  · simpa only [RCLike.im_eq_complex_im, Complex.im_resolvent_real] using hi.im

/-- For the transform of a finite measure and real `t`, the point `z - t m_μ(z)` lies in the upper
half-plane whenever `Im z > 0` and `|t| μ(ℝ) < (Im z)²`. -/
theorem im_sub_mul_resolventTransform_pos {t : ℝ} {z : ℂ} (hz : 0 < z.im)
    (h : |t| * μ.real Set.univ < z.im ^ 2) : 0 < (z - t * resolventTransform μ z).im := by
  have hm := norm_resolventTransform_le (μ := μ) hz.ne'
  rw [abs_of_pos hz] at hm
  have h₁ : t * (resolventTransform μ z).im ≤ |t| * (z.im⁻¹ * μ.real Set.univ) := by
    calc _ ≤ |t * (resolventTransform μ z).im| := le_abs_self _
      _ = |t| * |(resolventTransform μ z).im| := abs_mul _ _
      _ ≤ _ := by gcongr; exact (abs_im_le_norm _).trans hm
  have h₂ : |t| * (z.im⁻¹ * μ.real Set.univ) < z.im := by
    rw [mul_left_comm, ← div_eq_inv_mul, div_lt_iff₀ hz]
    simpa [sq] using h
  simp only [sub_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  linarith

/-- For the transform of a finite measure and real `t`, the map `z ↦ z - t m_μ(z)` is injective on
pairs of points `a`, `b` of the upper half-plane with `|t| μ(ℝ) < Im a Im b`. -/
theorem eq_of_sub_mul_resolventTransform_eq {t : ℝ} {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (h : |t| * μ.real Set.univ < a.im * b.im)
    (hab : a - t * resolventTransform μ a = b - t * resolventTransform μ b) : a = b := by
  by_contra hne
  have hpos : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hlip := norm_resolventTransform_sub_le (μ := μ) ha.ne' hb.ne'
  rw [abs_of_pos ha, abs_of_pos hb] at hlip
  have hab' : a - b = t * (resolventTransform μ a - resolventTransform μ b) := by
    linear_combination hab
  have : ‖a - b‖ ≤ |t| * μ.real Set.univ * (‖a - b‖ / (a.im * b.im)) := by
    calc ‖a - b‖ = |t| * ‖resolventTransform μ a - resolventTransform μ b‖ := by
          rw [hab', norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |t| * (‖a - b‖ / (a.im * b.im) * μ.real Set.univ) := by gcongr
      _ = _ := by ring
  rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
  nlinarith [mul_lt_mul_of_pos_left h hpos]

variable (μ) in
open Filter Topology in
/-- Let `m_μ` be the transform of a finite measure and `t` real. If two functions analytic in the
upper half-plane agree at every point `z - t m_μ(z)` of the upper half-plane with `z` in the upper
half-plane, then they agree on the whole upper half-plane, since near `i ∞` the map
`z ↦ z - t m_μ(z)` is continuous and injective. -/
theorem eqOn_of_eq_sub_mul_resolventTransform (t : ℝ) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {w : ℂ | 0 < w.im}) (hg : AnalyticOnNhd ℂ g {w : ℂ | 0 < w.im})
    (hfg : ∀ z : ℂ, 0 < z.im → 0 < (z - t * resolventTransform μ z).im →
      f (z - t * resolventTransform μ z) = g (z - t * resolventTransform μ z)) :
    Set.EqOn f g {w : ℂ | 0 < w.im} := by
  set r := |t| * μ.real Set.univ + 1
  have hr : 0 < r := by positivity
  have hlt {x y : ℝ} (hx : r < x) (hy : r < y) : |t| * μ.real Set.univ < x * y := by
    have hM : 0 ≤ |t| * μ.real Set.univ := mul_nonneg (abs_nonneg t) measureReal_nonneg
    nlinarith [mul_lt_mul'' hx hy hr.le hr.le]
  have hpos {x : ℂ} (hx : r < x.im) : 0 < (x - t * resolventTransform μ x).im :=
    im_sub_mul_resolventTransform_pos (hr.trans hx) (sq x.im ▸ hlt hx hx)
  set z₀ : ℂ := ⟨0, 2 * r⟩
  have hz₀ : r < z₀.im := show r < 2 * r by linarith
  have hU : {z : ℂ | r < z.im} ∈ 𝓝 z₀ := (isOpen_im_gt _).mem_nhds hz₀
  have hcont : ContinuousAt (fun z : ℂ ↦ z - t * resolventTransform μ z) z₀ :=
    continuousAt_id.sub (continuousAt_const.mul
      (hasDerivAt_resolventTransform_of_im_ne_zero (hr.trans hz₀).ne').continuousAt)
  -- The images of a punctured neighbourhood of `z₀` accumulate at the image of `z₀`.
  have htend : Tendsto (fun z : ℂ ↦ z - t * resolventTransform μ z) (𝓝[≠] z₀)
      (𝓝[≠] (z₀ - t * resolventTransform μ z₀)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with z hz hne
    exact fun h ↦ hne (eq_of_sub_mul_resolventTransform_eq (hr.trans hz) (hr.trans hz₀)
      (hlt hz hz₀) h)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f (z - t * resolventTransform μ z) =
      g (z - t * resolventTransform μ z) := by
    refine Eventually.frequently ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU] with z hz
    exact hfg z (hr.trans hz) (hpos hz)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_im_gt 0).isPreconnected
    (hpos hz₀) (htend.frequently hfreq)

omit [IsFiniteMeasure μ] in
/-- The resolvent transform of the pushforward by a real affine map is obtained by the
corresponding affine change of spectral parameter. The identity holds for arbitrary measures,
without finiteness assumptions. -/
theorem resolventTransform_map_affine (a b : ℝ) (hb : b ≠ 0) (z : ℂ) :
    resolventTransform (μ.map (fun x : ℝ => a + b * x)) z =
      (b : ℂ)⁻¹ * resolventTransform μ ((z - a) / b) := by
  let e : ℝ ≃ᵐ ℝ :=
    ((Homeomorph.mulLeft₀ b hb).trans (Homeomorph.addRight a)).toMeasurableEquiv
  have he : (fun x : ℝ => a + b * x) = e := by
    ext x
    simp [e, Homeomorph.coe_mulLeft₀, add_comm]
  have hkernel (x : ℝ) :
      resolvent z (a + b * x) =
        (b : ℂ)⁻¹ * resolvent ((z - a) / b) x := by
    have hfactor :
        (a : ℂ) + (b : ℂ) * x - z = (b : ℂ) * ((x : ℂ) - (z - a) / b) := by
      field_simp [hb]
      ring
    rw [Complex.resolvent_real_eq_inv, Complex.resolvent_real_eq_inv]
    push_cast
    rw [hfactor, mul_inv_rev]
    ring
  calc
    resolventTransform (μ.map (fun x : ℝ => a + b * x)) z =
        ∫ x, resolvent z (e x) ∂μ := by
          rw [resolventTransform_apply, he, integral_map_equiv]
    _ = ∫ x, resolvent z (a + b * x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => congrArg (resolvent z) (congrFun he x).symm
    _ = ∫ x, (b : ℂ)⁻¹ * resolvent ((z - a) / b) x ∂μ := by
          exact integral_congr_ae (ae_of_all _ hkernel)
    _ = (b : ℂ)⁻¹ * resolventTransform μ ((z - a) / b) := by
          rw [integral_const_mul, resolventTransform_apply]

end MeasureTheory

namespace TauCeti

/-- Off the real axis, `h(x) / (x - z)` is integrable for `h ∈ L¹(μ)`: `|x - z| ≥ |Im z|`. -/
theorem integrable_div_ofReal_sub {μ : Measure ℝ} {h : ℝ → ℂ} (hh : Integrable h μ) {z : ℂ}
    (hz : z.im ≠ 0) : Integrable (fun x : ℝ ↦ h x / ((x : ℂ) - z)) μ :=
  (hh.bdd_mul (Complex.continuous_resolvent_real hz).aestronglyMeasurable
    (.of_forall fun x ↦ Complex.norm_resolvent_real_le z x hz)).congr
      (.of_forall fun x ↦ by simp [resolvent, Ring.inverse_eq_inv', div_eq_mul_inv, mul_comm])

/-- For `h ∈ L¹(μ)`, `x h(x) / (1 + x ^ 2)` is integrable, since `|x| / (1 + x ^ 2) ≤ 1`. -/
theorem integrable_div_one_add_sq_mul {μ : Measure ℝ} {h : ℝ → ℂ} (hh : Integrable h μ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x) μ := by
  refine hh.norm.mono' (((by fun_prop : Measurable fun x : ℝ ↦ (x : ℂ) / (1 + (x : ℂ) ^ 2))
    |>.aestronglyMeasurable).mul hh.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  have h1 : (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, h1, ← ofReal_div, norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  refine mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (by positivity)).2 ?_)
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

end TauCeti
