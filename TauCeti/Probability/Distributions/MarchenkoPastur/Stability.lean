/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.ResolventTransform
public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.Probability.Distributions.MarchenkoPastur.Continuity
import TauCeti.Basic.Complex.OfRealSub

/-!
# Stability of the Marchenko–Pastur equation

Write `P(y,z,w) = y z w² + (z+y-1)w + 1` and `m = m_{MP_y}(z)`, with the resolvent convention
`m_μ(z) = ∫ (x-z)⁻¹ dμ(x)`. For `Im z > 0`, a small residual `P(y,z,w)` forces every `w` in the
closed upper half-plane to be close to `m`. In particular there is no extra boundedness or
tightness hypothesis on the approximate solutions. The estimate also applies when `y = 0`,
where the equation becomes linear and the law is `δ₁`.

The key factorization is
`P(y,z,w) = z (w-m) (y w - (z m)⁻¹)`.
Since `Im (z m) > 0`, the imaginary part of the last factor is bounded below by the positive
number `-Im ((z m)⁻¹)`, uniformly over `Im w ≥ 0`. This gives a quantitative residual estimate.
Weak continuity of `MP_y` then permits varying aspect ratios, including passage through `y = 1`
and to `y = 0`.

The consuming results identify weak limits of deterministic and random probability measures
from vanishing residuals, on a determining set of spectral parameters. They do not assume the
self-consistent equation: probabilistic matrix arguments must establish its residual estimate.

## References

* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.3.1.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

variable {y : ℝ≥0} {z w : ℂ}

private lemma neg_im_inv_mul_resolventTransform_marchenkoPastur_pos (hz : 0 < z.im) :
    0 < -((z * resolventTransform (marchenkoPastur y) z)⁻¹).im := by
  have h := im_mul_resolventTransform_marchenkoPastur_pos (y := y) hz
  have hne : z * resolventTransform (marchenkoPastur y) z ≠ 0 := by
    intro heq
    simp [heq] at h
  simp only [inv_im, neg_div, neg_neg]
  exact div_pos h (normSq_pos.mpr hne)

private lemma marchenkoPastur_quadratic_factor (hz : 0 < z.im) :
    (y : ℂ) * z * (w * w) + (z + y - 1) * w + 1 =
      z * (w - resolventTransform (marchenkoPastur y) z) *
        ((y : ℂ) * w - (z * resolventTransform (marchenkoPastur y) z)⁻¹) := by
  set m := resolventTransform (marchenkoPastur y) z
  have hq := resolventTransform_marchenkoPastur_quadratic_eq_zero (y := y)
    (notMem_image_ofReal_of_im_ne_zero hz.ne')
  have hpos : 0 < (z * m).im := im_mul_resolventTransform_marchenkoPastur_pos (y := y) hz
  have hne : z * m ≠ 0 := by
    intro heq
    simp [heq] at hpos
  have hi := mul_inv_cancel₀ hne
  apply mul_right_cancel₀ hne
  linear_combination z * w * hq + z * (w - m) * hi

/-- **Stability of the Marchenko–Pastur equation.** At an upper-half-plane spectral parameter,
the distance from any point in the closed upper half-plane to the Marchenko–Pastur transform
is bounded by its quadratic residual divided by a strictly positive constant. This includes
the linear equation at `y = 0`. -/
theorem norm_sub_resolventTransform_marchenkoPastur_le (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    ‖w - resolventTransform (marchenkoPastur y) z‖ ≤
      ‖(y : ℂ) * z * (w * w) + (z + y - 1) * w + 1‖ /
        (‖z‖ * -((z * resolventTransform (marchenkoPastur y) z)⁻¹).im) := by
  have hc := neg_im_inv_mul_resolventTransform_marchenkoPastur_pos (y := y) hz
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hz
  have hbound : -((z * resolventTransform (marchenkoPastur y) z)⁻¹).im ≤
      ‖(y : ℂ) * w - (z * resolventTransform (marchenkoPastur y) z)⁻¹‖ := by
    calc -((z * resolventTransform (marchenkoPastur y) z)⁻¹).im
        ≤ ((y : ℂ) * w - (z * resolventTransform (marchenkoPastur y) z)⁻¹).im := by
          simp only [sub_im, im_ofReal_mul]
          nlinarith [y.coe_nonneg]
      _ ≤ _ := im_le_norm _
  rw [le_div_iff₀ (mul_pos (norm_pos_iff.mpr hz0) hc),
    marchenkoPastur_quadratic_factor hz, norm_mul, norm_mul]
  calc _ = ‖z‖ * ‖w - resolventTransform (marchenkoPastur y) z‖ *
        -((z * resolventTransform (marchenkoPastur y) z)⁻¹).im := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

section ApproximateSolutions

variable {ι : Type*} {l : Filter ι} {ys : ι → ℝ≥0}

/-- Convergence to the Marchenko–Pastur transform is equivalent to a vanishing quadratic
residual for approximate solutions in the closed upper half-plane, with a convergent aspect
ratio. No bound on the approximate solutions is required. -/
theorem tendsto_resolventTransform_marchenkoPastur_iff_quadratic_tendsto_zero
    {ws : ι → ℂ} (hz : 0 < z.im) (hy : Tendsto ys l (𝓝 y))
    (hw : ∀ᶠ i in l, 0 ≤ (ws i).im) :
    Tendsto ws l (𝓝 (resolventTransform (marchenkoPastur y) z)) ↔
      Tendsto (fun i ↦ (ys i : ℂ) * z * (ws i * ws i) +
        (z + ys i - 1) * ws i + 1) l (𝓝 0) := by
  constructor
  · intro h
    have hyc : Tendsto (fun i ↦ (ys i : ℂ)) l (𝓝 (y : ℂ)) :=
      (continuous_ofReal.tendsto _).comp ((NNReal.continuous_coe.tendsto _).comp hy)
    have hq := resolventTransform_marchenkoPastur_quadratic_eq_zero (y := y)
      (notMem_image_ofReal_of_im_ne_zero hz.ne')
    simpa only [hq] using (((hyc.mul_const z).mul (h.mul h)).add
      (((hyc.const_add z).sub_const 1).mul h)).add_const 1
  intro h
  have hm : Tendsto (fun i ↦ resolventTransform (marchenkoPastur (ys i)) z) l
      (𝓝 (resolventTransform (marchenkoPastur y) z)) := by
    simpa only [Function.comp_def, Measure.coe_toProbabilityMeasure] using
      ProbabilityMeasure.tendsto_resolventTransform_of_tendsto
        (continuous_marchenkoPastur.continuousAt.tendsto.comp hy) hz.ne'
  have hc := neg_im_inv_mul_resolventTransform_marchenkoPastur_pos (y := y) hz
  have hc_ne : (z * resolventTransform (marchenkoPastur y) z)⁻¹.im ≠ 0 := by
    linarith
  have hzm_ne : z * resolventTransform (marchenkoPastur y) z ≠ 0 := by
    intro heq
    have hpos := im_mul_resolventTransform_marchenkoPastur_pos (y := y) hz
    simp [heq] at hpos
  have hi := (hm.const_mul z).inv₀ hzm_ne
  have hden := (((continuous_im.tendsto _).comp hi).neg).const_mul ‖z‖
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hz
  have he : Tendsto (fun i ↦ ws i - resolventTransform (marchenkoPastur (ys i)) z) l (𝓝 0) := by
    refine squeeze_zero_norm' (hw.mono fun i hi ↦
      norm_sub_resolventTransform_marchenkoPastur_le hz hi) ?_
    simpa only [Pi.div_def, Function.comp_def, norm_zero, zero_div] using
      h.norm.div hden (mul_ne_zero (norm_ne_zero_iff.mpr hz0) (neg_ne_zero.mpr hc_ne))
  simpa only [sub_add_cancel, zero_add] using he.add hm

end ApproximateSolutions

variable {ys : ℕ → ℝ≥0}

/-- Weak convergence to a Marchenko–Pastur law is equivalent to vanishing quadratic residuals
on an upper-half-plane determining set. The aspect ratio may tend to zero. -/
theorem tendsto_marchenkoPastur_iff_quadratic_tendsto_zero_of_subset_closure
    {μs : ℕ → ProbabilityMeasure ℝ} {D : Set ℂ} (hy : Tendsto ys atTop (𝓝 y))
    (hDupper : D ⊆ {z : ℂ | 0 < z.im}) (hD : {z : ℂ | 0 < z.im} ⊆ closure D) :
    Tendsto μs atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) ↔
      ∀ z ∈ D, Tendsto (fun i ↦
        (ys i : ℂ) * z * (resolventTransform (μs i : Measure ℝ) z *
          resolventTransform (μs i : Measure ℝ) z) +
        (z + ys i - 1) * resolventTransform (μs i : Measure ℝ) z + 1) atTop (𝓝 0) := by
  have he (z : ℂ) (hz : z ∈ D) :=
    tendsto_resolventTransform_marchenkoPastur_iff_quadratic_tendsto_zero (hDupper hz) hy
      (Eventually.of_forall fun i ↦ (im_resolventTransform_pos
        (IsProbabilityMeasure.ne_zero (μs i : Measure ℝ)) (hDupper hz)).le)
  constructor
  · intro h z hz
    apply (he z hz).1
    simpa only [Measure.coe_toProbabilityMeasure] using
      ProbabilityMeasure.tendsto_resolventTransform_of_tendsto h (hDupper hz).ne'
  · intro h
    apply ProbabilityMeasure.tendsto_of_tendsto_resolventTransform_of_subset_closure hD
    intro z hz
    simpa only [Measure.coe_toProbabilityMeasure] using (he z hz).2 (h z hz)

/-- Weak Marchenko–Pastur convergence is equivalent to vanishing quadratic residuals at every
upper-half-plane parameter. The input measures need not have moments or nonnegative support. -/
theorem tendsto_marchenkoPastur_iff_quadratic_tendsto_zero
    {μs : ℕ → ProbabilityMeasure ℝ} (hy : Tendsto ys atTop (𝓝 y)) :
    Tendsto μs atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) ↔
      ∀ z : ℂ, 0 < z.im → Tendsto (fun i ↦
        (ys i : ℂ) * z * (resolventTransform (μs i : Measure ℝ) z *
          resolventTransform (μs i : Measure ℝ) z) +
        (z + ys i - 1) * resolventTransform (μs i : Measure ℝ) z + 1) atTop (𝓝 0) :=
  tendsto_marchenkoPastur_iff_quadratic_tendsto_zero_of_subset_closure hy Subset.rfl subset_closure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost-sure Marchenko–Pastur convergence is equivalent to almost-sure vanishing of each
residual on a determining set. The set need not be countable and exceptional null sets may
depend on the spectral parameter. No independence across indices is assumed. -/
theorem ae_tendsto_marchenkoPastur_iff_ae_quadratic_tendsto_zero_of_subset_closure
    {μs : ℕ → Ω → ProbabilityMeasure ℝ} {D : Set ℂ} (hy : Tendsto ys atTop (𝓝 y))
    (hDupper : D ⊆ {z : ℂ | 0 < z.im}) (hD : {z : ℂ | 0 < z.im} ⊆ closure D) :
    (∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure)) ↔
      ∀ z ∈ D, ∀ᵐ ω ∂P, Tendsto (fun i ↦
        (ys i : ℂ) * z * (resolventTransform (μs i ω : Measure ℝ) z *
          resolventTransform (μs i ω : Measure ℝ) z) +
        (z + ys i - 1) * resolventTransform (μs i ω : Measure ℝ) z + 1) atTop (𝓝 0) := by
  constructor
  · intro h z hz
    filter_upwards [h] with ω hω
    exact (tendsto_marchenkoPastur_iff_quadratic_tendsto_zero_of_subset_closure
      hy hDupper hD).1 hω z hz
  · intro h
    obtain ⟨E, hED, hEc, hDE⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace D).exists_countable_dense_subset
    have hE : {z : ℂ | 0 < z.im} ⊆ closure E :=
      hD.trans (closure_minimal hDE isClosed_closure)
    filter_upwards [(ae_ball_iff hEc).2 (fun z hz ↦ h z (hED hz))] with ω hω
    exact (tendsto_marchenkoPastur_iff_quadratic_tendsto_zero_of_subset_closure
      hy (hED.trans hDupper) hE).2 hω

/-- Almost-sure weak Marchenko–Pastur convergence is equivalent to residuals vanishing almost
surely at each upper-half-plane parameter. No measurability of the random measures is required. -/
theorem ae_tendsto_marchenkoPastur_iff_ae_quadratic_tendsto_zero
    {μs : ℕ → Ω → ProbabilityMeasure ℝ} (hy : Tendsto ys atTop (𝓝 y)) :
    (∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure)) ↔
      ∀ z : ℂ, 0 < z.im → ∀ᵐ ω ∂P, Tendsto (fun i ↦
        (ys i : ℂ) * z * (resolventTransform (μs i ω : Measure ℝ) z *
          resolventTransform (μs i ω : Measure ℝ) z) +
        (z + ys i - 1) * resolventTransform (μs i ω : Measure ℝ) z + 1) atTop (𝓝 0) :=
  ae_tendsto_marchenkoPastur_iff_ae_quadratic_tendsto_zero_of_subset_closure
    hy Subset.rfl subset_closure

end TauCeti.Probability
