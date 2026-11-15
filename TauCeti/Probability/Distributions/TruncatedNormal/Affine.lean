/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Affine transport of truncated Gaussian laws

An invertible affine map transports a truncated Gaussian by transforming both its Gaussian
parameters and its truncation event. The event formulation works for unbounded intervals as
well as bounded ones, and retains endpoint atoms when the variance is zero. For finite
intervals, positive slopes preserve endpoint flags, whereas negative slopes reverse them.
No positive-mass assumption is needed: a zero conditional measure stays zero.

The transport uses `ProbabilityTheory.map_cond_preimage` and Mathlib's Gaussian translation
and scaling identities. For background on the truncated normal distribution, see
Johnson, Kotz and Balakrishnan, *Continuous Univariate Distributions*, volume 1, chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- Affine transport commutes with Gaussian truncation on the preimage of a measurable event.
This formulation also allows a zero slope and a zero variance. -/
theorem map_affine_truncatedNormalMeasure_preimage (m : ℝ) (v : ℝ≥0) (a b : ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (truncatedNormalMeasure m v ((fun x ↦ a + b * x) ⁻¹' s)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v) s := by
  have hf : Measurable (fun x : ℝ ↦ a + b * x) := by fun_prop
  rw [truncatedNormalMeasure_def, truncatedNormalMeasure_def]
  exact map_cond_preimage hf one_ne_zero ENNReal.one_ne_top
    (fun A hA ↦ by
      rw [← Measure.map_apply hf hA, gaussianReal_map_const_add_const_mul, one_mul]) hs

/-- An invertible affine image of a truncated Gaussian transforms the underlying Gaussian's
location and variance parameters and the truncation event, including zero-mass cases. -/
theorem map_affine_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) :
    (truncatedNormalMeasure m v s).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        ((fun x ↦ a + b * x) '' s) := by
  have hf : MeasurableEmbedding (fun x : ℝ ↦ a + b * x) := by
    convert (affineHomeomorph b a hb).measurableEmbedding using 1
    ext x
    simp [affineHomeomorph, add_comm]
  simpa only [preimage_image_eq s hf.injective] using
    map_affine_truncatedNormalMeasure_preimage m v a b (hf.measurableSet_image.mpr hs)

/-- Positive affine transport preserves both closed endpoints. -/
theorem map_affine_truncatedNormalMeasure_Icc_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Icc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * l) (a + b * r)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Icc (a + b * l) (a + b * r) = Icc l r := by
    ext x
    simp [mul_le_mul_iff_right₀ hb]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Icc (a + b * l) (a + b * r)) measurableSet_Icc

/-- Positive affine transport preserves both open endpoints. -/
theorem map_affine_truncatedNormalMeasure_Ioo_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioo l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * l) (a + b * r)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ioo (a + b * l) (a + b * r) = Ioo l r := by
    ext x
    simp [mul_lt_mul_iff_right₀ hb]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ioo (a + b * l) (a + b * r)) measurableSet_Ioo

/-- Positive affine transport preserves a closed lower and open upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ico_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ico l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * l) (a + b * r)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ico (a + b * l) (a + b * r) = Ico l r := by
    ext x
    simp [mul_le_mul_iff_right₀ hb, mul_lt_mul_iff_right₀ hb]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ico (a + b * l) (a + b * r)) measurableSet_Ico

/-- Positive affine transport preserves an open lower and closed upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ioc_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * l) (a + b * r)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ioc (a + b * l) (a + b * r) = Ioc l r := by
    ext x
    simp [mul_le_mul_iff_right₀ hb, mul_lt_mul_iff_right₀ hb]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ioc (a + b * l) (a + b * r)) measurableSet_Ioc

/-- Negative affine transport reverses the endpoints of a closed interval. -/
theorem map_affine_truncatedNormalMeasure_Icc_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Icc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * r) (a + b * l)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Icc (a + b * r) (a + b * l) = Icc l r := by
    ext x
    simp [mul_le_mul_left_of_neg hb, and_comm]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Icc (a + b * r) (a + b * l)) measurableSet_Icc

/-- Negative affine transport reverses the endpoints of an open interval. -/
theorem map_affine_truncatedNormalMeasure_Ioo_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioo l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * r) (a + b * l)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ioo (a + b * r) (a + b * l) = Ioo l r := by
    ext x
    simp [mul_lt_mul_left_of_neg hb, and_comm]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ioo (a + b * r) (a + b * l)) measurableSet_Ioo

/-- Negative affine transport exchanges a closed lower and open upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ico_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ico l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * r) (a + b * l)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ioc (a + b * r) (a + b * l) = Ico l r := by
    ext x
    simp [mul_le_mul_left_of_neg hb, mul_lt_mul_left_of_neg hb, and_comm]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ioc (a + b * r) (a + b * l)) measurableSet_Ioc

/-- Negative affine transport exchanges an open lower and closed upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ioc_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * r) (a + b * l)) := by
  have hpre : (fun x : ℝ ↦ a + b * x) ⁻¹' Ico (a + b * r) (a + b * l) = Ioc l r := by
    ext x
    simp [mul_le_mul_left_of_neg hb, mul_lt_mul_left_of_neg hb, and_comm]
  simpa only [hpre] using map_affine_truncatedNormalMeasure_preimage m v a b
    (s := Ico (a + b * r) (a + b * l)) measurableSet_Ico

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- An invertible affine function of a truncated Gaussian variable has the corresponding
truncated Gaussian law, with the truncation event transported as well. -/
theorem affine_truncatedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} {s : Set ℝ}
    (hX : HasLaw X (truncatedNormalMeasure m v s) P) (a : ℝ) {b : ℝ}
    (hb : b ≠ 0) (hs : MeasurableSet s) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        ((fun x ↦ a + b * x) '' s)) P := by
  have hf : HasLaw (fun x : ℝ ↦ a + b * x)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        ((fun x ↦ a + b * x) '' s)) (truncatedNormalMeasure m v s) :=
    ⟨by fun_prop, map_affine_truncatedNormalMeasure m v a hb hs⟩
  exact hf.comp hX

end ProbabilityTheory.HasLaw
