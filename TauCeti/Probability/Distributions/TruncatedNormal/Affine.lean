/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Affine

/-!
# Affine transport of truncated Gaussian laws

An invertible affine map transports a truncated Gaussian by transforming both its Gaussian
parameters and its truncation event, without requiring the event to be measurable. The event
formulation works for unbounded intervals as well as bounded ones, and retains endpoint atoms when
the variance is zero. For finite intervals, positive slopes preserve endpoint flags, whereas
negative slopes reverse them. No positive-mass assumption is needed: a zero conditional measure
stays zero.

The identities combine general affine truncation transport (`TauCeti.Probability.map_affine_cond`,
`TauCeti.Probability.map_affine_cond_preimage`, and their interval specializations) with Gaussian
affine pushforward (`TauCeti.Probability.gaussianReal_map_const_add_const_mul`). For background on
the truncated normal distribution, see Johnson, Kotz and Balakrishnan, *Continuous Univariate
Distributions*, volume 1, chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- Affine transport commutes with Gaussian truncation on the preimage of an arbitrary event,
without requiring the event to be measurable. This formulation also allows a zero slope and a
zero variance. -/
theorem map_affine_truncatedNormalMeasure_preimage (m : ℝ) (v : ℝ≥0) (a b : ℝ) (s : Set ℝ) :
    (truncatedNormalMeasure m v ((fun x ↦ a + b * x) ⁻¹' s)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v) s := by
  rw [truncatedNormalMeasure_def, map_affine_cond_preimage a b,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- An invertible affine image of a truncated Gaussian transforms the underlying Gaussian's
location and variance parameters and the truncation event, without requiring the event to be
measurable and including zero-mass cases. -/
theorem map_affine_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b ≠ 0) {s : Set ℝ} :
    (truncatedNormalMeasure m v s).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        ((fun x ↦ a + b * x) '' s) := by
  rw [truncatedNormalMeasure_def, map_affine_cond a hb, gaussianReal_map_const_add_const_mul,
    truncatedNormalMeasure_def]

/-- Positive affine transport preserves both closed endpoints. -/
theorem map_affine_truncatedNormalMeasure_Icc_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Icc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * l) (a + b * r)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Icc_pos a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Positive affine transport preserves both open endpoints. -/
theorem map_affine_truncatedNormalMeasure_Ioo_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioo l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * l) (a + b * r)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ioo_pos a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Positive affine transport preserves a closed lower and open upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ico_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ico l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * l) (a + b * r)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ico_pos a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Positive affine transport preserves an open lower and closed upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ioc_pos (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * l) (a + b * r)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ioc_pos a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Negative affine transport reverses the endpoints of a closed interval. -/
theorem map_affine_truncatedNormalMeasure_Icc_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Icc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * r) (a + b * l)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Icc_neg a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Negative affine transport reverses the endpoints of an open interval. -/
theorem map_affine_truncatedNormalMeasure_Ioo_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioo l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * r) (a + b * l)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ioo_neg a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Negative affine transport exchanges a closed lower and open upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ico_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ico l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * r) (a + b * l)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ico_neg a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

/-- Negative affine transport exchanges an open lower and closed upper endpoint. -/
theorem map_affine_truncatedNormalMeasure_Ioc_neg (m : ℝ) (v : ℝ≥0) (a : ℝ) {b : ℝ}
    (hb : b < 0) (l r : ℝ) :
    (truncatedNormalMeasure m v (Ioc l r)).map (fun x ↦ a + b * x) =
      truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * r) (a + b * l)) := by
  rw [truncatedNormalMeasure_def, map_affine_cond_Ioc_neg a hb l r,
    gaussianReal_map_const_add_const_mul, truncatedNormalMeasure_def]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- An invertible affine function of a truncated Gaussian variable has the corresponding
truncated Gaussian law, with the truncation event transported as well and without requiring the
event to be measurable. -/
theorem affine_truncatedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} {s : Set ℝ}
    (hX : HasLaw X (truncatedNormalMeasure m v s) P) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        ((fun x ↦ a + b * x) '' s)) P := by
  rw [truncatedNormalMeasure_def] at hX ⊢
  rw [← gaussianReal_map_const_add_const_mul]
  exact hX.affine_cond a hb

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a closed interval,
then `a + b * X` for `0 < b` has the truncated Gaussian law with location `a + b * m`, variance
`v` scaled by `b ^ 2`, and closed interval with endpoints `a + b * l` and `a + b * r`. -/
theorem affine_truncatedNormalMeasure_Icc_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Icc l r)) P)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * l) (a + b * r))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Icc_pos m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to an open interval,
then `a + b * X` for `0 < b` has the truncated Gaussian law with location `a + b * m`, variance
`v` scaled by `b ^ 2`, and open interval with endpoints `a + b * l` and `a + b * r`. -/
theorem affine_truncatedNormalMeasure_Ioo_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ioo l r)) P)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * l) (a + b * r))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ioo_pos m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a lower-closed,
upper-open interval, then `a + b * X` for `0 < b` has the truncated Gaussian law with location
`a + b * m`, variance `v` scaled by `b ^ 2`, and the same endpoint conventions at `a + b * l` and
`a + b * r`. -/
theorem affine_truncatedNormalMeasure_Ico_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ico l r)) P)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * l) (a + b * r))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ico_pos m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a lower-open,
upper-closed interval, then `a + b * X` for `0 < b` has the truncated Gaussian law with location
`a + b * m`, variance `v` scaled by `b ^ 2`, and the same endpoint conventions at `a + b * l` and
`a + b * r`. -/
theorem affine_truncatedNormalMeasure_Ioc_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ioc l r)) P)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * l) (a + b * r))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ioc_pos m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a closed interval,
then `a + b * X` for `b < 0` has the truncated Gaussian law with location `a + b * m`, variance
`v` scaled by `b ^ 2`, and closed interval with reversed endpoints `a + b * r` and `a + b * l`. -/
theorem affine_truncatedNormalMeasure_Icc_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Icc l r)) P)
    (a : ℝ) {b : ℝ} (hb : b < 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Icc (a + b * r) (a + b * l))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Icc_neg m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to an open interval,
then `a + b * X` for `b < 0` has the truncated Gaussian law with location `a + b * m`, variance
`v` scaled by `b ^ 2`, and open interval with reversed endpoints `a + b * r` and `a + b * l`. -/
theorem affine_truncatedNormalMeasure_Ioo_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ioo l r)) P)
    (a : ℝ) {b : ℝ} (hb : b < 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioo (a + b * r) (a + b * l))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ioo_neg m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a lower-closed,
upper-open interval, then `a + b * X` for `b < 0` has the truncated Gaussian law with location
`a + b * m`, variance `v` scaled by `b ^ 2`, and the lower-open, upper-closed interval with reversed
endpoints `a + b * r` and `a + b * l`. -/
theorem affine_truncatedNormalMeasure_Ico_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ico l r)) P)
    (a : ℝ) {b : ℝ} (hb : b < 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ioc (a + b * r) (a + b * l))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ico_neg m v a hb l r)).fun_comp hX

/-- If `X` has a Gaussian law with location `m` and variance `v` truncated to a lower-open,
upper-closed interval, then `a + b * X` for `b < 0` has the truncated Gaussian law with location
`a + b * m`, variance `v` scaled by `b ^ 2`, and the lower-closed, upper-open interval with reversed
endpoints `a + b * r` and `a + b * l`. -/
theorem affine_truncatedNormalMeasure_Ioc_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (truncatedNormalMeasure m v (Ioc l r)) P)
    (a : ℝ) {b : ℝ} (hb : b < 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (truncatedNormalMeasure (a + b * m) (NNReal.mk (b ^ 2) (sq_nonneg b) * v)
        (Ico (a + b * r) (a + b * l))) P :=
  (HasLaw.mk (by fun_prop) (map_affine_truncatedNormalMeasure_Ioc_neg m v a hb l r)).fun_comp hX

end ProbabilityTheory.HasLaw
