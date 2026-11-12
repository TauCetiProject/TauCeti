/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

/-!
# Integrability of inverse matrix segments

For real positive-definite matrices `A`, `B`, every entry of
`((1 - t) • A + t • B)⁻¹` is interval integrable over `[0, 1]`. Its quadratic form at any
fixed coordinate vector is interval integrable as well. These facts support integrating
inverse segments, in particular when constructing segment-averaged inverse coefficients.

## Main declarations

* `Matrix.PosDef.intervalIntegrable_inv_segment_apply`: integrability of an inverse entry.
* `Matrix.PosDef.intervalIntegrable_inv_segment_toQuadraticForm'`: integrability of an
  inverse quadratic form.

The statements are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set MeasureTheory in
/-- Every entry of the inverse segment between positive-definite endpoints is interval
integrable on the unit interval. -/
theorem Matrix.PosDef.intervalIntegrable_inv_segment_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (i j : ι) :
    IntervalIntegrable (fun t : ℝ => ((1 - t) • A + t • B)⁻¹ i j) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one (fun t ht => ?_)
  have hc := TauCeti.continuousAt_inv_segment (P := fun _ : ℝ => A) (Q := fun _ : ℝ => B)
    (t := id) continuousAt_const continuousAt_const continuousAt_id hA hB ht
  exact ((continuous_apply_apply i j).continuousAt.comp hc).continuousWithinAt

/-- The inverse segment's quadratic form is interval integrable for positive-definite endpoints. -/
theorem Matrix.PosDef.intervalIntegrable_inv_segment_toQuadraticForm'
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (ξ : ι → ℝ) :
    IntervalIntegrable
      (fun t : ℝ => (((1 - t) • A + t • B)⁻¹).toQuadraticForm' ξ)
      MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one (fun t ht => ?_)
  have hc := TauCeti.continuousAt_inv_segment (P := fun _ : ℝ => A) (Q := fun _ : ℝ => B)
    (t := id) continuousAt_const continuousAt_const continuousAt_id hA hB ht
  have hq : Continuous (fun M : Matrix ι ι ℝ => M.toQuadraticForm' ξ) := by
    simp only [Matrix.toQuadraticForm'_apply]
    fun_prop
  exact (hq.continuousAt.comp hc).continuousWithinAt
