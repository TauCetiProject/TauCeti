/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Interval integrability of the derivative of a `C¹` function

The derivative of a function that is `C¹` on `[[a, b]]` is interval-integrable on `a..b`. The
within-interval derivative is continuous on the compact interval, and it agrees with `deriv`
on the interior, hence almost everywhere.

## Provenance

Adapted from `ClosedPwC1Curve.deriv_intervalIntegrable_piece` in the AINTLIB
`LeanModularForms` development's `PaperPwC1Immersion.lean`, restated for an arbitrary function.
-/

public section

open MeasureTheory Set
open scoped ContDiff

/-- The derivative of a function that is `C¹` on `[[a, b]]` is interval-integrable on `a..b`. -/
theorem ContDiffOn.intervalIntegrable_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f (uIcc a b)) (hn : 1 ≤ n) :
    IntervalIntegrable (deriv f) volume a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact IntervalIntegrable.refl
  have hlt : min a b < max a b := min_lt_max.mpr hab
  rw [← Icc_min_max] at hf
  have hint : IntervalIntegrable (derivWithin f (Icc (min a b) (max a b))) volume a b :=
    ((hf.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) hn).mono
      Icc_min_max.symm.subset).intervalIntegrable
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr ?_
  rw [uIoc, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
