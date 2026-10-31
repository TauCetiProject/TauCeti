/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation symmetry of the resolvent transform

The resolvent transform of a real measure satisfies conjugation symmetry. The identity
holds for arbitrary measures, with no finiteness assumption.
-/

public section

noncomputable section

open MeasureTheory

namespace MeasureTheory

/-- Conjugating the spectral parameter conjugates the resolvent transform of a real measure. -/
theorem resolventTransform_conj (μ : Measure ℝ) (z : ℂ) :
    resolventTransform μ (star z) = star (resolventTransform μ z) := by
  rw [resolventTransform_apply, resolventTransform_apply]
  calc
    (∫ x, resolvent (R := ℝ) (star z) x ∂μ) =
        ∫ x, star (resolvent (R := ℝ) z x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            simp [resolvent, Ring.inverse_eq_inv']
    _ = _ := by
      simpa only [RCLike.star_def] using (integral_conj (f := resolvent (R := ℝ) z))

end MeasureTheory
