/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Fin.PartialSums
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Partial sums preserve Lebesgue measure

The partial-sum linear equivalence on real tuples preserves product Lebesgue measure,
since its determinant is one. This is the change of variables between increments and
cumulative coordinates.
-/

public section

open MeasureTheory

namespace TauCeti

/-- Taking nonempty initial sums of a real tuple preserves Lebesgue measure. -/
theorem measurePreserving_partialSumsLinearEquiv (n : ℕ) :
    MeasurePreserving (partialSumsLinearEquiv ℝ n) volume volume := by
  refine ⟨(partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  simpa only [coe_partialSumsLinearEquiv, det_partialSumsLinearMap, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using
    (Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := partialSumsLinearMap ℝ n) (by simp))

end TauCeti
