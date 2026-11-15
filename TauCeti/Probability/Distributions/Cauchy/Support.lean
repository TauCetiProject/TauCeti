/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Cauchy.PDF

/-!
# Topological support of the Cauchy distribution

A nondegenerate Cauchy density is positive everywhere, while the zero-scale boundary is a Dirac
measure. This file gives the exact support in both cases.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The support of a Cauchy law is the whole line at nonzero scale and the location singleton at
zero scale. -/
@[simp]
theorem support_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) :
    (cauchyMeasure x₀ γ).support = if γ = 0 then {x₀} else Set.univ := by
  by_cases hγ : γ = 0
  · subst γ
    simp [cauchyMeasure_zero_scale]
  · simp only [hγ, ↓reduceIte]
    rw [cauchyMeasure_of_scale_ne_zero x₀ hγ]
    calc
      (volume.withDensity (cauchyPDF x₀ γ)).support = closure Set.univ :=
        Measure.support_withDensity_eq_closure (measurable_cauchyPDF x₀ γ) isOpen_univ (by
          ext x
          simp only [Function.mem_support, Set.mem_univ, iff_true, cauchyPDF_def,
            ENNReal.ofReal_ne_zero_iff]
          exact cauchyPDF_pos x₀ hγ x)
      _ = Set.univ := closure_univ

end TauCeti.Probability
