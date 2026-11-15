/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedCauchy.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Cauchy.Support
import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of wrapped Cauchy laws

A wrapped Cauchy law with positive scale has the whole circle as its topological support.
At zero scale its support is the singleton containing its location. These are supports on the
circle itself, independently of any choice of real angle representatives.

The result follows from `TauCeti.Probability.support_cauchyMeasure` and
`MeasureTheory.Measure.support_map_eq_closure_range`: the quotient followed by a rotation is
a continuous surjection from the real line onto the circle.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

/-- The support of a wrapped Cauchy law is the whole circle at nonzero scale and the location
singleton at zero scale. -/
@[simp]
theorem support_wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    (wrappedCauchyMeasure m γ).support = if γ = 0 then {m} else univ := by
  by_cases hγ : γ = 0
  · subst γ
    simp
  · simp only [hγ, ↓reduceIte]
    rw [wrappedCauchyMeasure_def, Measure.support_map_eq_closure_range _
      (by simp [hγ]) (by fun_prop)]
    have hsurj : Function.Surjective (fun x : ℝ ↦ m + (x : AddCircle (2 * π))) :=
      (Equiv.addLeft m).surjective.comp QuotientAddGroup.mk_surjective
    rw [hsurj.range_eq, closure_univ]

end TauCeti.Probability
