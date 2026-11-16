/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedNormal.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Gaussian.Support
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of wrapped normal laws

A wrapped normal law with positive variance has the whole circle as its topological support:
the quotient map is continuous and surjective, and its source Gaussian has full support.
At zero variance the support is the singleton containing the circle location.
These statements concern the circle itself, independently of any choice of angle chart.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

/-- The support of a wrapped normal law is the entire circle at positive variance and the
singleton containing its location at zero variance. -/
@[simp]
theorem support_wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) :
    (wrappedNormalMeasure m v).support = if v = 0 then {m} else univ := by
  by_cases hv : v = 0
  · subst v
    simp [Measure.support_dirac]
  · simp only [hv, ite_false]
    rw [wrappedNormalMeasure_def,
      Measure.support_map_eq_closure_range _ (by simp [hv]) (by fun_prop)]
    have hsurj : Function.Surjective (fun x : ℝ ↦ m + (x : AddCircle (2 * π))) :=
      (add_left_surjective m).comp QuotientAddGroup.mk_surjective
    rw [hsurj.range_eq, closure_univ]

end TauCeti.Probability
