/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Bernoulli laws

A Bernoulli law is supported on its two atoms when its success probability is strictly
between zero and one. At either endpoint only the atom with nonzero mass remains. The result
is stated for arbitrary atoms in a T₁ space with measurable open sets, so it applies
directly to both native and real-valued Bernoulli variables and also covers coincident atoms.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {X : Type*} [TopologicalSpace X] [T1Space X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The exact topological support of a Bernoulli law, including deterministic success
probabilities and coincident atoms. -/
@[simp]
theorem support_bernoulliMeasure (x y : X) (p : unitInterval) :
    Ber(x, y, p).support =
      if p = 0 then {y} else if p = 1 then {x} else {x, y} := by
  by_cases hp0 : p = 0
  · subst p
    simp [Measure.support_dirac]
  by_cases hp1 : p = 1
  · subst p
    simp [Measure.support_dirac]
  have hpNN : unitInterval.toNNReal p ≠ 0 := by
    intro h
    apply hp0
    ext
    simpa using congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) h
  have hsymmNN : unitInterval.toNNReal (unitInterval.symm p) ≠ 0 := by
    intro h
    apply hp1
    ext
    have hsum := unitInterval.toNNReal_add_toNNReal_symm p
    rw [h, add_zero] at hsum
    simpa using congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hsum
  rw [bernoulliMeasure_def, Measure.support_add]
  -- The decomposition uses the ℝ≥0 action, while the support lemma uses the definitionally
  -- equal ℝ≥0∞ action after coercion.
  change
    ((unitInterval.toNNReal p : ℝ≥0∞) • Measure.dirac x).support ∪
        ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) • Measure.dirac y).support = _
  rw [
    Measure.support_smul_measure _ _ (ENNReal.coe_ne_zero.mpr hpNN),
    Measure.support_smul_measure _ _ (ENNReal.coe_ne_zero.mpr hsymmNN),
    Measure.support_dirac, Measure.support_dirac]
  simp [hp0, hp1, pair_comm]

end TauCeti.Probability
