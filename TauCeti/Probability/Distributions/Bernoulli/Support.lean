/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Bernoulli laws

The support of `bernoulliMeasure x y p` consists of the outcomes whose weights are nonzero.
Thus it is `{y}` at success probability zero, `{x}` at success probability one, and `{x, y}`
in the interior. This description also covers coincident outcomes.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set unitInterval

namespace TauCeti.Probability

variable {X : Type*} [TopologicalSpace X] [T1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The exact topological support of a Bernoulli law, including both deterministic parameter
boundaries and coincident outcomes. -/
@[simp]
theorem support_bernoulliMeasure (x y : X) (p : unitInterval) :
    Ber(x, y, p).support = if p = 0 then {y} else if p = 1 then {x} else {x, y} := by
  by_cases hp0 : p = 0
  · simp [hp0, Measure.support_dirac]
  by_cases hp1 : p = 1
  · simp [hp1, Measure.support_dirac]
  have hp0' : unitInterval.toNNReal p ≠ 0 := by
    simp only [ne_eq, NNReal.eq_iff, unitInterval.coe_toNNReal, NNReal.coe_zero]
    exact fun h ↦ hp0 (Subtype.ext h)
  have hp1' : unitInterval.toNNReal (σ p) ≠ 0 := by
    simp only [ne_eq, NNReal.eq_iff, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, NNReal.coe_zero, sub_eq_zero]
    exact fun h ↦ hp1 (Subtype.ext h.symm)
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, Measure.support_add,
    Measure.support_smul_measure _ _ (by exact_mod_cast hp0'),
    Measure.support_smul_measure _ _ (by exact_mod_cast hp1'),
    Measure.support_dirac, Measure.support_dirac]
  simpa [hp0, hp1] using Set.pair_comm y x

end TauCeti.Probability
