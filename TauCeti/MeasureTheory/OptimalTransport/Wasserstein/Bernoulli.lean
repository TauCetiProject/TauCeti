/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Finite moments of Bernoulli measures

A two-point law on a pseudometric space has finite moments at every exponent, including infinity.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

/-- A Bernoulli law has finite moments at every exponent, including infinity. -/
theorem hasFiniteMoment_bernoulliMeasure {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (p : ℝ≥0∞) (x y : X) (t : unitInterval) :
    HasFiniteMoment p (bernoulliMeasure x y t) := by
  classical
  apply hasFiniteMoment_of_ae_mem_finset (s := {x, y}) x
  apply mem_ae_iff.mpr
  simp [bernoulliMeasure_def]

end TauCeti
