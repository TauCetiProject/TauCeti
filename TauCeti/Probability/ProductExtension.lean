/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw

/-!
# Extending a probability space by an independent coordinate

If a random variable has law `μ` under a probability measure `P`, adjoining a new coordinate with
law `ν` gives the pair the product law `μ.prod ν`. In particular, this preserves the full law of
an old random state (which may itself be a tuple) and makes the new coordinate independent of it.
This implements RandomMatrices roadmap section 0.1, Product extensions.
-/

public section

namespace ProbabilityTheory

open MeasureTheory

variable {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace E]
  {X : Ω → α} {μ : Measure α} {P : Measure Ω} {ν : Measure E}

/-- Adjoining a coordinate with law `ν` to a probability space preserves the law of an existing
random variable and gives the pair the product law. Taking the old random variable to be a tuple
preserves its joint law with all of its components. -/
theorem HasLaw.prod_extension (hX : HasLaw X μ P) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] :
    HasLaw (fun z : Ω × E => (X z.1, z.2)) (μ.prod ν) (P.prod ν) := by
  refine ⟨hX.aemeasurable.prodMap measurable_id.aemeasurable, ?_⟩
  change Measure.map (Prod.map X id) (P.prod ν) = μ.prod ν
  rw [← Measure.map_prod_map_of_aemeasurable P ν hX.aemeasurable measurable_id.aemeasurable,
    hX.map_eq, Measure.map_id]

end ProbabilityTheory
