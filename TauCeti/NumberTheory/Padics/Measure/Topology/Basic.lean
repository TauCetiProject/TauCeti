/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology

/-!
# Evaluation in the weak topology of measures

Evaluation on any fixed continuous test is weakly continuous.
`AbstractMeasure.continuous_weak_iff` characterizes weak continuity by continuity on each test.
-/

public section

open ContinuousMap

namespace AbstractMeasure

variable {X R E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]

/-- Evaluation of a measure on a fixed continuous test is weakly continuous. -/
theorem continuous_apply_weak [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module R E] (f : C(X, R)) :
    @Continuous _ E WeakTopology inferInstance (fun μ : AbstractMeasure X R E ↦ μ f) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  exact (continuous_apply f).comp continuous_induced_dom

/-- A family of measures is weakly continuous exactly when each test evaluation is continuous. -/
theorem continuous_weak_iff [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module R E] {Y : Type*} [TopologicalSpace Y] (g : Y → AbstractMeasure X R E) :
    @Continuous _ _ inferInstance WeakTopology g ↔ ∀ f : C(X, R), Continuous (fun y ↦ g y f) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  exact continuous_induced_rng.trans continuous_pi_iff

end AbstractMeasure
