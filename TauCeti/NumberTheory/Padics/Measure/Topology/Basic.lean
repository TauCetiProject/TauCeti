/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.Topology.ContinuousMap.Compact

import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Evaluation and closed balls in the weak topology of measures

Evaluation on any fixed continuous test is weakly continuous.
`AbstractMeasure.continuous_weak_iff` characterizes weak continuity by continuity on each test.
`AbstractMeasure.isClosed_closedBall_weak` proves that the operator-norm closed balls of
module-valued measures over a nontrivially normed field on a compact space are weakly closed.
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

/-- An operator-norm closed ball of measures on a compact space is weakly closed. -/
theorem isClosed_closedBall_weak [CompactSpace X] [NontriviallyNormedField R] [NormedSpace R E]
    (μ₀ : AbstractMeasure X R E) (r : ℝ) :
    @IsClosed (AbstractMeasure X R E) WeakTopology
      {μ | toCLMEquiv μ ∈ Metric.closedBall (toCLMEquiv μ₀) r} := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  let : TopologicalSpace (C(X, R) →L[R] E) :=
    .induced (fun L ↦ (L : C(X, R) → E)) inferInstance
  have hball : IsClosed (Metric.closedBall (toCLMEquiv μ₀) r) :=
    isClosed_induced_iff'.2
      (ContinuousLinearMap.is_weak_closed_closedBall (toCLMEquiv μ₀) r)
  apply hball.preimage
  exact continuous_induced_rng.mpr <| continuous_pi fun f ↦ by
    simpa only [Function.comp_apply, coe_toCLMEquiv] using continuous_apply_weak f

end AbstractMeasure
