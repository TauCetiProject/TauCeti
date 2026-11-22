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
# Evaluation and the unit ball in the weak topology of measures

Evaluation on any fixed continuous test is weakly continuous. For module-valued measures
over a nontrivially normed field on a compact space, the operator-norm unit ball is weakly
closed by Mathlib's weak closedness theorem for balls of continuous linear maps.
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

/-- The operator-norm unit ball of measures on a compact space is weakly closed. -/
theorem isClosed_unitBall_weak [CompactSpace X] [NontriviallyNormedField R] [NormedSpace R E] :
    @IsClosed (AbstractMeasure X R E) WeakTopology {μ | ‖toCLMEquiv μ‖ ≤ 1} := by
  have hsub :
      (fun (μ : AbstractMeasure X R E) (f : C(X, R)) ↦ μ f) '' {μ | ‖toCLMEquiv μ‖ ≤ 1} ⊆
        ((↑) : (C(X, R) →L[R] E) → C(X, R) → E) '' Metric.closedBall 0 1 := by
    rintro _ ⟨ν, hν, rfl⟩
    exact ⟨toCLMEquiv ν, mem_closedBall_zero_iff.mpr hν, funext (coe_toCLMEquiv ν)⟩
  refine isClosed_induced_iff'.2 fun μ hμ ↦ mem_closedBall_zero_iff.mp <|
    ContinuousLinearMap.is_weak_closed_closedBall 0 1 ?_
  have hcoe : ⇑(toCLMEquiv μ) = (fun f ↦ μ f) := funext (coe_toCLMEquiv μ)
  exact hcoe ▸ closure_mono hsub hμ

end AbstractMeasure
