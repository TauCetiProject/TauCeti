/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Evaluation and closed balls in the weak topology of measures

Evaluation on any fixed continuous test is weakly continuous.
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

/-- An operator-norm closed ball of measures on a compact space is weakly closed. -/
theorem isClosed_closedBall_weak [CompactSpace X] [NontriviallyNormedField R] [NormedSpace R E]
    (μ₀ : AbstractMeasure X R E) (r : ℝ) :
    @IsClosed (AbstractMeasure X R E) WeakTopology
      {μ | toCLMEquiv μ ∈ Metric.closedBall (toCLMEquiv μ₀) r} := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  by_cases hr : 0 ≤ r
  · have hball : {μ | toCLMEquiv μ ∈ Metric.closedBall (toCLMEquiv μ₀) r} =
        ⋂ f : C(X, R), {μ | ‖μ f - μ₀ f‖ ≤ r * ‖f‖} := by
      ext μ
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm,
        ContinuousLinearMap.opNorm_le_iff hr, _root_.sub_apply, coe_toCLMEquiv]
    rw [hball]
    exact isClosed_iInter fun f ↦
      isClosed_le (((continuous_apply_weak f).sub continuous_const).norm) continuous_const
  · simp [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)]

end AbstractMeasure
