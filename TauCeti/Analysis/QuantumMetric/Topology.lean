/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.QuantumMetric.StateEDist
public import TauCeti.Analysis.Normed.Order.StateSpace

/-!
# The topology of the state distance

An extended Lipschitz seminorm gives an extended metric on the states of an order-unit
space. Its topology is finer than the weak-star topology: convergence for the state distance
implies convergence on the finite domain by the evaluation estimate, and then convergence
everywhere by density and the common norm bound of states.

`stateEMetricSpace` is an explicit structure, rather than an instance. The state space retains
its inherited weak-star topology. Comparisons use the explicit topology of the metric. The filter
theorem `tendsto_of_stateEDist_tendsto_zero` compares these topologies without changing instances.
The converse requires the Lip-norm condition.

Joint weak-star lower semicontinuity gives closed distance sublevels on the weak dual. Under
`IsOrderUnitNorm e`, their fixed-center slices intersect the compact state space in compact sets.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), §2.
-/

public section

open Filter Set
open scoped Topology ENNReal

namespace TauCeti.ExtendedLipschitzSeminorm

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {e : E}
  (L : ExtendedLipschitzSeminorm e)

variable [Preorder E]

/-- The extended metric defined by `L` on the state space. This is deliberately not an
instance: its topology need not equal the inherited weak-star topology. -/
@[instance_reducible]
noncomputable def stateEMetricSpace : EMetricSpace (OrderUnit.stateSpace e) :=
  EMetricSpace.induced Subtype.val Subtype.val_injective L.weakDualEMetricSpace

/-- Installing the state metric computes extended distance by `stateEDist`. -/
@[simp]
theorem edist_stateEMetricSpace (φ ψ : OrderUnit.stateSpace e) :
    @edist _ L.stateEMetricSpace.toEDist φ ψ = L.stateEDist φ ψ :=
  L.edist_weakDualEMetricSpace φ ψ

/-- For a finite-domain element, evaluation on the state metric space is Lipschitz, with
constant equal to its seminorm. -/
theorem lipschitzWith_eval (a : L.domain) :
    letI := L.stateEMetricSpace
    LipschitzWith (L a).toNNReal (fun φ : OrderUnit.stateSpace e => (φ : WeakDual ℝ E) a) :=
  fun φ ψ => L.lipschitzOnWith_eval a 1 (OrderUnit.apply_eq_one_of_mem_stateSpace φ.property)
    (OrderUnit.apply_eq_one_of_mem_stateSpace ψ.property)

end Topological

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e : E} (L : ExtendedLipschitzSeminorm e)

/-- The intersection of the state space with a fixed-center distance sublevel is weak-star compact
when the norm is the order-unit norm. The center can be any weak-dual functional. -/
theorem isCompact_stateSpace_inter_setOf_stateEDist_le (he : IsOrderUnitNorm e)
    (φ : WeakDual ℝ E) (r : ℝ≥0∞) :
    IsCompact {ψ ∈ OrderUnit.stateSpace e | L.stateEDist ψ φ ≤ r} := by
  exact (he.isCompact_stateSpace).inter_right
    ((L.isClosed_setOf_stateEDist_le r).preimage (continuous_id.prodMk continuous_const))

/-- Convergence for the state distance implies weak-star convergence, along any filter.
No finiteness or Lip-norm condition on the distance is needed. -/
theorem tendsto_of_stateEDist_tendsto_zero (he : IsOrderUnitNorm e) {ι : Type*} {l : Filter ι}
    {φ : ι → OrderUnit.stateSpace e} {ψ : OrderUnit.stateSpace e}
    (h : Tendsto (fun i => L.stateEDist (φ i) ψ) l (𝓝 0)) :
    Tendsto φ l (𝓝 ψ) :=
  tendsto_subtype_rng.2 <| L.tendsto_weakDual_of_stateEDist_tendsto_zero
    (.of_forall fun i => (he.norm_toStrongDual_of_mem_stateSpace (φ i).property).le) h

/-- The state metric topology is finer than the inherited weak-star topology. -/
theorem stateEMetricSpace_toTopologicalSpace_le (he : IsOrderUnitNorm e) :
    L.stateEMetricSpace.toUniformSpace.toTopologicalSpace ≤
      inferInstanceAs (TopologicalSpace (OrderUnit.stateSpace e)) := by
  refine le_of_nhds_le_nhds fun ψ => tendsto_id'.1 ?_
  let := L.stateEMetricSpace
  let : TopologicalSpace (OrderUnit.stateSpace e) :=
    L.stateEMetricSpace.toUniformSpace.toTopologicalSpace
  exact L.tendsto_of_stateEDist_tendsto_zero he (φ := id) (ψ := ψ)
    (by simpa only [L.edist_stateEMetricSpace] using
      (tendsto_iff_edist_tendsto_0.1 (tendsto_id : Tendsto id (𝓝 ψ) (𝓝 ψ))))

end Normed

end TauCeti.ExtendedLipschitzSeminorm
