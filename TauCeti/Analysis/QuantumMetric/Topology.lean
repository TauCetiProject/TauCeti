/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.QuantumMetric.StateEDist
public import TauCeti.Analysis.Normed.Order.StateSpace
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Semicontinuity.Basic

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

The distance is lower semicontinuous for the weak-star topology, so its closed balls are
weak-star compact. These facts are useful when comparing the two topologies.

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

/-- The state distance is lower semicontinuous in the pair of weak-star functionals. -/
theorem lowerSemicontinuous_stateEDist :
    LowerSemicontinuous (fun p : WeakDual ℝ E × WeakDual ℝ E => L.stateEDist p.1 p.2) := by
  simp only [stateEDist_def]
  exact lowerSemicontinuous_iSup fun a => lowerSemicontinuous_iSup fun _ =>
    ((WeakDual.eval_continuous a).comp continuous_fst |>.edist
      ((WeakDual.eval_continuous a).comp continuous_snd)).lowerSemicontinuous

/-- A sublevel set of the state distance is weak-star closed, jointly in both functionals. -/
theorem isClosed_setOf_stateEDist_le (r : ℝ≥0∞) :
    IsClosed {p : WeakDual ℝ E × WeakDual ℝ E | L.stateEDist p.1 p.2 ≤ r} :=
  L.lowerSemicontinuous_stateEDist.isClosed_preimage r

variable [Preorder E]

/-- The extended metric defined by `L` on the state space. This is deliberately not an
instance: its topology need not equal the inherited weak-star topology. -/
@[instance_reducible]
noncomputable def stateEMetricSpace : EMetricSpace (OrderUnit.stateSpace e) where
  edist φ ψ := L.stateEDist φ ψ
  edist_self φ := L.stateEDist_self φ
  edist_comm φ ψ := L.stateEDist_comm φ ψ
  edist_triangle φ ψ χ := L.stateEDist_triangle φ ψ χ
  eq_of_edist_eq_zero h := Subtype.ext (L.stateEDist_eq_zero_iff.1 h)

/-- Installing the state metric computes extended distance by `stateEDist`. -/
@[simp]
theorem edist_stateEMetricSpace (φ ψ : OrderUnit.stateSpace e) :
    @edist _ L.stateEMetricSpace.toEDist φ ψ = L.stateEDist φ ψ :=
  (rfl)

/-- For a finite-domain element, evaluation on the state metric space is Lipschitz, with
constant equal to its seminorm. -/
theorem lipschitzWith_eval (a : L.domain) :
    letI := L.stateEMetricSpace
    LipschitzWith (L a).toNNReal (fun φ : OrderUnit.stateSpace e => (φ : WeakDual ℝ E) a) := by
  let := L.stateEMetricSpace
  intro φ ψ
  rw [ENNReal.coe_toNNReal (L.mem_domain.1 a.property), L.edist_stateEMetricSpace]
  exact L.edist_apply_le_mul_stateEDist ((OrderUnit.apply_eq_one_of_mem_stateSpace φ.property).trans
    (OrderUnit.apply_eq_one_of_mem_stateSpace ψ.property).symm) a

end Topological

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e : E} (L : ExtendedLipschitzSeminorm e)

/-- Closed balls for the state distance are compact in the weak-star topology. -/
theorem isCompact_setOf_stateEDist_le (he : IsOrderUnitNorm e) (φ : WeakDual ℝ E) (r : ℝ≥0∞) :
    IsCompact {ψ ∈ OrderUnit.stateSpace e | L.stateEDist ψ φ ≤ r} := by
  exact (he.isCompact_stateSpace).inter_right
    ((L.isClosed_setOf_stateEDist_le r).preimage (continuous_id.prodMk continuous_const))

/-- Convergence for the state distance implies weak-star convergence, along any filter.
No finiteness or Lip-norm condition on the distance is needed. -/
theorem tendsto_of_stateEDist_tendsto_zero (he : IsOrderUnitNorm e) {ι : Type*} {l : Filter ι}
    {φ : ι → OrderUnit.stateSpace e} {ψ : OrderUnit.stateSpace e}
    (h : Tendsto (fun i => L.stateEDist (φ i) ψ) l (𝓝 0)) :
    Tendsto (fun i => (φ i : WeakDual ℝ E)) l (𝓝 (ψ : WeakDual ℝ E)) := by
  have hfinite (a : E) (ha : a ∈ L.domain) :
      Tendsto (fun i => (φ i : WeakDual ℝ E) a) l (𝓝 ((ψ : WeakDual ℝ E) a)) := by
    apply tendsto_iff_edist_tendsto_0.2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => bot_le) (fun i =>
        L.edist_apply_le_mul_stateEDist
          ((OrderUnit.apply_eq_one_of_mem_stateSpace (φ i).property).trans
            (OrderUnit.apply_eq_one_of_mem_stateSpace ψ.property).symm) a)
    simpa using ENNReal.Tendsto.const_mul h (a := L a) (Or.inr (L.mem_domain.1 ha))
  have hcont : Equicontinuous (fun i a => (φ i : WeakDual ℝ E) a) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro a b i
    simpa [Real.dist_eq, dist_eq_norm, map_sub] using
      he.abs_apply_le_of_mem_stateSpace (φ i).property (a - b)
  have hclosed := hcont.isClosed_setOfPred_tendsto (l := l) (map_continuous (ψ : WeakDual ℝ E))
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.2
  exact fun a => L.dense_domain.induction hfinite hclosed a

/-- The inclusion from the state metric topology into the weak-star dual is continuous.
This expresses that the state metric topology is finer than the weak-star subspace topology. -/
theorem continuous_stateEMetricSpace_coe (he : IsOrderUnitNorm e) :
    @Continuous (OrderUnit.stateSpace e) (WeakDual ℝ E)
      L.stateEMetricSpace.toUniformSpace.toTopologicalSpace inferInstance Subtype.val := by
  let := L.stateEMetricSpace
  -- Specify the metric topology explicitly alongside the inherited subtype topology.
  let : TopologicalSpace (OrderUnit.stateSpace e) :=
    L.stateEMetricSpace.toUniformSpace.toTopologicalSpace
  apply continuous_iff_continuousAt.2
  intro ψ
  exact L.tendsto_of_stateEDist_tendsto_zero he (φ := id)
    (by simpa only [L.edist_stateEMetricSpace] using
      (tendsto_iff_edist_tendsto_0.1 (tendsto_id : Tendsto id (𝓝 ψ) (𝓝 ψ))))

end Normed

end TauCeti.ExtendedLipschitzSeminorm
