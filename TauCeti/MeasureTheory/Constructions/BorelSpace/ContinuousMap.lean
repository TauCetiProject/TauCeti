/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Sequences

/-!
# Measurable evaluations of continuous maps

Evaluations on a dense subset generate the Borel sigma algebra of continuous maps
under second-countability, local compactness and pseudometrizability assumptions.

A continuous map on an order interval extends to the ambient linearly ordered space by its
endpoint values. Evaluation of this extension at a fixed point is measurable for the Borel
structure on the space of continuous maps. No compatibility between the order and topology
of the domain is needed.
-/

public section

open Set MeasureTheory TopologicalSpace
open scoped Topology

namespace ContinuousMap

/-- Evaluations on a dense subset generate the Borel sigma algebra of continuous maps. -/
theorem borel_eq_iSup_comap_eval_of_dense {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [PseudoMetrizableSpace Y]
    {D : Set X} (hD : Dense D) :
    borel C(X, Y) = ⨆ x ∈ D, (borel Y).comap (fun f : C(X, Y) ↦ f x) := by
  borelize Y
  refine le_antisymm ?_ (iSup_le fun x ↦ iSup_le fun _ ↦
    (ContinuousMap.measurable_eval (Y := Y) x).comap_le)
  rw [borel_eq_iSup_comap_eval]
  refine iSup_le fun x ↦ ?_
  let : MeasurableSpace C(X, Y) := ⨆ x ∈ D, (borel Y).comap (fun f : C(X, Y) ↦ f x)
  apply measurable_iff_comap_le.1
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 (hD x)
  apply measurable_of_tendsto_metrizable (f := fun n f ↦ f (s n))
  · intro n
    exact (comap_measurable _).mono
      (le_iSup_of_le (s n) (le_iSup_of_le (hs n) le_rfl)) le_rfl
  · exact tendsto_pi_nhds.2 fun f ↦ f.continuous.continuousAt.tendsto.comp hlim

end ContinuousMap

namespace TauCeti

/-- On the space `C([a, b], X)` of continuous maps, evaluating the map extended by endpoint
values outside the order interval `[a, b]` at a fixed point is measurable. -/
theorem measurable_IccExtend_apply {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {a b : α} (hab : a ≤ b) (t : α) :
    Measurable fun γ : C(Icc a b, X) ↦ IccExtend hab γ t := by
  simp only [IccExtend_apply]
  exact (continuous_eval_const _).measurable

end TauCeti
