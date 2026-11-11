/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Sequences

/-!
# Measurable evaluations of continuous maps

Evaluations on a dense subset generate the Borel sigma algebra of continuous maps
when the domain is second-countable and locally compact and the codomain is second-countable
and regular, the assumptions of Mathlib's `ContinuousMap.borel_eq_iSup_comap_eval`.
For Hausdorff codomains, a random continuous map is a.e. measurable exactly when all its
evaluations are a.e. measurable, using countably many dense evaluations to select one
common representative.

A continuous map on an order interval extends to the ambient linearly ordered space by its
endpoint values. Evaluation of this extension at a fixed point is measurable for the Borel
structure on the space of continuous maps. No compatibility between the order and topology
of the domain is needed.
-/

public section

open Set MeasureTheory TopologicalSpace
open scoped Topology

namespace ContinuousMap

/-- Evaluations on a dense subset generate the Borel sigma algebra of continuous maps, for a
second-countable locally compact domain and a second-countable regular codomain. -/
theorem borel_eq_iSup_comap_eval_of_dense {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [RegularSpace Y]
    {D : Set X} (hD : Dense D) :
    borel C(X, Y) = ⨆ x ∈ D, (borel Y).comap (fun f : C(X, Y) ↦ f x) := by
  borelize Y
  refine le_antisymm ?_ (iSup₂_le fun x _ ↦ (measurable_eval (Y := Y) x).comap_le)
  rw [borel_eq_iSup_comap_eval]
  refine iSup_le fun x ↦ ?_
  let : MeasurableSpace C(X, Y) := ⨆ x ∈ D, (borel Y).comap (fun f : C(X, Y) ↦ f x)
  apply measurable_iff_comap_le.1
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 (hD x)
  apply measurable_of_tendsto_metrizable (f := fun n f ↦ f (s n))
  · intro n
    exact (comap_measurable _).mono (le_iSup₂_of_le (s n) (hs n) le_rfl) le_rfl
  · exact tendsto_pi_nhds.2 fun f ↦ f.continuous.continuousAt.tendsto.comp hlim

/-- A random continuous map is a.e. measurable exactly when each evaluation is a.e.
measurable. Countably many dense evaluations suffice to choose one common representative. -/
theorem aemeasurable_iff_eval {X Y Ω : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [RegularSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → C(X, Y)} :
    AEMeasurable f μ ↔ ∀ x, AEMeasurable (fun ω ↦ f ω x) μ := by
  constructor
  · intro hf x
    exact (measurable_eval x).comp_aemeasurable hf
  · intro hf
    obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
    let := hDc.to_subtype
    let e : C(X, Y) → (D → Y) := fun g x ↦ g x
    have he : Function.Injective e := by
      intro g h hgh
      apply injective_restrict hDd
      ext x
      exact congrFun hgh x
    have hm : borel C(X, Y) =
        (inferInstance : MeasurableSpace (D → Y)).comap e := by
      rw [borel_eq_iSup_comap_eval_of_dense hDd]
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp, e, Function.comp_def]
      rw [iSup_subtype]
      simp only [BorelSpace.measurable_eq]
    have h := (aemeasurable_comap_iff he).2 (AEMeasurable.of_eval fun x ↦ hf x)
    rwa [← hm] at h

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
