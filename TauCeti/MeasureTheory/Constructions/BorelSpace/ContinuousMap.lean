/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Sequences

/-!
# Measurable evaluations and finite-marginal uniqueness on continuous maps

Evaluations on a dense subset generate the Borel sigma algebra of continuous maps
when the domain is second-countable and locally compact and the codomain is second-countable
and regular, the assumptions of Mathlib's `ContinuousMap.borel_eq_iSup_comap_eval`.
Consequently a finite Borel measure on `C(X, Y)` is determined by its finite-dimensional
evaluation laws on any dense set of evaluation points, and in particular by all finite-dimensional
evaluation laws.

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

end ContinuousMap

namespace TauCeti

/-- A finite Borel measure on `C(X, Y)` is determined by its finite-dimensional evaluation
marginals on any dense subset `D` of `X`; finiteness is only needed on one side. -/
theorem measure_eq_of_finset_eval_map_eq_of_dense {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [RegularSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {D : Set X} (hD : Dense D) {μ ν : Measure C(X, Y)} [IsFiniteMeasure μ]
    (h : ∀ I : Finset X, (I : Set X) ⊆ D →
      μ.map (fun f (i : I) ↦ f i) = ν.map (fun f (i : I) ↦ f i)) :
    μ = ν := by
  let r : C(X, Y) → (D → Y) := fun f x ↦ f x
  have hm : ContinuousMap.measurableSpace (X := X) (Y := Y) = MeasurableSpace.pi.comap r := by
    rw [BorelSpace.measurable_eq (α := C(X, Y)),
      ContinuousMap.borel_eq_iSup_comap_eval_of_dense hD,
      MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_subtype]
    simp_rw [BorelSpace.measurable_eq (α := Y), MeasurableSpace.comap_comp, Function.comp_def, r]
  have hr : Measurable r := hm ▸ comap_measurable r
  have hmap : μ.map r = ν.map r := by
    refine IsProjectiveLimit.unique (P := fun J : Finset D ↦ (μ.map r).map J.restrict)
      (fun _ ↦ rfl) fun J ↦ ?_
    let e : D ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
    let q : (J.map e → Y) → (J → Y) := fun g j ↦ g (J.equivMap e j)
    have hq : Measurable q := by fun_prop
    have heval : Measurable fun (f : C(X, Y)) (i : J.map e) ↦ f i :=
      measurable_pi_iff.2 fun i ↦ ContinuousMap.measurable_eval i.1
    have hcomp : J.restrict ∘ r = q ∘ fun (f : C(X, Y)) (i : J.map e) ↦ f i := rfl
    dsimp only
    rw [Measure.map_map (Finset.measurable_restrict J) hr,
      Measure.map_map (Finset.measurable_restrict J) hr, hcomp,
      ← Measure.map_map hq heval, ← Measure.map_map hq heval,
      h (J.map e) J.map_subtype_subset]
  ext s hs
  rw [hm] at hs
  rcases hs with ⟨t, ht, rfl⟩
  rw [← Measure.map_apply hr ht, hmap, Measure.map_apply hr ht]

/-- Two Borel measures on `C(X, Y)`, at least one of which is finite, are equal if they have the
same finite-dimensional evaluation marginals. -/
theorem measure_eq_of_finset_eval_map_eq {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [RegularSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {μ ν : Measure C(X, Y)} [IsFiniteMeasure μ]
    (h : ∀ I : Finset X, μ.map (fun f (i : I) ↦ f i) = ν.map (fun f (i : I) ↦ f i)) :
    μ = ν :=
  measure_eq_of_finset_eval_map_eq_of_dense dense_univ fun I _ ↦ h I

/-- On the space `C([a, b], X)` of continuous maps, evaluating the map extended by endpoint
values outside the order interval `[a, b]` at a fixed point is measurable. -/
theorem measurable_IccExtend_apply {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {a b : α} (hab : a ≤ b) (t : α) :
    Measurable fun γ : C(Icc a b, X) ↦ IccExtend hab γ t := by
  simp only [IccExtend_apply]
  exact (continuous_eval_const _).measurable

end TauCeti
