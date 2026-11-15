/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.ProjIcc
public import TauCeti.Topology.MappingSpace.Based
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Sequences

/-!
# Measurable evaluations and dense-marginal uniqueness on continuous maps

Evaluations on a dense subset generate the Borel sigma algebra of continuous maps
when the domain is second-countable and locally compact and the codomain is second-countable
and regular, the assumptions of Mathlib's `ContinuousMap.borel_eq_iSup_comap_eval`.
A random continuous map is a.e. measurable exactly when all its evaluations are a.e.
measurable under the same topological assumptions. The evaluation criteria and measurable
finite-dimensional restrictions are also available for based continuous maps.
Consequently a finite Borel measure on `C(X, Y)` is determined by its finite-dimensional
evaluation laws on any dense set of evaluation points.

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

/-- Forgetting continuity is measurable for the product sigma algebra. -/
theorem measurable_coeFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] :
    Measurable (DFunLike.coe : C(X, Y) → (X → Y)) :=
  Measurable.of_eval measurable_eval

/-- Restricting a continuous map to finitely many evaluation points is measurable. -/
theorem measurable_finsetRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (I : Finset X) :
    Measurable (fun γ : C(X, Y) ↦ I.restrict (γ : X → Y)) :=
  (Finset.measurable_restrict I).comp measurable_coeFun

/-- For a second-countable locally compact domain and a second-countable regular Borel
codomain, a random continuous map is a.e. measurable exactly when every evaluation is. -/
theorem aemeasurable_iff_eval {X Y Ω : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [RegularSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → C(X, Y)} :
    AEMeasurable f μ ↔ ∀ x, AEMeasurable (fun ω ↦ f ω x) μ := by
  constructor
  · intro hf x
    exact (measurable_eval x).comp_aemeasurable hf
  · intro hf
    classical
    cases isEmpty_or_nonempty Ω
    · exact (measurable_of_empty f).aemeasurable
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
    let := hDc.to_subtype
    let N := {ω | ¬ ∀ d : D, f ω d = (hf d).mk (fun ω ↦ f ω d) ω}
    have hN : μ N = 0 := by
      apply ae_iff.1
      simpa only [N, not_not] using
        (ae_all_iff.2 fun d : D ↦ (hf d).ae_eq_mk)
    -- Replace entire paths on a measurable null set, preserving their continuity.
    let S := toMeasurable μ N
    let g : Ω → C(X, Y) := S.piecewise (fun _ ↦ f ω₀) f
    have hgD (d : D) : Measurable (fun ω ↦ g ω d) := by
      have heq : (fun ω ↦ g ω d) =
          S.piecewise (fun _ ↦ f ω₀ d) ((hf d).mk (fun ω ↦ f ω d)) := by
        funext ω
        by_cases hω : ω ∈ S
        · simp [g, hω]
        · have hωN : ω ∉ N := fun h ↦ hω (subset_toMeasurable μ N h)
          simpa [g, hω] using (not_not.1 hωN) d
      rw [heq]
      exact measurable_const.piecewise (measurableSet_toMeasurable μ N) (hf d).measurable_mk
    -- Recover the other measurable evaluations by limits, without uniqueness of limits.
    have hgm : Measurable g := measurable_iff_eval.2 fun x ↦ by
      obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 (hDd x)
      apply measurable_of_tendsto_metrizable (f := fun n ω ↦ g ω (s n))
      · exact fun n ↦ hgD ⟨s n, hs n⟩
      · exact tendsto_pi_nhds.2 fun ω ↦ (g ω).continuous.continuousAt.tendsto.comp hlim
    apply hgm.aemeasurable.congr
    have hS : μ S = 0 := (measure_toMeasurable N).trans hN
    have hSae : ∀ᵐ ω ∂μ, ω ∉ S := by
      simpa only [ae_iff, not_not, ofPred_mem_eq] using hS
    filter_upwards [hSae] with ω hω
    simp [g, hω]

end ContinuousMap

namespace TauCeti.BasedMap

variable {T E Ω : Type*} [TopologicalSpace T] [TopologicalSpace E]
  [MeasurableSpace E] [BorelSpace E] {t₀ : T} {x₀ : E}

/-- The inclusion of based continuous maps into continuous maps is a measurable embedding
when singletons in the codomain are measurable. -/
theorem measurableEmbedding_val [MeasurableSingletonClass E] :
    MeasurableEmbedding (Subtype.val : BasedMap T E t₀ x₀ → C(T, E)) :=
  MeasurableEmbedding.subtype_coe ((ContinuousMap.measurable_eval t₀) (measurableSet_singleton x₀))

/-- Restriction to finitely many times is measurable on based continuous maps. -/
theorem measurable_finsetRestrict (I : Finset T) :
    Measurable (fun γ : BasedMap T E t₀ x₀ ↦ I.restrict (γ.1 : T → E)) :=
  (ContinuousMap.measurable_finsetRestrict I).comp measurable_subtype_coe

variable [SecondCountableTopology T] [LocallyCompactSpace T]
  [SecondCountableTopology E] [RegularSpace E] [MeasurableSpace Ω]

/-- A map into based continuous maps is measurable exactly when every evaluation is. -/
theorem measurable_iff_eval {f : Ω → BasedMap T E t₀ x₀} :
    Measurable f ↔ ∀ t, Measurable (fun ω ↦ (f ω).1 t) := by
  exact ⟨fun hf ↦ ContinuousMap.measurable_iff_eval.1 hf.subtype_coe,
    fun hf ↦ (ContinuousMap.measurable_iff_eval.2 hf).subtype_mk⟩

/-- A map into based continuous maps is a.e. measurable exactly when every evaluation is. -/
theorem aemeasurable_iff_eval {μ : Measure Ω} {f : Ω → BasedMap T E t₀ x₀} :
    AEMeasurable f μ ↔ ∀ t, AEMeasurable (fun ω ↦ (f ω).1 t) μ := by
  rw [aemeasurable_comap_iff Subtype.val_injective, ContinuousMap.aemeasurable_iff_eval]
  rfl

end TauCeti.BasedMap

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

/-- On the space `C([a, b], X)` of continuous maps, evaluating the map extended by endpoint
values outside the order interval `[a, b]` at a fixed point is measurable. -/
theorem measurable_IccExtend_apply {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {a b : α} (hab : a ≤ b) (t : α) :
    Measurable fun γ : C(Icc a b, X) ↦ IccExtend hab γ t := by
  simp only [IccExtend_apply]
  exact (continuous_eval_const _).measurable

end TauCeti
