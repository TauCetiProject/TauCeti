/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Polish.Analytic
public import TauCeti.MeasureTheory.MeasurableSpace.Graph

/-!
# The Borel graph theorem

A map between standard Borel spaces is measurable if and only if its graph is measurable, and a
map between Polish spaces is measurable if and only if its graph is analytic. One direction holds
for every countably separated target (`Measurable.measurableSet_graph`); this file proves the
converses.

The measurable form is the Lusin–Souslin theorem. If `G ⊆ X × Y` is a measurable set with at most
one point above each `x` (`InjOn Prod.fst G`), the projection `G → X` is a measurable injection
from a standard Borel space, hence a measurable embedding
(`MeasurableSet.measurableEmbedding_domRestrict_fst`). So a map into `X × Y` with values in `G` is
measurable as soon as its first coordinate is (`MeasurableSet.measurable_iff_measurable_fst`).
Applied to `x ↦ (x, f x)`, this recovers `f` from its graph. The same argument applies to maps
defined on a subset `s ⊆ X`: the graph `s.graphOn f` is measurable if and only if `s` is
measurable and `f` is measurable on `s` (`TauCeti.measurableSet_graphOn_iff`). When `Y` is
nonempty, every set `G` with `InjOn Prod.fst G` is of the form `graphOn f (Prod.fst '' G)`
(`Set.exists_eq_graphOn_image_fst`), so this describes all measurable sets with at most one point
in each vertical section: their domain is measurable (`MeasurableSet.of_graphOn`) and the partial
function they name is measurable on it (`MeasurableSet.measurable_domRestrict_of_graphOn`). The
projection embedding above needs no such hypothesis.

The analytic form is Souslin's theorem. If the graph of `f` is analytic, the preimage
`f ⁻¹' t = (Function.graph f).preimage t` of a Borel set is analytic, and so is the preimage of
its complement; a set that is analytic with analytic complement is Borel.

## Main results

* `MeasurableSet.measurableEmbedding_domRestrict_fst`: the projection of a measurable set with at
  most one point above each `x` is a measurable embedding.
* `MeasurableSet.measurable_iff_measurable_fst`: a map with values in such a set is measurable if
  and only if its first coordinate is.
* `TauCeti.measurableSet_graphOn_iff`: a partial map between standard Borel spaces has
  measurable graph if and only if its domain is measurable and it is measurable on its domain.
* `TauCeti.measurableSet_graph_iff_measurable`: a map between standard Borel spaces is
  measurable if and only if its graph is measurable.
* `MeasureTheory.AnalyticSet.measurable_of_graph`, `TauCeti.analyticSet_graph_iff_measurable`:
  a map between Polish spaces is measurable if and only if its graph is analytic.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 14.12 (the Borel graph theorem) and Theorem 15.1 (Lusin–Souslin).
* The statements of `MeasureTheory.AnalyticSet.measurable_of_graph` and
  `TauCeti.analyticSet_graph_iff_measurable` follow `measurable_of_analyticSet_graph` and
  `analyticSet_graph_iff_measurable` in Mathlib PR 41945,
  `feat(Polish): add analyticSet_graph_iff_measurable` (generantao, with Zelong Li, Aaron Liu and
  Wojciech Nawrocki), whose proof of the analytic direction is adapted here.
* The treatment of measurable sets with at most one point above each `x` through the projection
  embedding is adapted from `InfinitaryLogic/Descriptive/BorelFunctionalGraph.lean` in
  `cameronfreer/infinitary-logic` (Apache-2.0), which bundles these sets in a structure.
-/

public section

open Set Function MeasureTheory

variable {X Y : Type*}

section StandardBorel

variable [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]

/-- **Lusin–Souslin for vertical sections.** If a measurable subset `G` of a product of standard
Borel spaces has at most one point above each `x`, its projection `G → X` is a measurable
embedding. -/
theorem MeasurableSet.measurableEmbedding_domRestrict_fst {G : Set (X × Y)}
    (hG : MeasurableSet G) (hinj : InjOn Prod.fst G) :
    MeasurableEmbedding (G.domRestrict Prod.fst) :=
  have := hG.standardBorel
  (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (injOn_iff_injective.1 hinj)

/-- A map with values in a measurable subset `G` of a product of standard Borel spaces with at
most one point above each `x` is measurable if and only if its first coordinate is. -/
theorem MeasurableSet.measurable_iff_measurable_fst {Z : Type*} [MeasurableSpace Z]
    {G : Set (X × Y)} (hG : MeasurableSet G) (hinj : InjOn Prod.fst G) {φ : Z → X × Y}
    (hφ : ∀ z, φ z ∈ G) : Measurable φ ↔ Measurable fun z ↦ (φ z).1 := by
  refine ⟨fun h ↦ measurable_fst.comp h, fun h ↦ ?_⟩
  have hψ : Measurable fun z ↦ (⟨φ z, hφ z⟩ : G) :=
    (hG.measurableEmbedding_domRestrict_fst hinj).measurable_comp_iff.1 h
  exact measurable_subtype_coe.comp hψ

/-- **The domain of a measurable graph is measurable.** If the graph of `f` on `s` is a measurable
subset of a product of standard Borel spaces, then `s` is measurable. -/
theorem MeasurableSet.of_graphOn {s : Set X} {f : X → Y} (h : MeasurableSet (s.graphOn f)) :
    MeasurableSet s := by
  simpa only [image_fst_graphOn] using h.image_of_measurable_injOn measurable_fst fst_injOn_graph

/-- **A partial map with measurable graph is measurable on its domain.** If the graph of `f` on
`s` is a measurable subset of a product of standard Borel spaces, then `f` is measurable on
`s`. -/
theorem MeasurableSet.measurable_domRestrict_of_graphOn {s : Set X} {f : X → Y}
    (h : MeasurableSet (s.graphOn f)) : Measurable (s.domRestrict f) := by
  have : Measurable fun x : s ↦ ((x : X), f x) :=
    (h.measurable_iff_measurable_fst fst_injOn_graph fun x ↦ by simp).2 measurable_subtype_coe
  exact measurable_snd.comp this

namespace TauCeti

/-- **The Borel graph theorem for partial maps.** The graph of `f` on `s`, for standard Borel
spaces `X` and `Y`, is measurable if and only if `s` is measurable and `f` is measurable on
`s`. -/
theorem measurableSet_graphOn_iff {s : Set X} {f : X → Y} :
    MeasurableSet (s.graphOn f) ↔ MeasurableSet s ∧ Measurable (s.domRestrict f) :=
  ⟨fun h ↦ ⟨h.of_graphOn, h.measurable_domRestrict_of_graphOn⟩, fun h ↦ h.1.graphOn h.2⟩

/-- **The Borel graph theorem.** A map between standard Borel spaces is measurable if and only if
its graph is measurable. -/
theorem measurableSet_graph_iff_measurable {f : X → Y} :
    MeasurableSet f.graph ↔ Measurable f := by
  refine ⟨fun h ↦ ?_, Measurable.measurableSet_graph⟩
  have : Measurable fun x ↦ (x, f x) :=
    (h.measurable_iff_measurable_fst (fun _ _ _ _ ↦ by grind) fun x ↦ by simp).2
      measurable_id
  exact measurable_snd.comp this

end TauCeti

end StandardBorel

/-- **Souslin's theorem for graphs.** A map from a Hausdorff space with its Borel sets measurable
to a Polish space, whose graph is analytic, is measurable. -/
@[fun_prop]
theorem MeasureTheory.AnalyticSet.measurable_of_graph [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} (hf : AnalyticSet f.graph) : Measurable f := by
  intro t ht
  refine AnalyticSet.measurableSet_of_compl ?_ ?_
  · rw [preimage_eq]
    exact hf.relPreimage ht.analyticSet
  · rw [← preimage_compl, preimage_eq]
    exact hf.relPreimage ht.compl.analyticSet

namespace TauCeti

/-- **The Borel graph theorem, analytic form.** A map between Polish spaces is measurable if and
only if its graph is analytic. -/
theorem analyticSet_graph_iff_measurable [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} : AnalyticSet f.graph ↔ Measurable f :=
  ⟨AnalyticSet.measurable_of_graph, fun hf ↦ hf.measurableSet_graph.analyticSet⟩

end TauCeti
