/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Graphs of measurable maps are measurable

The graph `Function.graph f` of a measurable map `f : α → β` is a measurable subset of `α × β`
as soon as the diagonal of `β` is measurable (`MeasurableEq β`), since it is the preimage of the
diagonal under `(a, b) ↦ (f a, b)`. A countably separated measurable space has a measurable
diagonal: the diagonal is the intersection, over a countable separating family of measurable
sets `s`, of the sets of pairs that lie both in `s` or both outside it. In particular graphs of
measurable maps into standard Borel spaces, or into quotients whose σ-algebra is countably
separated, are measurable.

The same holds for maps defined on a measurable subset only: the graph `s.graphOn f` is
measurable when `s` is measurable and the restriction `s.domRestrict f` is measurable.

These are the easy directions of the Borel graph theorem; the converses, which need the
Lusin–Souslin theorem, are in `TauCeti.MeasureTheory.Constructions.Polish.Graph`.

## Main results

* `MeasurableSpace.measurableEq_of_countablySeparated`: a countably separated measurable space
  has a measurable diagonal.
* `Measurable.measurableSet_graph`: the graph of a measurable map into a space with measurable
  diagonal is measurable.
* `MeasurableSet.graphOn`: the graph of a map that is measurable on a measurable set is
  measurable.

## References

* The statement of `Measurable.measurableSet_graph` and the instance
  `MeasurableSpace.measurableEq_of_countablySeparated` follow Mathlib PR 41944,
  `feat(CountablyGenerated): add measurableSet_graph` (generantao and Wojciech Nawrocki).
-/

public section

open Set Function

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace MeasurableSpace

/-- A countably separated measurable space has a measurable diagonal: the diagonal is the
intersection of the measurable sets `s ×ˢ s ∪ sᶜ ×ˢ sᶜ` over a countable separating family. -/
instance (priority := 100) measurableEq_of_countablySeparated [CountablySeparated α] :
    MeasurableEq α := by
  obtain ⟨S, hSc, hSm, hsep⟩ := exists_countable_separating α MeasurableSet univ
  have : diagonal α = ⋂ s ∈ S, s ×ˢ s ∪ sᶜ ×ˢ sᶜ := by
    ext ⟨x, y⟩
    simp only [mem_diagonal_iff, mem_iInter, mem_union, mem_prod, mem_compl_iff]
    refine ⟨fun h s _ ↦ by grind, fun h ↦ hsep x trivial y trivial fun s hs ↦ ?_⟩
    grind
  exact ⟨this ▸ .biInter hSc fun s hs ↦ ((hSm s hs).prod (hSm s hs)).union
    ((hSm s hs).compl.prod (hSm s hs).compl)⟩

end MeasurableSpace

/-- The graph of a measurable map into a space with measurable diagonal, for example a countably
separated space, is measurable. -/
@[measurability]
theorem Measurable.measurableSet_graph [MeasurableEq β] {f : α → β} (hf : Measurable f) :
    MeasurableSet f.graph :=
  measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd

/-- The graph of a map that is measurable on a measurable set `s`, into a space with measurable
diagonal, is measurable. -/
protected theorem MeasurableSet.graphOn [MeasurableEq β] {s : Set α} {f : α → β}
    (hs : MeasurableSet s) (hf : Measurable (s.domRestrict f)) : MeasurableSet (s.graphOn f) := by
  have : s.graphOn f = Prod.map (↑) id '' (s.domRestrict f).graph := by
    ext ⟨x, y⟩
    simp only [mem_graphOn, mem_image, mem_graph, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq, Subtype.exists, domRestrict_apply]
    grind
  rw [this]
  exact ((MeasurableEmbedding.subtype_coe hs).prodMap .id).measurableSet_image.2
    hf.measurableSet_graph
