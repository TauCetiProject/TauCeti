/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Basic
public import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad
import TauCeti.Data.Set.PowersetCard

/-!
# Unordered supports of polyads and subpolyads

A polyad `P` or subpolyad `Q` computes its support as a `Finset` of ordered injective triples
`{x : Fin 3 → V // Function.Injective x}`. Projecting each ordered triple via
`Set.powersetCard.ofFinEmb 3 V` yields `Polyad3.unorderedSupport` and `Subpolyad3.unorderedSupport`
in `Set.powersetCard V 3`.

When `P` has pairwise distinct vertex cells (`Polyad3.HasDistinctCells`), `ofFinEmb` is injective
on `P.support`, so unordered supports preserve support cardinalities and color-fiber counts
(`Polyad3.HasDistinctCells.card_unorderedSupport`,
`Polyad3.HasDistinctCells.card_filter_unorderedSupport`, `Subpolyad3.card_unorderedSupport`,
`Subpolyad3.card_filter_unorderedSupport`).

## Main definitions

* `TauCeti.Polyad3.unorderedSupport`: the unordered `3`-subsets underlying `P.support`.
* `TauCeti.Subpolyad3.unorderedSupport`: the unordered `3`-subsets underlying `Q.support`.

## Main results

* `TauCeti.Polyad3.HasDistinctCells.injOn_ofFinEmb`: `ofFinEmb` is injective on the support of
  a distinct-cell polyad.
* `TauCeti.Polyad3.HasDistinctCells.card_unorderedSupport` and
  `TauCeti.Subpolyad3.card_unorderedSupport`: unordered and ordered supports have equal size over
  distinct cells.
-/

public section

open Finset

namespace TauCeti

namespace Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- For a distinct-cell polyad, the map from ordered injective triples to unordered triples is
injective on `P.support`. -/
theorem HasDistinctCells.injOn_ofFinEmb {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Set.InjOn (fun x : {x : Fin 3 → V // Function.Injective x} ↦
      Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) (P.support : Set _) := by
  intro x hx y hy hxy
  obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm
    ⟨y.val, y.property⟩ ⟨x.val, x.property⟩).1 hxy.symm
  have hcell (i : Fin 3) : P.cell i = P.cell (σ i) := by
    have hxi := ((mem_support_iff_cell_colorAt P x).1 hx).1 (σ i)
    have hyi := ((mem_support_iff_cell_colorAt P y).1 hy).1 i
    have hσi : y.val i = x.val (σ i) := congrFun hσ i
    rw [hσi] at hyi
    rw [← S.vertexPart.part_eq_of_mem (P.cell_mem_parts i) hyi,
      ← S.vertexPart.part_eq_of_mem (P.cell_mem_parts (σ i)) hxi]
  have hσ1 : ∀ i, i = σ i := fun i ↦ (hasDistinctCells_iff_injective_cell P).1 hP (hcell i)
  exact (Subtype.ext (funext fun i ↦ by
    have hσi : y.val i = x.val (σ i) := congrFun hσ i
    rw [hσi, ← hσ1 i])).symm

/-- The unordered three-element vertex sets underlying the support of a polyad. -/
noncomputable def unorderedSupport (P : Polyad3 S) : Finset (Set.powersetCard V 3) :=
  P.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩

/-- The unordered support of a polyad is the image of its ordered support under `ofFinEmb`. -/
theorem unorderedSupport_def (P : Polyad3 S) :
    P.unorderedSupport =
      P.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ :=
  (rfl)

/-- An unordered triple lies in the unordered support of a polyad iff it underlies some ordered
triple in the polyad's support. -/
@[simp]
theorem mem_unorderedSupport (P : Polyad3 S) {s : Set.powersetCard V 3} :
    s ∈ P.unorderedSupport ↔
      ∃ x ∈ P.support, Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s := by
  simp [unorderedSupport]

/-- A distinct-cell polyad has as many unordered triples as ordered triples in its support. -/
theorem HasDistinctCells.card_unorderedSupport {P : Polyad3 S} (hP : P.HasDistinctCells) :
    #P.unorderedSupport = #P.support :=
  card_image_of_injOn hP.injOn_ofFinEmb

/-- Over a distinct-cell polyad, filtering the unordered support of the polyad by a top color
gives the same count as filtering its ordered support. -/
theorem HasDistinctCells.card_filter_unorderedSupport {κ₃ : Type*} [DecidableEq κ₃]
    {P : Polyad3 S} (hP : P.HasDistinctCells) (H : Colored3Graph κ₃ V) (c : κ₃) :
    #{s ∈ P.unorderedSupport | H.color s = c} =
      #{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} := by
  rw [unorderedSupport_def, filter_image,
    card_image_of_injOn (hP.injOn_ofFinEmb.mono (filter_subset _ _))]

end Polyad3

namespace Subpolyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {P : Polyad3 S}

/-- The unordered three-element vertex sets underlying the support of a subpolyad. -/
noncomputable def unorderedSupport (Q : Subpolyad3 P) : Finset (Set.powersetCard V 3) :=
  Q.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩

/-- The unordered support of a subpolyad is the image of its ordered support under `ofFinEmb`. -/
theorem unorderedSupport_def (Q : Subpolyad3 P) :
    Q.unorderedSupport =
      Q.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ :=
  (rfl)

/-- An unordered triple lies in the unordered support of a subpolyad iff it underlies some ordered
triple in the subpolyad's support. -/
@[simp]
theorem mem_unorderedSupport (Q : Subpolyad3 P) {s : Set.powersetCard V 3} :
    s ∈ Q.unorderedSupport ↔
      ∃ x ∈ Q.support, Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s := by
  simp [unorderedSupport]

/-- The unordered support of a subpolyad lies in the unordered support of its parent polyad. -/
theorem unorderedSupport_subset (Q : Subpolyad3 P) :
    Q.unorderedSupport ⊆ P.unorderedSupport :=
  image_subset_image Q.support_subset

/-- Over a distinct-cell polyad, a subpolyad has as many unordered triples as ordered triples. -/
theorem card_unorderedSupport (Q : Subpolyad3 P) (hP : P.HasDistinctCells) :
    #Q.unorderedSupport = #Q.support :=
  card_image_of_injOn (hP.injOn_ofFinEmb.mono Q.support_subset)

/-- Over a distinct-cell polyad, filtering the unordered support of a subpolyad by a top color
gives the same count as filtering its ordered support. -/
theorem card_filter_unorderedSupport {κ₃ : Type*} [DecidableEq κ₃] (Q : Subpolyad3 P)
    (hP : P.HasDistinctCells) (H : Colored3Graph κ₃ V) (c : κ₃) :
    #{s ∈ Q.unorderedSupport | H.color s = c} =
      #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} := by
  have hinj := hP.injOn_ofFinEmb.mono Q.support_subset
  rw [unorderedSupport_def, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]

end Subpolyad3

end TauCeti
