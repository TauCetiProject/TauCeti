/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Order.Partition.Equipartition

/-!
# Triadic complexes

A `TriadicComplex3 V` is the bounded-complexity object over which an arity-three regular
approximation of a coloring of the triples of `V` is measured. It chooses its own finite palette
`Fin C.pairColorCount` of pair colors, carries a lower skeleton over that palette (vertex cells and
a coherent pair coloring), and selects a finite family of polyads over that skeleton.

Its complexity `C.complexity` is the number of vertex cells plus the number of pair colors plus
the number of selected polyads, so it bounds each of these quantities. Since the selected polyads
are polyads over the skeleton, the complexity is in turn bounded in terms of the lower data alone.

Forgetting colors and roles, `C.toHypergraphComplex` is a hypergraph complex of rank three: its
levels zero, one and two are complete, since the pair coloring is total, and its level three
consists of the underlying unordered triples of the selected polyad supports.

`C.IsPolyadDecomposition` says that every injective triple lies in the support of a selected
polyad. As distinct polyads have disjoint supports, the selected supports then partition the
`|V| (|V| - 1) (|V| - 2)` injective triples. `C.VertexCellsControlled t₀` says that the vertex cells
form an equipartition with at least `t₀` cells; each cell then has at most `|V| / t₀ + 1`
vertices.

Finally, for a coloring `H` of the triples, `H.exceptionalPolyadMass C η r` is the proportion of
the selected support carried by polyads over which `H` is not `(η, r)`-top-regular, and
`H.TopRegularOverMostPolyads C η ε r` bounds this proportion by `ε`.

## Main definitions

* `TauCeti.TriadicComplex3`: a lower skeleton over a chosen pair palette with selected polyads.
* `TauCeti.TriadicComplex3.complexity`: vertex cells plus pair colors plus polyads.
* `TauCeti.TriadicComplex3.toHypergraphComplex`: the underlying hypergraph complex of rank three.
* `TauCeti.TriadicComplex3.IsPolyadDecomposition`: the selected polyads cover all injective
  triples.
* `TauCeti.TriadicComplex3.VertexCellsControlled`: equitable vertex cells, at least `t₀` of them.
* `TauCeti.Colored3Graph.exceptionalPolyadMass`: the support proportion of irregular polyads.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads`: top regularity off an `ε`-proportion.

## Main results

* `TauCeti.TriadicComplex3.complexity_le`: the complexity is bounded by the lower data.
* `TauCeti.TriadicComplex3.faces_three`: the triple faces are the selected support triples.
* `TauCeti.TriadicComplex3.isPolyadDecomposition_iff_forall_mem_of_nonempty`: a polyad
  family is a decomposition exactly when it contains every polyad with nonempty support.
* `TauCeti.TriadicComplex3.IsPolyadDecomposition.sum_card_support`: the selected supports have
  `|V|.descFactorial 3` triples in total.
* `TauCeti.TriadicComplex3.VertexCellsControlled.card_le`: controlled cells are small.
* `TauCeti.Colored3Graph.topRegularOverMostPolyads_iff_sum_card_support_le`: the support of
  the irregular polyads is at most an `ε`-proportion of the selected support.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A triadic complex on `V`: a finite palette of `pairColorCount` pair colors chosen by the
complex, a lower skeleton over that palette, and a finite family of polyads over that skeleton. -/
structure TriadicComplex3 (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The number of pair colors in the lower palette. -/
  pairColorCount : ℕ
  /-- The lower skeleton: vertex cells and a coherent coloring of distinct pairs. -/
  skeleton : PairSkeleton3 (Fin pairColorCount) V
  /-- The selected polyads over the lower skeleton. -/
  polyads : Finset (Polyad3 skeleton)

namespace TriadicComplex3

variable (C : TriadicComplex3 V)

/-! ### Complexity -/

/-- The complexity of a triadic complex: the number of vertex cells, plus the number of pair
colors, plus the number of selected polyads. -/
def complexity : ℕ :=
  #C.skeleton.vertexPart.parts + C.pairColorCount + #C.polyads

/-- The complexity is vertex cells plus pair colors plus polyads. -/
theorem complexity_def :
    C.complexity = #C.skeleton.vertexPart.parts + C.pairColorCount + #C.polyads :=
  (rfl)

/-- The complexity bounds the number of vertex cells. -/
theorem card_parts_le_complexity : #C.skeleton.vertexPart.parts ≤ C.complexity := by
  rw [complexity_def]
  omega

/-- The complexity bounds the number of pair colors. -/
theorem pairColorCount_le_complexity : C.pairColorCount ≤ C.complexity := by
  rw [complexity_def]
  omega

/-- The complexity bounds the number of selected polyads. -/
theorem card_polyads_le_complexity : #C.polyads ≤ C.complexity := by
  rw [complexity_def]
  omega

/-- The complexity is bounded in terms of the lower data alone: with `t` vertex cells and `q`
pair colors there are at most `t³ q³` polyads. -/
theorem complexity_le :
    C.complexity ≤ #C.skeleton.vertexPart.parts + C.pairColorCount +
      #C.skeleton.vertexPart.parts ^ 3 * C.pairColorCount ^ 3 := by
  have h := (card_le_univ C.polyads).trans (card_polyad3_le C.skeleton)
  rw [Fintype.card_fin] at h
  rw [complexity_def]
  omega

/-! ### The underlying hypergraph complex -/

/-- The unordered triples underlying the supports of the selected polyads. -/
noncomputable def topFaces : Finset (Finset V) :=
  C.polyads.biUnion fun P ↦ P.support.image fun x ↦
    (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩).val

/-- A top face is the underlying triple of a triple supported by a selected polyad. -/
@[simp]
theorem mem_topFaces {s : Finset V} :
    s ∈ C.topFaces ↔ ∃ P ∈ C.polyads, ∃ x ∈ P.support, univ.map ⟨x.1, x.2⟩ = s := by
  simp [topFaces]

/-- Every top face has three elements. -/
theorem card_eq_three_of_mem_topFaces {s : Finset V} (hs : s ∈ C.topFaces) : #s = 3 := by
  obtain ⟨-, -, x, -, rfl⟩ := C.mem_topFaces.1 hs
  simp

/-- The hypergraph complex of rank three underlying a triadic complex. Its levels zero, one and
two contain all sets of the corresponding size, since the pair coloring is total; its level three
consists of the unordered triples underlying the selected polyad supports. Level zero is `{∅}`,
as in every hypergraph complex (`HypergraphComplex.faces_zero`). -/
noncomputable def toHypergraphComplex : HypergraphComplex 3 V where
  faces k _ := {s ∈ univ.powersetCard k | k ≤ 2 ∨ s ∈ C.topFaces}
  face_card _ _ _ hs := (mem_powersetCard.1 (mem_filter.1 hs).1).2
  down_closed k hk s hs t hts ht := by
    obtain ⟨hs, hface⟩ := mem_filter.1 hs
    rw [mem_powersetCard] at hs
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, rfl⟩, ?_⟩
    by_cases ht₂ : #t ≤ 2
    · exact Or.inl ht₂
    · -- A subset with at least three elements of a face of size at most three is the face.
      obtain rfl : t = s := eq_of_subset_of_card_le hts (by omega)
      exact Or.inr (hface.resolve_left (by omega))
  empty_mem := by simp

/-- Membership in a level of the underlying hypergraph complex. -/
@[simp]
theorem mem_faces_toHypergraphComplex {k : ℕ} (hk : k ≤ 3) {s : Finset V} :
    s ∈ C.toHypergraphComplex.faces k hk ↔ #s = k ∧ (k ≤ 2 ∨ s ∈ C.topFaces) := by
  simp [toHypergraphComplex]

/-- Every vertex is a face of the underlying hypergraph complex. -/
theorem faces_one : C.toHypergraphComplex.faces 1 (by decide) = univ.powersetCard 1 := by
  ext s
  simp

/-- Every unordered pair of distinct vertices is a face of the underlying hypergraph complex. -/
theorem faces_two : C.toHypergraphComplex.faces 2 (by decide) = univ.powersetCard 2 := by
  ext s
  simp

/-- The triple faces of the underlying hypergraph complex are exactly the unordered triples
underlying the selected polyad supports. -/
theorem faces_three : C.toHypergraphComplex.faces 3 (by decide) = C.topFaces := by
  ext s
  simp only [mem_faces_toHypergraphComplex, show ¬3 ≤ 2 by decide, false_or]
  exact ⟨And.right, fun hs ↦ ⟨C.card_eq_three_of_mem_topFaces hs, hs⟩⟩

/-! ### Polyad decompositions -/

/-- The selected polyads decompose the injective triples: every injective triple lies in the
support of a selected polyad. Distinct polyads have disjoint supports
(`Polyad3.pairwise_disjoint_support`), so this polyad is unique. -/
def IsPolyadDecomposition : Prop :=
  ∀ x : {x : Fin 3 → V // Function.Injective x}, ∃ P ∈ C.polyads, x ∈ P.support

/-- Unfolded form of `TriadicComplex3.IsPolyadDecomposition`. -/
theorem isPolyadDecomposition_iff :
    C.IsPolyadDecomposition ↔
      ∀ x : {x : Fin 3 → V // Function.Injective x}, ∃ P ∈ C.polyads, x ∈ P.support :=
  Iff.rfl

/-- The selected polyads form a decomposition exactly when they contain the polyad of every
injective triple. -/
theorem isPolyadDecomposition_iff_ofTriple_mem :
    C.IsPolyadDecomposition ↔ ∀ x, Polyad3.ofTriple C.skeleton x ∈ C.polyads := by
  refine forall_congr' fun x ↦ ⟨?_, fun h ↦ ⟨_, h, Polyad3.mem_support_ofTriple x⟩⟩
  rintro ⟨P, hP, hx⟩
  rwa [← Polyad3.mem_support_iff_eq_ofTriple.1 hx]

/-- The selected polyads form a decomposition exactly when they contain every polyad over the
skeleton with nonempty support. -/
theorem isPolyadDecomposition_iff_forall_mem_of_nonempty :
    C.IsPolyadDecomposition ↔ ∀ P : Polyad3 C.skeleton, P.support.Nonempty → P ∈ C.polyads := by
  rw [isPolyadDecomposition_iff_ofTriple_mem]
  refine ⟨fun h P ⟨x, hx⟩ ↦ ?_, fun h x ↦ h _ ⟨x, Polyad3.mem_support_ofTriple x⟩⟩
  rw [Polyad3.mem_support_iff_eq_ofTriple.1 hx]
  exact h x

variable {C}

/-- In a polyad decomposition, every injective triple lies in exactly one selected polyad. -/
theorem IsPolyadDecomposition.existsUnique (h : C.IsPolyadDecomposition)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    ∃! P, P ∈ C.polyads ∧ x ∈ P.support := by
  obtain ⟨P, hP, hx⟩ := h x
  refine ⟨P, ⟨hP, hx⟩, fun Q hQ ↦ ?_⟩
  rw [Polyad3.mem_support_iff_eq_ofTriple.1 hQ.2, Polyad3.mem_support_iff_eq_ofTriple.1 hx]

/-- The supports of the selected polyads of a decomposition contain `|V| (|V| - 1) (|V| - 2)`
triples in total, the number of injective triples. -/
theorem IsPolyadDecomposition.sum_card_support (h : C.IsPolyadDecomposition) :
    ∑ P ∈ C.polyads, #P.support = (Fintype.card V).descFactorial 3 := by
  rw [← card_biUnion fun P _ Q _ hPQ ↦ Polyad3.pairwise_disjoint_support hPQ]
  have hU : C.polyads.biUnion Polyad3.support = univ :=
    eq_univ_of_forall fun x ↦ mem_biUnion.2 (h x)
  rw [hU, card_univ, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin]

variable (C)

/-! ### Controlled vertex cells -/

/-- The vertex cells are controlled at `t₀`: they form an equipartition with at least `t₀`
cells. -/
def VertexCellsControlled (t₀ : ℕ) : Prop :=
  C.skeleton.vertexPart.IsEquipartition ∧ t₀ ≤ #C.skeleton.vertexPart.parts

variable {C} {t₀ t : ℕ}

/-- Unfolded form of `TriadicComplex3.VertexCellsControlled`. -/
theorem vertexCellsControlled_iff :
    C.VertexCellsControlled t₀ ↔
      C.skeleton.vertexPart.IsEquipartition ∧ t₀ ≤ #C.skeleton.vertexPart.parts :=
  Iff.rfl

/-- Control at `t₀` implies control at every smaller floor. -/
theorem VertexCellsControlled.mono (h : C.VertexCellsControlled t₀) (ht : t ≤ t₀) :
    C.VertexCellsControlled t :=
  ⟨h.1, ht.trans h.2⟩

/-- Every vertex cell of a complex controlled at a positive floor `t₀` has at most
`|V| / t₀ + 1` vertices. -/
theorem VertexCellsControlled.card_le (h : C.VertexCellsControlled t₀) (ht₀ : 0 < t₀)
    {A : Finset V} (hA : A ∈ C.skeleton.vertexPart.parts) : #A ≤ Fintype.card V / t₀ + 1 := by
  have hle := h.1.card_part_le_average_add_one hA
  rw [card_univ] at hle
  exact hle.trans (Nat.add_le_add_right (Nat.div_le_div_left h.2 ht₀) 1)

end TriadicComplex3

/-! ### Exceptional polyads -/

namespace Colored3Graph

variable {κ : Type*} [DecidableEq κ] (H : Colored3Graph κ V) (C : TriadicComplex3 V)

open Classical in
/-- The exceptional polyad mass of a coloring `H` over a triadic complex `C`: the proportion of
the total support of the selected polyads carried by those over which `H` is not
`(η, r)`-top-regular. It is `0` when the selected polyads have empty supports. -/
noncomputable def exceptionalPolyadMass (η : ℝ) (r : ℕ) : ℝ :=
  (∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ)) /
    ∑ P ∈ C.polyads, (#P.support : ℝ)

open Classical in
/-- The exceptional polyad mass is the support of the irregular polyads over the total
support. -/
theorem exceptionalPolyadMass_def (η : ℝ) (r : ℕ) :
    H.exceptionalPolyadMass C η r =
      (∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ)) /
        ∑ P ∈ C.polyads, (#P.support : ℝ) :=
  (rfl)

variable {H C} {η η' ε ε' : ℝ} {r r' : ℕ}

/-- The exceptional polyad mass is nonnegative. -/
theorem exceptionalPolyadMass_nonneg : 0 ≤ H.exceptionalPolyadMass C η r := by
  classical
  rw [exceptionalPolyadMass_def]
  exact div_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)

/-- The exceptional polyad mass is at most one. -/
theorem exceptionalPolyadMass_le_one : H.exceptionalPolyadMass C η r ≤ 1 := by
  classical
  rw [exceptionalPolyadMass_def]
  exact div_le_one_of_le₀ (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)

/-- The exceptional polyad mass vanishes when `H` is top-regular over every selected polyad. -/
theorem exceptionalPolyadMass_eq_zero (h : ∀ P ∈ C.polyads, H.IsTopRegularOverPolyad P η r) :
    H.exceptionalPolyadMass C η r = 0 := by
  classical
  rw [exceptionalPolyadMass_def, filter_false_of_mem fun P hP ↦ not_not.2 (h P hP), sum_empty,
    zero_div]

/-- The exceptional polyad mass decreases as the regularity parameter grows and as the rank
drops. -/
theorem exceptionalPolyadMass_le_exceptionalPolyadMass (hη : η ≤ η') (hr : r' ≤ r) :
    H.exceptionalPolyadMass C η' r' ≤ H.exceptionalPolyadMass C η r := by
  classical
  rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
  refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_
    fun _ _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  intro P
  simp only [mem_filter]
  exact fun ⟨hP, h⟩ ↦ ⟨hP, fun h' ↦ h ((h'.of_rank_le hr).mono hη)⟩

variable (H C) in
/-- `H` is `(η, r)`-top-regular over most polyads of `C`: the polyads over which `H` is not
`(η, r)`-top-regular carry at most an `ε`-proportion of the selected support. -/
def TopRegularOverMostPolyads (η ε : ℝ) (r : ℕ) : Prop :=
  H.exceptionalPolyadMass C η r ≤ ε

/-- Unfolded form of `Colored3Graph.TopRegularOverMostPolyads`. -/
theorem topRegularOverMostPolyads_iff :
    H.TopRegularOverMostPolyads C η ε r ↔ H.exceptionalPolyadMass C η r ≤ ε :=
  Iff.rfl

open Classical in
/-- **Elimination form.** For `0 ≤ ε`, top regularity over most polyads says that the support of
the irregular selected polyads is at most `ε` times the total selected support. -/
theorem topRegularOverMostPolyads_iff_sum_card_support_le (hε : 0 ≤ ε) :
    H.TopRegularOverMostPolyads C η ε r ↔
      ∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ) ≤
        ε * ∑ P ∈ C.polyads, (#P.support : ℝ) := by
  rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_def]
  have hsub : ∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ) ≤
      ∑ P ∈ C.polyads, (#P.support : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ Nat.cast_nonneg _
  have hT : 0 ≤ ∑ P ∈ C.polyads, (#P.support : ℝ) := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  obtain h₀ | h₀ := hT.eq_or_lt
  · -- With empty total support, both sides hold trivially.
    rw [← h₀, div_zero, mul_zero]
    exact iff_of_true hε (h₀ ▸ hsub)
  · rw [div_le_iff₀ h₀, mul_comm]

/-- Top regularity over most polyads forces a nonnegative exceptional proportion. -/
theorem TopRegularOverMostPolyads.nonneg (h : H.TopRegularOverMostPolyads C η ε r) : 0 ≤ ε :=
  exceptionalPolyadMass_nonneg.trans h

open Classical in
/-- In a polyad decomposition, the irregular polyads of a coloring top-regular over most
polyads carry at most `ε |V| (|V| - 1) (|V| - 2)` injective triples. -/
theorem TopRegularOverMostPolyads.sum_card_support_le (h : H.TopRegularOverMostPolyads C η ε r)
    (hC : C.IsPolyadDecomposition) :
    ∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ) ≤
      ε * (Fintype.card V).descFactorial 3 := by
  rw [← hC.sum_card_support, Nat.cast_sum]
  exact (topRegularOverMostPolyads_iff_sum_card_support_le h.nonneg).1 h

/-- Top regularity over most polyads weakens as the regularity parameter and the exceptional
proportion grow and as the rank drops. -/
theorem TopRegularOverMostPolyads.mono (h : H.TopRegularOverMostPolyads C η ε r)
    (hη : η ≤ η') (hε : ε ≤ ε') (hr : r' ≤ r) : H.TopRegularOverMostPolyads C η' ε' r' :=
  ((exceptionalPolyadMass_le_exceptionalPolyadMass hη hr).trans h).trans hε

/-- A coloring top-regular over every selected polyad is top-regular over most polyads, for every
nonnegative exceptional proportion. -/
theorem topRegularOverMostPolyads_of_forall
    (h : ∀ P ∈ C.polyads, H.IsTopRegularOverPolyad P η r) (hε : 0 ≤ ε) :
    H.TopRegularOverMostPolyads C η ε r :=
  (exceptionalPolyadMass_eq_zero h).trans_le hε

variable (C r) in
/-- A constant coloring is top-regular over most polyads of every triadic complex, for every
positive regularity parameter and every nonnegative exceptional proportion. -/
theorem topRegularOverMostPolyads_const (c₀ : κ) (hη : 0 < η) (hε : 0 ≤ ε) :
    (const c₀ : Colored3Graph κ V).TopRegularOverMostPolyads C η ε r :=
  topRegularOverMostPolyads_of_forall (fun P _ ↦ isTopRegularOverPolyad_const P r c₀ hη) hε

end Colored3Graph

end TauCeti
