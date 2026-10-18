/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Sym

/-!
# Capacities of undirected cuts

This file defines the capacity of a cut for a function on unordered vertex pairs and for a
weighted multigraph.  For a multigraph, parallel edges contribute separately and loops never
contribute.  Aggregating the weights of all edges with the same unordered pair of distinct ends
therefore preserves every cut capacity.

The pair-capacity interface is useful when only cut values matter, while the multigraph interface
retains the identities of parallel and zero-capacity edges for path and deletion arguments.

## Main definitions

* `TauCeti.pairCutCapacity`: the capacity of a cut for weights on unordered vertex pairs.
* `TauCeti.capacitySupport`: the simple support graph of a pair-capacity function.
* `Graph.edgeCutCapacity`: the capacity of a cut in a weighted multigraph.
* `Graph.pairCapacity`: aggregation of multigraph edge weights by their distinct ends.

## Main result

* `Graph.pairCutCapacity_pairCapacity`: aggregation preserves every cut capacity.
-/

public section

open Finset

namespace Sym2

variable {V : Type*}

/-- An unordered pair crosses `S` when its two endpoints lie on opposite sides of `S`. -/
def Crosses (p : Sym2 V) (S : Set V) : Prop :=
  (∃ x ∈ p, x ∈ S) ∧ ∃ y ∈ p, y ∉ S

/-- A displayed unordered pair crosses a set exactly when its endpoints lie on opposite sides. -/
@[simp]
theorem crosses_mk_iff {S : Set V} {x y : V} :
    s(x, y).Crosses S ↔ (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S) := by
  simp only [Crosses, Sym2.mem_iff]
  aesop

/-- Crossing a set is unchanged by exchanging the set with its complement. -/
@[simp]
theorem crosses_compl (p : Sym2 V) (S : Set V) : p.Crosses Sᶜ ↔ p.Crosses S := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, Set.mem_compl_iff, not_not]
      tauto

/-- A diagonal unordered pair crosses no set. -/
@[simp]
theorem not_crosses_diag (x : V) (S : Set V) : ¬s(x, x).Crosses S := by
  simp

/-- A crossing unordered pair is not diagonal. -/
theorem Crosses.not_isDiag {p : Sym2 V} {S : Set V} (h : p.Crosses S) : ¬p.IsDiag := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, mk_isDiag_iff] at h ⊢
      rintro rfl
      simp at h

end Sym2

namespace TauCeti

variable {V K : Type*}

open Classical in
/-- The capacity of the undirected cut with source side `S` for weights on unordered vertex
pairs. Each crossing pair is counted once; diagonal pairs never cross. -/
noncomputable def pairCutCapacity [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) : K :=
  ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0

open Classical in
/-- The defining finite-sum formula for `pairCutCapacity`. -/
theorem pairCutCapacity_def [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    pairCutCapacity c S =
      ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0 :=
  (rfl)

open Classical in
/-- Pair cut capacity is unchanged when the two sides of the cut are exchanged. -/
@[simp]
theorem pairCutCapacity_compl [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    pairCutCapacity c Sᶜ = pairCutCapacity c S := by
  simp only [pairCutCapacity]
  apply sum_congr rfl
  intro p _
  have hcomp : (↑(Sᶜ) : Set V) = (↑S : Set V)ᶜ := by ext; simp
  rw [hcomp]
  rw [Sym2.crosses_compl]

/-- Diagonal values do not affect pair cut capacities. -/
theorem pairCutCapacity_eq_of_offDiagonal_eq [Fintype V] [AddCommMonoid K]
    (c d : Sym2 V → K) (h : ∀ x y, x ≠ y → c s(x, y) = d s(x, y)) :
    pairCutCapacity c = pairCutCapacity d := by
  funext S
  classical
  simp only [pairCutCapacity]
  apply sum_congr rfl
  intro p _
  induction p using Sym2.inductionOn with
  | _ x y =>
      split_ifs with hxy
      · exact h x y fun hEq ↦ by subst y; simp at hxy
      · rfl

/-- The simple support graph of a pair-capacity function. Diagonal capacities are ignored. -/
def capacitySupport [Zero K] [LT K] (c : Sym2 V → K) : SimpleGraph V where
  Adj x y := x ≠ y ∧ 0 < c s(x, y)
  symm := ⟨fun x y h ↦ ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

@[simp]
theorem capacitySupport_adj [Zero K] [LT K] (c : Sym2 V → K) (x y : V) :
    (capacitySupport c).Adj x y ↔ x ≠ y ∧ 0 < c s(x, y) :=
  Iff.rfl

/-- Changing only diagonal capacities does not change the support graph. -/
theorem capacitySupport_eq_of_offDiagonal_eq [Zero K] [LT K]
    (c d : Sym2 V → K) (h : ∀ x y, x ≠ y → c s(x, y) = d s(x, y)) :
    capacitySupport c = capacitySupport d := by
  ext x y
  simp only [capacitySupport_adj]
  by_cases hxy : x = y
  · simp [hxy]
  · rw [h x y hxy]

end TauCeti

namespace Graph

variable {V E K : Type*} (G : Graph V E)

private theorem edgeEnds_spec_nonempty (e : G.edgeSet) :
    Nonempty {p : Sym2 G.vertexSet //
      ∀ x y : G.vertexSet, p = s(x, y) ↔ G.IsLink e.1 x.1 y.1} := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  refine ⟨⟨s(⟨x, hxy.left_mem⟩, ⟨y, hxy.right_mem⟩), ?_⟩⟩
  intro u v
  rw [Sym2.eq_iff]
  simpa only [Subtype.ext_iff] using hxy.isLink_iff.symm

/-- The unordered pair of actual vertices at the ends of an actual edge. -/
noncomputable def edgeEnds (e : G.edgeSet) : Sym2 G.vertexSet :=
  (Classical.choice (edgeEnds_spec_nonempty G e)).1

/-- `edgeEnds` records exactly the `IsLink` relation of an actual edge. -/
@[simp]
theorem edgeEnds_eq_iff_isLink (e : G.edgeSet) (x y : G.vertexSet) :
    G.edgeEnds e = s(x, y) ↔ G.IsLink e.1 x.1 y.1 := by
  classical
  exact (Classical.choice (edgeEnds_spec_nonempty G e)).2 x y

/-- An actual edge crosses a vertex cut exactly when its unordered pair of ends crosses the
corresponding cut of actual vertices. -/
theorem edgeEnds_crosses_iff_mem_edgeCut (e : G.edgeSet) (S : Finset G.vertexSet) :
    (G.edgeEnds e).Crosses (S : Set G.vertexSet) ↔
      e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) := by
  classical
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  let x' : G.vertexSet := ⟨x, hxy.left_mem⟩
  let y' : G.vertexSet := ⟨y, hxy.right_mem⟩
  have hend : G.edgeEnds e = s(x', y') := (G.edgeEnds_eq_iff_isLink e x' y').2 hxy
  have himage (z : G.vertexSet) :
      z.1 ∈ Subtype.val '' (S : Set G.vertexSet) ↔ z ∈ S := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact (Subtype.ext hwz) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hximage : x ∈ Subtype.val '' (S : Set G.vertexSet) ↔ x' ∈ S := by
    simpa only [x'] using himage x'
  have hyimage : y ∈ Subtype.val '' (S : Set G.vertexSet) ↔ y' ∈ S := by
    simpa only [y'] using himage y'
  rw [hend, Sym2.crosses_mk_iff, hxy.mem_edgeCut_iff, hximage, hyimage]
  simp only [SetLike.mem_coe]

open Classical in
/-- The capacity of a cut in a weighted multigraph. Each actual crossing edge is counted once. -/
noncomputable def edgeCutCapacity [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (S : Finset G.vertexSet) : K :=
  ∑ e : G.edgeSet,
    if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0

open Classical in
/-- The defining finite-sum formula for `edgeCutCapacity`. -/
theorem edgeCutCapacity_def [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (S : Finset G.vertexSet) :
    G.edgeCutCapacity c S =
      ∑ e : G.edgeSet,
        if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0 :=
  (rfl)

open Classical in
/-- Aggregate edge weights by the unordered pair of their distinct ends. The capacity of every
diagonal pair is zero, so loops are discarded. -/
noncomputable def pairCapacity [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (p : Sym2 G.vertexSet) : K :=
  ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0

open Classical in
/-- The defining finite-sum formula for `pairCapacity`. -/
theorem pairCapacity_def [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) (p : Sym2 G.vertexSet) :
    G.pairCapacity c p =
      ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0 :=
  (rfl)

/-- Aggregated pair capacity vanishes on diagonal pairs, independently of loop weights. -/
theorem pairCapacity_eq_zero_of_isDiag [Fintype G.edgeSet] [AddCommMonoid K]
    (c : G.edgeSet → K) {p : Sym2 G.vertexSet} (hp : p.IsDiag) :
    G.pairCapacity c p = 0 := by
  classical
  rw [pairCapacity_def]
  apply sum_eq_zero
  intro e _
  simp [hp]

/-- Aggregating parallel edge weights by their distinct ends preserves every cut capacity. -/
theorem pairCutCapacity_pairCapacity [Fintype G.vertexSet] [Fintype G.edgeSet]
    [AddCommMonoid K] (c : G.edgeSet → K) (S : Finset G.vertexSet) :
    TauCeti.pairCutCapacity (G.pairCapacity c) S = G.edgeCutCapacity c S := by
  classical
  rw [TauCeti.pairCutCapacity_def, edgeCutCapacity_def]
  simp only [pairCapacity_def]
  calc
    (∑ p : Sym2 G.vertexSet,
        if p.Crosses (S : Set G.vertexSet) then
          ∑ e : G.edgeSet, if ¬p.IsDiag ∧ G.edgeEnds e = p then c e else 0 else 0) =
        ∑ p : Sym2 G.vertexSet, ∑ e : G.edgeSet,
          if p.Crosses (S : Set G.vertexSet) ∧ G.edgeEnds e = p
            then c e else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Crosses (S : Set G.vertexSet)
      · simp [hp, hp.not_isDiag]
      · simp [hp]
    _ = ∑ e : G.edgeSet, ∑ p : Sym2 G.vertexSet,
          if p.Crosses (S : Set G.vertexSet) ∧ G.edgeEnds e = p
            then c e else 0 := sum_comm
    _ = ∑ e : G.edgeSet,
          if (G.edgeEnds e).Crosses (S : Set G.vertexSet)
            then c e else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases he : (G.edgeEnds e).Crosses (S : Set G.vertexSet)
      · simp only [ite_eq_left he]
        rw [sum_eq_single (G.edgeEnds e)]
        · simp [he]
        · intro p _ hp
          have hne : G.edgeEnds e ≠ p := Ne.symm hp
          simp [hne]
        · simp
      · simp only [ite_eq_right he]
        apply sum_eq_zero
        intro p _
        by_cases hp : G.edgeEnds e = p
        · subst p
          simp [he]
        · simp [hp]
    _ = ∑ e : G.edgeSet,
          if e.1 ∈ G.edgeCut (Subtype.val '' (S : Set G.vertexSet)) then c e else 0 := by
      apply sum_congr rfl
      intro e _
      simp only [G.edgeEnds_crosses_iff_mem_edgeCut e S]

end Graph
