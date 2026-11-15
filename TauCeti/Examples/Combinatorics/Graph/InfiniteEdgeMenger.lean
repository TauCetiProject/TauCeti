/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Menger.Adjacent
import Mathlib.Tactic.FinCases

/-!
# Vertex Menger examples with infinitely many edges

These examples exercise vertex Menger's theorem on three actual vertices and infinitely many
parallel edges. The first graph has countably many edges from `0` to `1` and from `1` to `2`.
Deleting vertex `1` separates the nonadjacent endpoints, so their maximum internally disjoint
path family has one member even though the graph has no finite edge set.

The second graph adds one edge from `0` to `2` while retaining the two infinite parallel families.
After deleting that edge, removing vertex `1` separates the endpoints. The adjacent-terminal form
of Menger's theorem therefore gives exactly one path through the middle vertex together with the
unique direct path. Its finiteness assumption concerns only the direct terminal edges, not the
entire edge set.
-/

open Finset Set
open Graph
open scoped Graph

namespace TauCeti.Examples.InfiniteEdgeMenger

/-- The common graph constructor used by the two infinite-edge examples. -/
public def graphOfEnds {β : Type*}
    (ends : β → Sym2 (Fin 3)) : Graph (Fin 3) β where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := s(x, y) = ends e
  isLink_symm := by
    intro e _
    exact ⟨fun x y hxy ↦ by rw [Sym2.eq_swap]; exact hxy⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases Sym2.eq_iff.mp (hxy.trans hvw.symm) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      exact (ends e).inductionOn fun x y ↦ ⟨x, y, rfl⟩
    · simp
  left_mem_of_isLink := by simp

@[simp]
public theorem graphOfEnds_isLink {β : Type*} (ends : β → Sym2 (Fin 3))
    (e : β) (x y : Fin 3) :
    (graphOfEnds ends).IsLink e x y ↔ s(x, y) = ends e :=
  (Iff.rfl)

@[simp]
public theorem edgeSet_graphOfEnds {β : Type*} (ends : β → Sym2 (Fin 3)) :
    E(graphOfEnds ends) = Set.univ :=
  (rfl)

@[simp]
public theorem vertexSet_graphOfEnds {β : Type*} (ends : β → Sym2 (Fin 3)) :
    V(graphOfEnds ends) = Set.univ :=
  (rfl)

private def pathWalk {β : Type*} (G : Graph (Fin 3) β) (e₀₁ e₁₂ : β)
    (h₀₁ : G.IsLink e₀₁ 0 1) (h₁₂ : G.IsLink e₁₂ 1 2) :
    G.Walk (0 : Fin 3) 2 :=
  h₀₁.toWalk.append h₁₂.toWalk

private abbrev infiniteParallelPathEnds (e : Bool × ℕ) : Sym2 (Fin 3) :=
  if e.1 then s(1, 2) else s(0, 1)

/-- A three-vertex path with countably many parallel edges on each of its two links. -/
public def infiniteParallelPath : Graph (Fin 3) (Bool × ℕ) :=
  graphOfEnds fun e ↦ if e.1 then s(1, 2) else s(0, 1)

@[simp]
public theorem infiniteParallelPath_isLink (e : Bool × ℕ) (x y : Fin 3) :
    infiniteParallelPath.IsLink e x y ↔
      s(x, y) = if e.1 then s(1, 2) else s(0, 1) :=
  (Iff.rfl)

@[simp]
public theorem edgeSet_infiniteParallelPath : E(infiniteParallelPath) = Set.univ :=
  (rfl)

@[simp]
public theorem vertexSet_infiniteParallelPath : V(infiniteParallelPath) = Set.univ :=
  (rfl)

private def infiniteParallelPathWalkZeroOne :
    infiniteParallelPath.Walk (0 : Fin 3) 1 :=
  (show infiniteParallelPath.IsLink (false, 0) 0 1 by simp).toWalk

private def infiniteParallelPathWalkOneTwo :
    infiniteParallelPath.Walk (1 : Fin 3) 2 :=
  (show infiniteParallelPath.IsLink (true, 0) 1 2 by simp).toWalk

private def infiniteParallelPathWalk :
    infiniteParallelPath.Walk (0 : Fin 3) 2 :=
  pathWalk infiniteParallelPath (false, 0) (true, 0) (by simp) (by simp)

private theorem one_mem_infiniteParallelPathWalkSupport
    (p : infiniteParallelPath.Walk (0 : Fin 3) 2) : (1 : Fin 3) ∈ p.support := by
  cases p with
  | @cons _ y _ e h p =>
      rcases e with ⟨b, n⟩
      cases b
      · have hy : y = 1 := by
          simp only [infiniteParallelPath_isLink, Bool.false_eq_true, ↓reduceIte] at h
          simpa [Sym2.eq_iff] using h
        rw [Walk.support_cons, List.mem_cons]
        exact Or.inr (hy ▸ p.start_mem_support)
      · simp at h

private theorem infiniteParallelPath_connected : infiniteParallelPath.Connected := by
  refine connected_iff_forall_reachable.mpr ⟨by simp, ?_⟩
  intro x y _ _
  fin_cases x <;> fin_cases y
  · exact (Walk.nil : infiniteParallelPath.Walk 0 0).reachable (by simp)
  · exact infiniteParallelPathWalkZeroOne.reachable (by simp)
  · exact infiniteParallelPathWalk.reachable (by simp)
  · exact infiniteParallelPathWalkZeroOne.reverse.reachable (by simp)
  · exact (Walk.nil : infiniteParallelPath.Walk 1 1).reachable (by simp)
  · exact infiniteParallelPathWalkOneTwo.reachable (by simp)
  · exact infiniteParallelPathWalk.reverse.reachable (by simp)
  · exact infiniteParallelPathWalkOneTwo.reverse.reachable (by simp)
  · exact (Walk.nil : infiniteParallelPath.Walk 2 2).reachable (by simp)

private theorem infiniteParallelPath_not_reachable_delete_one :
    ¬(infiniteParallelPath.deleteVerts ({1} : Set (Fin 3))).Reachable 0 2 := by
  intro h
  obtain ⟨p, -, hp⟩ := reachable_deleteVerts_iff_exists_walk.mp h
  exact hp 1 (one_mem_infiniteParallelPathWalkSupport p) (by simp)

/-- The example really has infinitely many actual edges, although its actual vertex type is
finite. -/
example : Infinite E(infiniteParallelPath) := by
  rw [edgeSet_infiniteParallelPath]
  exact Set.infinite_coe_iff.mpr Set.infinite_univ

/-- The infinite-edge three-vertex path is connected but not `2`-vertex-connected. -/
example :
    infiniteParallelPath.IsVertexConnected 1 ∧
      ¬infiniteParallelPath.IsVertexConnected 2 := by
  constructor
  · exact isVertexConnected_one.mpr
      ⟨infiniteParallelPath_connected, ⟨0, by simp, 1, by simp, by decide⟩⟩
  · intro h
    have hreach := h.isVertexReachable
      (⟨0, by simp⟩ : V(infiniteParallelPath))
      (⟨2, by simp⟩ : V(infiniteParallelPath))
    have hreach' := (Graph.isVertexReachable_iff (G := infiniteParallelPath) (k := 2)).mp hreach
    exact infiniteParallelPath_not_reachable_delete_one
      (hreach' (X := {1}) (by norm_num) (by decide) (by decide))

private theorem infiniteParallelPath_not_adj_zero_two :
    ¬infiniteParallelPath.Adj (0 : Fin 3) 2 := by
  rintro ⟨e, he⟩
  rcases e with ⟨b, n⟩
  cases b <;> simp at he

/-- Nonadjacent vertex Menger gives a one-path family; deleting `{1}` separates the terminals and
rules out a two-path family, without any finiteness assumption on the actual edge set. -/
example :
    (∃ P : Fin 1 → infiniteParallelPath.Walk 0 2,
      (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      ¬(infiniteParallelPath.deleteVerts ({1} : Set (Fin 3))).Reachable 0 2 ∧
      ¬∃ P : Fin 2 → infiniteParallelPath.Walk 0 2,
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨?_, infiniteParallelPath_not_reachable_delete_one, ?_⟩
  · rw [← forall_reachable_deleteVerts_iff_exists_paths (G := infiniteParallelPath)
      (s := (0 : Fin 3)) (t := 2) (by decide) infiniteParallelPath_not_adj_zero_two 1]
    intro X _ _ hX
    have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
    subst X
    simpa only [Finset.coe_empty, deleteVerts_empty] using
      infiniteParallelPathWalk.reachable (by simp)
  · rw [← forall_reachable_deleteVerts_iff_exists_paths (G := infiniteParallelPath)
      (s := (0 : Fin 3)) (t := 2) (by decide) infiniteParallelPath_not_adj_zero_two 2]
    intro h
    apply infiniteParallelPath_not_reachable_delete_one
    simpa using h {1} (by simp) (by simp) (by norm_num)

private abbrev infiniteParallelPathWithDirectEnds
    (e : Option (Bool × ℕ)) : Sym2 (Fin 3) :=
  match e with
  | none => s(0, 2)
  | some e => infiniteParallelPathEnds e

/-- The infinite parallel path together with one direct edge between its endpoints. -/
public def infiniteParallelPathWithDirect : Graph (Fin 3) (Option (Bool × ℕ)) :=
  graphOfEnds fun e ↦ match e with
    | none => s(0, 2)
    | some e => if e.1 then s(1, 2) else s(0, 1)

@[simp]
public theorem infiniteParallelPathWithDirect_isLink (e : Option (Bool × ℕ))
    (x y : Fin 3) :
    infiniteParallelPathWithDirect.IsLink e x y ↔
      s(x, y) = match e with
        | none => s(0, 2)
        | some e => if e.1 then s(1, 2) else s(0, 1) :=
  (Iff.rfl)

@[simp]
public theorem edgeSet_infiniteParallelPathWithDirect :
    E(infiniteParallelPathWithDirect) = Set.univ :=
  (rfl)

@[simp]
public theorem vertexSet_infiniteParallelPathWithDirect :
    V(infiniteParallelPathWithDirect) = Set.univ :=
  (rfl)

private def directEdgeEquiv :
    {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none, by
    simp⟩
  left_inv e := by
    apply Subtype.ext
    rcases e with ⟨e, he⟩
    rcases e with _ | ⟨b, n⟩
    · rfl
    · cases b <;> simp at he
  right_inv _ := rfl

private def infiniteParallelPathWithDirectWalk :
    infiniteParallelPathWithDirect.Walk (0 : Fin 3) 2 :=
  pathWalk infiniteParallelPathWithDirect (some (false, 0)) (some (true, 0))
    (by simp) (by simp)

private theorem one_mem_infiniteParallelPathWithDirectWalkSupportAfterDelete
    (p : (infiniteParallelPathWithDirect.deleteEdges
      {e | infiniteParallelPathWithDirect.IsLink e 0 2}).Walk (0 : Fin 3) 2) :
    (1 : Fin 3) ∈ p.support := by
  cases p with
  | @cons _ y _ e h p =>
      rcases e with _ | ⟨b, n⟩
      · simp at h
      · cases b
        · have hy : y = 1 := by
            simpa [Sym2.eq_iff] using h.1
          rw [Walk.support_cons, List.mem_cons]
          exact Or.inr (hy ▸ p.start_mem_support)
        · simp at h

private theorem infiniteParallelPathWithDirect_not_reachable_delete_direct_delete_one :
    ¬((infiniteParallelPathWithDirect.deleteEdges
      {e | infiniteParallelPathWithDirect.IsLink e 0 2}).deleteVerts
        ({1} : Set (Fin 3))).Reachable 0 2 := by
  intro h
  obtain ⟨p, -, hp⟩ := reachable_deleteVerts_iff_exists_walk.mp h
  exact hp 1 (one_mem_infiniteParallelPathWithDirectWalkSupportAfterDelete p) (by simp)

/-- The augmented example still has infinitely many edges, but exactly one of them directly joins
the two terminals. -/
example : Infinite E(infiniteParallelPathWithDirect) ∧
    Nat.card {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} = 1 := by
  constructor
  · rw [edgeSet_infiniteParallelPathWithDirect]
    exact Set.infinite_coe_iff.mpr Set.infinite_univ
  · rw [Nat.card_congr directEdgeEquiv]
    simp

/-- Adjacent-terminal Menger returns one path through the middle vertex in addition to the unique
direct path. Deleting the direct edge and `{1}` rules out a second internal path, while the theorem
requires finiteness only of the direct-edge subtype. -/
example :
    (∃ P : Fin 1 ⊕
      {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} →
        infiniteParallelPathWithDirect.Walk 0 2,
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      ¬((infiniteParallelPathWithDirect.deleteEdges
        {e | infiniteParallelPathWithDirect.IsLink e 0 2}).deleteVerts
          ({1} : Set (Fin 3))).Reachable 0 2 ∧
      ¬∃ P : Fin 2 ⊕
        {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} →
          infiniteParallelPathWithDirect.Walk 0 2,
        Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  let _ : Finite {e : Option (Bool × ℕ) //
      infiniteParallelPathWithDirect.IsLink e 0 2} :=
    Finite.of_equiv Unit directEdgeEquiv.symm
  refine ⟨?_, infiniteParallelPathWithDirect_not_reachable_delete_direct_delete_one, ?_⟩
  · rw [← forall_reachable_deleteEdges_deleteVerts_iff_exists_paths
      (G := infiniteParallelPathWithDirect) (s := (0 : Fin 3)) (t := 2) (by decide) 1]
    intro X _ _ hX
    have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
    subst X
    rw [Finset.coe_empty, deleteVerts_empty]
    refine reachable_deleteEdges_iff_exists_walk.mpr
      ⟨by simp, infiniteParallelPathWithDirectWalk, ?_⟩
    intro e he hdirect
    rcases e with _ | ⟨b, n⟩
    · unfold infiniteParallelPathWithDirectWalk pathWalk at he
      simp at he
    · cases b <;> simp at hdirect
  · rw [← forall_reachable_deleteEdges_deleteVerts_iff_exists_paths
      (G := infiniteParallelPathWithDirect) (s := (0 : Fin 3)) (t := 2) (by decide) 2]
    intro h
    apply infiniteParallelPathWithDirect_not_reachable_delete_direct_delete_one
    simpa using h {1} (by simp) (by simp) (by norm_num)

end TauCeti.Examples.InfiniteEdgeMenger
