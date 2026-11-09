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
The adjacent-terminal form of Menger's theorem removes that unique direct edge, finds the same
one-vertex separator, and restores the direct edge as a second internally disjoint path. Thus its
finiteness assumption concerns only the direct terminal edges, not the entire edge set.
-/

public section

open Finset Set
open scoped Graph

namespace Graph

private def infiniteParallelPathEnds (e : Bool × ℕ) : Sym2 (Fin 3) :=
  if e.1 then s(1, 2) else s(0, 1)

/-- A three-vertex path with countably many parallel edges on each of its two links. -/
def infiniteParallelPath : Graph (Fin 3) (Bool × ℕ) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := s(x, y) = infiniteParallelPathEnds e
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
      rcases e with ⟨b, n⟩
      cases b
      · exact ⟨0, 1, rfl⟩
      · exact ⟨1, 2, rfl⟩
    · simp
  left_mem_of_isLink := by simp

@[simp]
private theorem infiniteParallelPath_isLink (e : Bool × ℕ) (x y : Fin 3) :
    infiniteParallelPath.IsLink e x y ↔ s(x, y) = infiniteParallelPathEnds e :=
  Iff.rfl

private theorem infiniteParallelPath_isLink_zero_one :
    infiniteParallelPath.IsLink (false, 0) (0 : Fin 3) 1 := by
  simp [infiniteParallelPathEnds]

private theorem infiniteParallelPath_isLink_one_two :
    infiniteParallelPath.IsLink (true, 0) (1 : Fin 3) 2 := by
  simp [infiniteParallelPathEnds]

private def infiniteParallelPathWalkZeroOne :
    infiniteParallelPath.Walk (0 : Fin 3) 1 :=
  .cons (false, 0) infiniteParallelPath_isLink_zero_one .nil

private def infiniteParallelPathWalkOneTwo :
    infiniteParallelPath.Walk (1 : Fin 3) 2 :=
  .cons (true, 0) infiniteParallelPath_isLink_one_two .nil

private def infiniteParallelPathWalk :
    infiniteParallelPath.Walk (0 : Fin 3) 2 :=
  infiniteParallelPathWalkZeroOne.append infiniteParallelPathWalkOneTwo

private theorem one_mem_infiniteParallelPathWalkSupport
    (p : infiniteParallelPath.Walk (0 : Fin 3) 2) : (1 : Fin 3) ∈ p.support := by
  cases p with
  | @cons _ y _ e h p =>
      rcases e with ⟨b, n⟩
      cases b
      · have hy : y = 1 := by
          change s(0, y) = s(0, 1) at h
          simpa [Sym2.eq_iff] using h
        rw [Walk.support_cons, List.mem_cons]
        exact Or.inr (hy ▸ p.start_mem_support)
      · change s(0, y) = s(1, 2) at h
        simp at h

private theorem infiniteParallelPath_connected : infiniteParallelPath.Connected := by
  refine connected_iff_forall_reachable.mpr ⟨Set.univ_nonempty, ?_⟩
  intro x y _ _
  fin_cases x <;> fin_cases y
  · exact (Walk.nil : infiniteParallelPath.Walk 0 0).reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalkZeroOne.reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalk.reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalkZeroOne.reverse.reachable (Set.mem_univ _)
  · exact (Walk.nil : infiniteParallelPath.Walk 1 1).reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalkOneTwo.reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalk.reverse.reachable (Set.mem_univ _)
  · exact infiniteParallelPathWalkOneTwo.reverse.reachable (Set.mem_univ _)
  · exact (Walk.nil : infiniteParallelPath.Walk 2 2).reachable (Set.mem_univ _)

private theorem infiniteParallelPath_not_reachable_delete_one :
    ¬(infiniteParallelPath.deleteVerts ({1} : Set (Fin 3))).Reachable 0 2 := by
  intro h
  obtain ⟨p, -, hp⟩ := reachable_deleteVerts_iff_exists_walk.mp h
  exact hp 1 (one_mem_infiniteParallelPathWalkSupport p) (by simp)

/-- The example really has infinitely many actual edges, although its actual vertex type is
finite. -/
example : Infinite E(infiniteParallelPath) := by
  change Infinite {e : Bool × ℕ // e ∈ (Set.univ : Set (Bool × ℕ))}
  exact Set.infinite_coe_iff.mpr Set.infinite_univ

/-- The infinite-edge three-vertex path is connected but not `2`-vertex-connected. -/
example :
    infiniteParallelPath.IsVertexConnected 1 ∧
      ¬infiniteParallelPath.IsVertexConnected 2 := by
  constructor
  · exact isVertexConnected_one.mpr
      ⟨infiniteParallelPath_connected, ⟨0, Set.mem_univ _, 1, Set.mem_univ _, by decide⟩⟩
  · intro h
    have hreach := h.isVertexReachable
      (⟨0, by simp [infiniteParallelPath]⟩ : V(infiniteParallelPath))
      (⟨2, by simp [infiniteParallelPath]⟩ : V(infiniteParallelPath))
    have hreach' := (Graph.isVertexReachable_iff (G := infiniteParallelPath) (k := 2)).mp hreach
    exact infiniteParallelPath_not_reachable_delete_one
      (hreach' (X := {1}) (by norm_num) (by decide) (by decide))

private theorem infiniteParallelPath_not_adj_zero_two :
    ¬infiniteParallelPath.Adj (0 : Fin 3) 2 := by
  rintro ⟨e, he⟩
  rcases e with ⟨b, n⟩
  cases b <;> simp [infiniteParallelPathEnds] at he

/-- Nonadjacent vertex Menger gives one path and the one-vertex separator `{1}` without any
finiteness assumption on the actual edge set. -/
example :
    (∃ P : Fin 1 → infiniteParallelPath.Walk 0 2,
      (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      ¬(infiniteParallelPath.deleteVerts ({1} : Set (Fin 3))).Reachable 0 2 := by
  refine ⟨?_, infiniteParallelPath_not_reachable_delete_one⟩
  rw [← forall_reachable_deleteVerts_iff_exists_paths (G := infiniteParallelPath)
    (s := (0 : Fin 3)) (t := 2) (by decide) infiniteParallelPath_not_adj_zero_two 1]
  intro X _ _ hX
  have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
  subst X
  simpa only [Finset.coe_empty, deleteVerts_empty] using
    infiniteParallelPathWalk.reachable (by simp [infiniteParallelPath])

private def infiniteParallelPathWithDirectEnds (e : Option (Bool × ℕ)) : Sym2 (Fin 3) :=
  match e with
  | none => s(0, 2)
  | some e => infiniteParallelPathEnds e

/-- The infinite parallel path together with one direct edge between its endpoints. -/
def infiniteParallelPathWithDirect : Graph (Fin 3) (Option (Bool × ℕ)) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := s(x, y) = infiniteParallelPathWithDirectEnds e
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
      rcases e with _ | ⟨b, n⟩
      · exact ⟨0, 2, rfl⟩
      · cases b
        · exact ⟨0, 1, rfl⟩
        · exact ⟨1, 2, rfl⟩
    · simp
  left_mem_of_isLink := by simp

@[simp]
private theorem infiniteParallelPathWithDirect_isLink (e : Option (Bool × ℕ))
    (x y : Fin 3) :
    infiniteParallelPathWithDirect.IsLink e x y ↔
      s(x, y) = infiniteParallelPathWithDirectEnds e :=
  Iff.rfl

private def directEdgeEquiv :
    {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none, rfl⟩
  left_inv e := by
    apply Subtype.ext
    rcases e with ⟨e, he⟩
    rcases e with _ | ⟨b, n⟩
    · rfl
    · cases b <;> simp [infiniteParallelPathWithDirectEnds,
        infiniteParallelPathEnds] at he
  right_inv _ := rfl

private theorem infiniteParallelPathWithDirect_isLink_zero_one :
    infiniteParallelPathWithDirect.IsLink (some (false, 0)) (0 : Fin 3) 1 := by
  simp [infiniteParallelPathWithDirectEnds, infiniteParallelPathEnds]

private theorem infiniteParallelPathWithDirect_isLink_one_two :
    infiniteParallelPathWithDirect.IsLink (some (true, 0)) (1 : Fin 3) 2 := by
  simp [infiniteParallelPathWithDirectEnds, infiniteParallelPathEnds]

private def infiniteParallelPathWithDirectWalkZeroOne :
    infiniteParallelPathWithDirect.Walk (0 : Fin 3) 1 :=
  .cons (some (false, 0)) infiniteParallelPathWithDirect_isLink_zero_one .nil

private def infiniteParallelPathWithDirectWalkOneTwo :
    infiniteParallelPathWithDirect.Walk (1 : Fin 3) 2 :=
  .cons (some (true, 0)) infiniteParallelPathWithDirect_isLink_one_two .nil

private def infiniteParallelPathWithDirectWalk :
    infiniteParallelPathWithDirect.Walk (0 : Fin 3) 2 :=
  infiniteParallelPathWithDirectWalkZeroOne.append infiniteParallelPathWithDirectWalkOneTwo

/-- The augmented example still has infinitely many edges, but exactly one of them directly joins
the two terminals. -/
example : Infinite E(infiniteParallelPathWithDirect) ∧
    Nat.card {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} = 1 := by
  constructor
  · change Infinite {e : Option (Bool × ℕ) // e ∈
      (Set.univ : Set (Option (Bool × ℕ)))}
    exact Set.infinite_coe_iff.mpr Set.infinite_univ
  · rw [Nat.card_congr directEdgeEquiv]
    simp

/-- Adjacent-terminal Menger returns one path through the middle vertex in addition to the unique
direct path, while requiring finiteness only of the direct-edge subtype. -/
example :
    ∃ P : Fin 1 ⊕
        {e : Option (Bool × ℕ) // infiniteParallelPathWithDirect.IsLink e 0 2} →
          infiniteParallelPathWithDirect.Walk 0 2,
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  let _ : Finite {e : Option (Bool × ℕ) //
      infiniteParallelPathWithDirect.IsLink e 0 2} :=
    Finite.of_equiv Unit directEdgeEquiv.symm
  rw [← forall_reachable_deleteEdges_deleteVerts_iff_exists_paths
    (G := infiniteParallelPathWithDirect) (s := (0 : Fin 3)) (t := 2) (by decide) 1]
  intro X _ _ hX
  have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
  subst X
  rw [Finset.coe_empty, deleteVerts_empty]
  refine reachable_deleteEdges_iff_exists_walk.mpr ⟨by simp [infiniteParallelPathWithDirect],
    infiniteParallelPathWithDirectWalk, ?_⟩
  intro e he hdirect
  rcases e with _ | ⟨b, n⟩
  · simp [infiniteParallelPathWithDirectWalk, infiniteParallelPathWithDirectWalkZeroOne,
      infiniteParallelPathWithDirectWalkOneTwo] at he
  · cases b <;> simp [infiniteParallelPathWithDirectEnds, infiniteParallelPathEnds] at hdirect

end Graph
