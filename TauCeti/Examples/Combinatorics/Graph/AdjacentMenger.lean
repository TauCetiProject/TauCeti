/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Menger.Adjacent
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Menger
public import TauCeti.Combinatorics.Network.Menger.Adjacent
public import TauCeti.Examples.Combinatorics.Graph.InfiniteEdgeMenger
import Mathlib.Tactic.FinCases

/-!
# Adjacent-terminal examples for Menger's theorem

These examples isolate the correction term in the vertex form of Menger's theorem when the
terminals are adjacent. Deleting nonterminal vertices never destroys a direct terminal edge, so
deletion-based vertex reachability alone does not measure the number of internally disjoint paths.

The complete graph on three vertices has arbitrarily high deletion threshold between two adjacent
vertices, but exactly two internally disjoint paths. A finite multigraph then shows that parallel
direct edges contribute separately. Finally, a directed example records that only arrows from the
source to the sink enter the correction term; arrows in the reverse direction remain in the
network but are not counted.
-/

public section

open Finset Set
open scoped Graph

namespace TauCeti.Examples.AdjacentMenger

/-! ## The complete graph on three vertices -/

/-- The complete simple graph on three vertices. -/
abbrev triangle : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)

private def triangleDirect : triangle.Walk 0 1 := by
  have h : triangle.Adj 0 1 := by simp
  exact h.toWalk

private def triangleThrough : triangle.Walk 0 1 := by
  have h₀₂ : triangle.Adj 0 2 := by simp
  have h₂₁ : triangle.Adj 2 1 := by simp
  exact h₀₂.toWalk.append h₂₁.toWalk

private def trianglePaths : Fin 2 → triangle.Walk 0 1
  | ⟨0, _⟩ => triangleDirect
  | ⟨1, _⟩ => triangleThrough

private theorem trianglePaths_injective : Function.Injective trianglePaths := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have := congrArg SimpleGraph.Walk.length hij
    simp [trianglePaths, triangleDirect, triangleThrough] at this
  · have := congrArg SimpleGraph.Walk.length hij
    simp [trianglePaths, triangleDirect, triangleThrough] at this
  · rfl

private theorem trianglePaths_isPath (i : Fin 2) : (trianglePaths i).IsPath := by
  fin_cases i
  · simp [trianglePaths, triangleDirect]
  · simp [trianglePaths, triangleThrough, SimpleGraph.Walk.isPath_def]

private theorem trianglePaths_pairwise :
    Pairwise fun i j ↦ (trianglePaths i).InternallyDisjoint (trianglePaths j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [trianglePaths, triangleDirect, triangleThrough,
    SimpleGraph.Walk.internallyDisjoint_def]

private theorem triangle_separator :
    ¬((triangle.deleteEdges {s(0, 1)}).induce ((↑({2} : Finset (Fin 3)))ᶜ)).Reachable
      ⟨0, by simp⟩ ⟨1, by simp⟩ := by
  have hbot : (triangle.deleteEdges {s(0, 1)}).induce ((↑({2} : Finset (Fin 3)))ᶜ) = ⊥ := by
    ext x y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_singleton] at hx hy
    fin_cases x <;> fin_cases y <;> simp_all
  rw [hbot]
  simp

/-- In the triangle, adjacent vertices remain vertex-reachable at every deletion threshold, while
the largest internally disjoint path family has exactly two members. -/
theorem triangle_reachability_and_path_count :
    (∀ k, triangle.IsVertexReachable k 0 1) ∧
      (∃ P : Fin 2 → triangle.Walk 0 1, Function.Injective P ∧
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      ∀ {I : Type*} [Fintype I] (P : I → triangle.Walk 0 1), Function.Injective P →
        (∀ i, (P i).IsPath) →
        (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) → Fintype.card I ≤ 2 := by
  have h₀₁ : triangle.Adj 0 1 := by simp
  refine ⟨fun _ ↦ h₀₁.isVertexReachable,
    ⟨trianglePaths, trianglePaths_injective, trianglePaths_isPath, trianglePaths_pairwise⟩, ?_⟩
  intro I _ P hinj hpath hdisj
  simpa using SimpleGraph.card_le_card_add_one_of_not_reachable_induce_deleteEdges
    hinj hpath hdisj (X := {2}) (by simp) (by simp) triangle_separator

/-! ## Parallel direct edges in a multigraph -/

/-- The endpoint pair of each edge in `parallelGraph`. -/
def parallelEnds : Fin 4 → Sym2 (Fin 3)
  | 0 | 1 => s(0, 2)
  | 2 => s(0, 1)
  | 3 => s(1, 2)

/-- Two parallel direct terminal edges together with a path through the third vertex. -/
def parallelGraph : Graph (Fin 3) (Fin 4) :=
  InfiniteEdgeMenger.graphOfEnds parallelEnds

@[simp]
theorem parallelGraph_isLink (e : Fin 4) (x y : Fin 3) :
    parallelGraph.IsLink e x y ↔ s(x, y) = parallelEnds e := by
  simp [parallelGraph]

@[simp]
theorem edgeSet_parallelGraph : E(parallelGraph) = Set.univ := by
  simp [parallelGraph]

@[simp]
theorem vertexSet_parallelGraph : V(parallelGraph) = Set.univ := by
  simp [parallelGraph]

private def parallelThrough : parallelGraph.Walk 0 2 := by
  have h₀₁ : parallelGraph.IsLink 2 0 1 := by simp [parallelEnds]
  have h₁₂ : parallelGraph.IsLink 3 1 2 := by simp [parallelEnds]
  exact h₀₁.toWalk.append h₁₂.toWalk

private theorem parallelThrough_survives_direct_deletion :
    (parallelGraph.deleteEdges {e | parallelGraph.IsLink e 0 2}).Reachable 0 2 := by
  refine Graph.reachable_deleteEdges_iff_exists_walk.mpr
    ⟨by simp [parallelGraph], parallelThrough, ?_⟩
  intro e he hlink
  fin_cases e <;> simp [parallelThrough] at he <;>
    simp [parallelEnds] at hlink

/-- Adjacent-terminal Menger produces one internal path in addition to the two parallel direct
paths, hence a family of three distinct internally disjoint paths. -/
theorem parallel_edges_add_to_internal_path :
    {e : Fin 4 | parallelGraph.IsLink e 0 2} = {0, 1} ∧
      ∃ P : Fin 1 ⊕ {e : Fin 4 // parallelGraph.IsLink e 0 2} → parallelGraph.Walk 0 2,
        Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  constructor
  · ext e
    fin_cases e <;> simp [parallelEnds]
  · let _ : Finite {e : Fin 4 // parallelGraph.IsLink e 0 2} := inferInstance
    rw [← Graph.forall_reachable_deleteEdges_deleteVerts_iff_exists_paths
      (G := parallelGraph) (s := (0 : Fin 3)) (t := 2) (by decide) 1]
    intro X _ _ hX
    have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
    subst X
    simpa using parallelThrough_survives_direct_deletion

/-! ## Only forward arrows enter the directed correction -/

/-- The five arrows in the directed adjacent-terminal example. -/
inductive DirectedHom : Fin 3 → Fin 3 → Type
  | forward₀ : DirectedHom 0 2
  | forward₁ : DirectedHom 0 2
  | reverse : DirectedHom 2 0
  | sourceMiddle : DirectedHom 0 1
  | middleSink : DirectedHom 1 2
  deriving DecidableEq

noncomputable instance {x y} : Fintype (DirectedHom x y) :=
  Fintype.ofInjective
    (fun e ↦ match e with
      | .forward₀ => (0 : Fin 5)
      | .forward₁ => 1
      | .reverse => 2
      | .sourceMiddle => 3
      | .middleSink => 4)
    fun e f h ↦ by cases e <;> cases f <;> simp_all

private def directedForwardEquiv : DirectedHom 0 2 ≃ Fin 2 where
  toFun
    | .forward₀ => 0
    | .forward₁ => 1
  invFun
    | 0 => .forward₀
    | 1 => .forward₁
  left_inv e := by cases e <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def directedReverseEquiv : DirectedHom 2 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .reverse
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

private def directedThrough : ArrowWalk DirectedHom 0 2 :=
  ((ArrowWalk.nil 0).cons DirectedHom.sourceMiddle).cons DirectedHom.middleSink

private theorem not_mixedSeparator_empty :
    ¬IsMixedSeparator ∅ (arrowFinset DirectedHom 0 2) 0 2 := by
  intro h
  simpa [directedThrough, ArrowWalk.arrows_cons, mem_arrowFinset] using
    h.exists_mem directedThrough

/-- The directed adjacent-terminal theorem counts the two arrows from source to sink, while the
single reverse arrow is retained but does not contribute to the correction term. -/
theorem directed_correction_counts_only_forward_arrows :
    Fintype.card (DirectedHom 0 2) = 2 ∧ Fintype.card (DirectedHom 2 0) = 1 ∧
      ∃ P : Fin 1 ⊕ DirectedHom 0 2 → ArrowWalk DirectedHom 0 2,
        Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨Fintype.card_congr directedForwardEquiv,
    Fintype.card_congr directedReverseEquiv, ?_⟩
  rw [← forall_not_isMixedSeparator_iff_exists_paths (Q := DirectedHom) (by decide) 1]
  intro X hX
  have hX0 : X = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp hX)
  simpa [hX0] using not_mixedSeparator_empty

end TauCeti.Examples.AdjacentMenger
