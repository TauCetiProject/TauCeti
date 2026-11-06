/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Data.Finset.Basic

/-!
# Cut-minimal graphs

A graph is cut-minimal if every cut contains at most as many edges as non-edges.
Equivalently, toggling all pairs across any cut cannot decrease its edge count.
This is the graph-theoretic minimality condition for binary cochains: a binary gauge
changes the edge set by symmetric difference with a cut.

The cut-minimality convention follows D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Section 2. The characterization here isolates the finite
edge-count identity, independently of any cochain or coefficient group.
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- The cut with sides `S` and `Sᶜ`, regarded as a graph on all vertices. -/
def cutGraph (S : Set V) : SimpleGraph V where
  Adj u v := (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)

@[simp] theorem cutGraph_adj (S : Set V) (u v : V) :
    (cutGraph S).Adj u v ↔ (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := Iff.rfl

@[simp] theorem cutGraph_empty : cutGraph (∅ : Set V) = ⊥ := by
  ext u v
  simp

@[simp] theorem cutGraph_univ : cutGraph (Set.univ : Set V) = ⊥ := by
  ext u v
  simp

/-- Exchanging the two sides does not change the cut. -/
@[simp] theorem cutGraph_compl (S : Set V) : cutGraph Sᶜ = cutGraph S := by
  ext u v
  simp only [cutGraph_adj, Set.mem_compl_iff]
  tauto

/-- Adding binary gauges corresponds to symmetric difference of their cuts. -/
theorem cutGraph_symmDiff (S T : Set V) :
    cutGraph (S ∆ T) = cutGraph S ∆ cutGraph T := by
  ext u v
  simp only [cutGraph_adj, symmDiff_def, Set.mem_union, Set.mem_sdiff,
    sup_adj, sdiff_adj]
  tauto

section Finite

variable [Fintype V] [DecidableEq V]

open Classical in
/-- Every cut contains at most as many edges of `G` as non-edges of `G`. -/
def IsCutMinimal (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G ⊓ cutGraph S).edgeFinset.card ≤ (cutGraph S \ G).edgeFinset.card

open Classical in
/-- The defining cut inequality for cut-minimality. -/
theorem isCutMinimal_iff (G : SimpleGraph V) :
    G.IsCutMinimal ↔
      ∀ S : Set V, (G ⊓ cutGraph S).edgeFinset.card ≤
        (cutGraph S \ G).edgeFinset.card := Iff.rfl

open Classical in
/-- Cut-minimality says that at most half of each cut consists of edges. -/
theorem isCutMinimal_iff_two_mul_card_inter_le (G : SimpleGraph V) :
    G.IsCutMinimal ↔ ∀ S : Set V,
      2 * (G.edgeFinset ∩ (cutGraph S).edgeFinset).card ≤ (cutGraph S).edgeFinset.card := by
  simp only [isCutMinimal_iff, edgeFinset_inf, edgeFinset_sdiff]
  apply forall_congr'
  intro S
  have h := Finset.card_sdiff_add_card_inter (cutGraph S).edgeFinset G.edgeFinset
  rw [Finset.inter_comm] at h
  omega

open Classical in
/-- A graph is cut-minimal exactly when switching any cut does not reduce its edge count.
This is the cardinality criterion used to identify minimal binary cochains. -/
theorem isCutMinimal_iff_card_le_card_symmDiff (G : SimpleGraph V) :
    G.IsCutMinimal ↔ ∀ S : Set V,
      G.edgeFinset.card ≤ (G.edgeFinset ∆ (cutGraph S).edgeFinset).card := by
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  apply forall_congr'
  intro S
  have h := Finset.card_symmDiff_add_two_mul_card_inter
    G.edgeFinset (cutGraph S).edgeFinset
  omega

/-- The empty graph is cut-minimal. -/
@[simp] theorem isCutMinimal_bot : (⊥ : SimpleGraph V).IsCutMinimal := by
  classical
  simp [isCutMinimal_iff]

end Finite

end SimpleGraph
