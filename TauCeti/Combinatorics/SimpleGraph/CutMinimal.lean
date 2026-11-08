/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
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

/-- The complete-graph cut of `S ∆ T` is the symmetric difference of the cuts of `S` and `T`. -/
theorem top_between_symmDiff (S T : Set V) :
    (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ =
      (⊤ : SimpleGraph V).between S Sᶜ ∆ (⊤ : SimpleGraph V).between T Tᶜ := by
  ext u v
  simp only [between_adj, top_adj, Set.mem_compl_iff, symmDiff_def, Set.mem_union,
    Set.mem_sdiff, sup_adj, sdiff_adj]
  tauto

/-- Restricting a graph to pairs between two sets is intersection with the corresponding
restriction of the complete graph. -/
theorem between_eq_inf_top_between (G : SimpleGraph V) (s t : Set V) :
    G.between s t = G ⊓ (⊤ : SimpleGraph V).between s t := by
  ext u v
  simp only [between_adj, inf_adj, top_adj]
  exact and_congr_right fun h ↦ (and_iff_right h.ne).symm

section Finite

/-- Every cut contains at most as many edges of `G` as non-edges of `G`. -/
def IsCutMinimal (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.between S Sᶜ).edgeSet.encard ≤
    ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard

variable [Fintype V] [DecidableEq V]

/-- The defining cut inequality for cut-minimality, using decidable edge finsets. -/
theorem isCutMinimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      ∀ (S : Set V) [DecidablePred (· ∈ S)], (G.between S Sᶜ).edgeFinset.card ≤
        ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeFinset.card := by
  have hcut (S : Set V) [DecidablePred (· ∈ S)] :
      (G.between S Sᶜ).edgeSet.encard ≤
          ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard ↔
        (G.between S Sᶜ).edgeFinset.card ≤
          ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeFinset.card := by
    rw [← coe_edgeFinset, ← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  constructor
  · intro h S _
    exact (hcut S).mp (h S)
  · intro h S
    -- The definition quantifies over all sets, without a decidability assumption.
    classical
    exact (hcut S).mpr (h S)

/-- Cut-minimality says that at most half of each cut consists of edges. -/
theorem isCutMinimal_iff_two_mul_card_inter_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      2 * (G.edgeFinset ∩ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset).card ≤
        ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset.card := by
  rw [isCutMinimal_iff]
  apply forall_congr'
  intro S
  apply forall_congr'
  intro _
  -- Lift the graph equality to finsets since the adjacency instances depend on the graph.
  have hfin : (G.between S Sᶜ).edgeFinset =
      (G ⊓ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset :=
    edgeFinset_inj.mpr (between_eq_inf_top_between G S Sᶜ)
  rw [hfin, edgeFinset_inf, edgeFinset_sdiff]
  have h := Finset.card_sdiff_add_card_inter
    ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset G.edgeFinset
  rw [Finset.inter_comm] at h
  omega

/-- A graph is cut-minimal exactly when switching any cut does not reduce its edge count.
This is the cardinality criterion used to identify minimal binary cochains. -/
theorem isCutMinimal_iff_card_le_card_symmDiff (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      G.edgeFinset.card ≤ (G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset).card := by
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  apply forall_congr'
  intro S
  apply forall_congr'
  intro _
  have h := Finset.card_symmDiff_add_two_mul_card_inter
    G.edgeFinset ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset
  omega

end Finite

/-- The empty graph is cut-minimal. -/
@[simp] theorem isCutMinimal_bot : (⊥ : SimpleGraph V).IsCutMinimal := by
  intro S
  have h : (⊥ : SimpleGraph V).between S Sᶜ = ⊥ := by
    ext u v
    simp [between_adj]
  simp [h]

end SimpleGraph
