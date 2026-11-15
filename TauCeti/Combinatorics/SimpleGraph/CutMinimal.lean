/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Data.Finset.Basic

/-!
# Cut-minimal graphs

A graph is cut-minimal if every cut contains at most as many edges as non-edges.
Equivalently, toggling all pairs across any cut cannot decrease its edge count.
This is the graph-theoretic minimality condition for binary cochains: a binary gauge
changes the edge set by symmetric difference with a cut.

The cut-minimality convention follows D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Section 2. The characterizations here isolate isomorphism
invariance and the finite edge-count and vertex-count identities, independently of any cochain
or coefficient group.

## Main definitions and results

* `SimpleGraph.IsCutMinimal`: every cut `(S, Sᶜ)` contains at most as many edges as non-edges.
* `SimpleGraph.Iso.isCutMinimal_iff`: cut-minimality is invariant under graph isomorphism.
* `SimpleGraph.card_edgeFinset_top_between`: for disjoint `S` and `T`, the complete-graph
  restriction between `S` and `T` has `S.toFinset.card * T.toFinset.card` edges.
* `SimpleGraph.isCutMinimal_iff_two_mul_card_between_le`: finite cut-minimality in terms of
  vertex counts, `2 * (G.between S Sᶜ).edgeFinset.card ≤ S.toFinset.card * Sᶜ.toFinset.card`.
* `SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff`: switching any cut does not decrease the
  edge count.
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

section Finite

/-- Every cut contains at most as many edges of `G` as non-edges of `G`. -/
def IsCutMinimal (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.between S Sᶜ).edgeSet.encard ≤
    ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard

/-- The defining cut inequality for cut-minimality, with no finiteness assumptions. -/
theorem isCutMinimal_def (G : SimpleGraph V) :
    G.IsCutMinimal ↔ ∀ S : Set V, (G.between S Sᶜ).edgeSet.encard ≤
      ((⊤ : SimpleGraph V).between S Sᶜ \ G).edgeSet.encard := (Iff.rfl)

private theorem isCutMinimal_of_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (hG : G.IsCutMinimal) : H.IsCutMinimal := fun T ↦ by
  let S : Set V := f ⁻¹' T
  have hpre : Sᶜ = f ⁻¹' Tᶜ := rfl
  let iso₁ : G.between S Sᶜ ≃g H.between T Tᶜ :=
    { f.toEquiv with
      map_rel_iff' := fun {x y} ↦ by
        simp only [S, hpre, between_adj, Set.mem_preimage, RelIso.coe_fn_toEquiv, f.map_adj_iff] }
  let iso₂ : (⊤ : SimpleGraph V).between S Sᶜ \ G ≃g
      (⊤ : SimpleGraph W).between T Tᶜ \ H :=
    { f.toEquiv with
      map_rel_iff' := fun {x y} ↦ by
        simp only [S, hpre, sdiff_adj, between_adj, top_adj, Set.mem_preimage, ne_eq,
          RelIso.coe_fn_toEquiv, f.apply_eq_iff_eq, f.map_adj_iff] }
  rw [← Set.encard_congr iso₁.mapEdgeSet, ← Set.encard_congr iso₂.mapEdgeSet]
  exact hG S

/-- Cut-minimality is invariant under graph isomorphism. -/
theorem Iso.isCutMinimal_iff {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.IsCutMinimal ↔ H.IsCutMinimal :=
  ⟨isCutMinimal_of_iso f, isCutMinimal_of_iso f.symm⟩

variable [Fintype V] [DecidableEq V]

/-- The edge finset of `G.between S T` is the intersection of `G.edgeFinset` with the edges of the
complete graph between `S` and `T`. -/
theorem edgeFinset_between (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    (G.between S T).edgeFinset = G.edgeFinset ∩ ((⊤ : SimpleGraph V).between S T).edgeFinset := by
  rw [edgeFinset_inj.mpr (between_eq_inf_top_between G S T), edgeFinset_inf]

/-- For disjoint vertex sets `S` and `T`, the complete-graph restriction between `S` and `T` has
`S.toFinset.card * T.toFinset.card` edges. -/
theorem card_edgeFinset_top_between {S T : Set V} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hST : Disjoint S T) :
    ((⊤ : SimpleGraph V).between S T).edgeFinset.card = S.toFinset.card * T.toFinset.card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun (p : V × V) _ ↦ s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    rw [Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset] at hp
    rw [mem_edgeFinset, mem_edgeSet, between_adj, top_adj]
    exact ⟨hST.ne_of_mem hp.1 hp.2, Or.inl hp⟩
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ h
    rw [Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset] at hp₁ hp₂
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact False.elim (Set.disjoint_left.mp hST hp₁.1 hp₂.2)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet, between_adj, top_adj] at he
      rcases he.2 with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact ⟨(u, v), Finset.mem_product.mpr ⟨Set.mem_toFinset.mpr hu, Set.mem_toFinset.mpr hv⟩,
          rfl⟩
      · exact ⟨(v, u), Finset.mem_product.mpr ⟨Set.mem_toFinset.mpr hv, Set.mem_toFinset.mpr hu⟩,
          Sym2.eq_swap⟩

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
  rw [edgeFinset_between, edgeFinset_sdiff]
  have h := Finset.card_sdiff_add_card_inter
    ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset G.edgeFinset
  rw [Finset.inter_comm] at h
  omega

omit [DecidableEq V] in
/-- Cut-minimality in terms of vertex counts: twice the number of edges of `G` across `(S, Sᶜ)` is
at most `S.toFinset.card * Sᶜ.toFinset.card`. -/
theorem isCutMinimal_iff_two_mul_card_between_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ (S : Set V) [DecidablePred (· ∈ S)],
      2 * (G.between S Sᶜ).edgeFinset.card ≤ S.toFinset.card * Sᶜ.toFinset.card := by
  classical
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  refine forall_congr' fun S ↦ forall_congr' fun _ ↦ ?_
  rw [← edgeFinset_between, card_edgeFinset_top_between disjoint_compl_right]

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
