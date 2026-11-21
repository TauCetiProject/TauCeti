/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import TauCeti.Combinatorics.SimpleGraph.Degree
import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.Data.Finset.Basic

/-!
# Cut-minimal graphs

A graph is cut-minimal if every cut contains at most as many edges as non-edges.
Equivalently, toggling all pairs across any cut cannot decrease its edge count.
This is the graph-theoretic minimality condition for binary cochains: a binary gauge
changes the edge set by symmetric difference with a cut.

On any finite vertex type, every graph can be switched by a finset cut to a cut-minimal graph
(`exists_finset_isCutMinimal_symmDiff_top_between`). Conversely, the only cut-minimal
complete-graph cut is `⊥` (`isCutMinimal_top_between_iff`), while a single edge
`SimpleGraph.edge u v` (`u ≠ v`) is cut-minimal precisely when a third vertex exists
(`isCutMinimal_edge_iff`). Evaluating cut-minimality on singleton cuts bounds every vertex degree
by `2 * G.degree v ≤ Fintype.card V - 1` (`IsCutMinimal.two_mul_degree_le`), whence
`2 * #G.edgeFinset ≤ Fintype.card V * ((Fintype.card V - 1) / 2)`
(`IsCutMinimal.two_mul_card_edgeFinset_le`). On at most four vertices, every cut-minimal graph
therefore has maximum degree at most `1`, at most two edges, and no `3`-clique.

The cut-minimality convention follows D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Section 2. The characterizations here isolate isomorphism
invariance and the finite edge-count and vertex-count criteria, independently of any cochain
or coefficient group.

## Main definitions and results

* `SimpleGraph.IsCutMinimal`: every cut `(S, Sᶜ)` contains at most as many edges as non-edges.
* `SimpleGraph.Iso.isCutMinimal_iff`: cut-minimality is invariant under graph isomorphism.
* `SimpleGraph.isCutMinimal_iff_two_mul_card_between_le`,
  `SimpleGraph.isCutMinimal_iff_two_mul_sum_card_le`: finite cut-minimality in terms of vertex
  and degree counts across cuts.
* `SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff`,
  `SimpleGraph.exists_finset_isCutMinimal_symmDiff_top_between`: switching any cut does not
  decrease the edge count, and every graph on a finite vertex type admits a cut-minimal finset
  switching.
* `SimpleGraph.isCutMinimal_top_between_iff`, `SimpleGraph.isCutMinimal_edge_iff`: cut-minimality
  of complete-graph cuts and single-edge graphs.
* `SimpleGraph.IsCutMinimal.two_mul_degree_le`,
  `SimpleGraph.IsCutMinimal.two_mul_card_edgeFinset_le`:
  singleton-cut degree and edge-count bounds for cut-minimal graphs.
-/

public section

open Finset
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

/-- Cut-minimality counted from one side of each cut: for every finite set `s`, twice the number
of edges from `s` to its complement is at most the number `#s * #sᶜ` of pairs across the cut. -/
theorem isCutMinimal_iff_two_mul_sum_card_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔ ∀ s : Finset V, 2 * ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} ≤ #s * #sᶜ := by
  have key (s : Finset V) [DecidablePred (· ∈ (s : Set V))] :
      2 * #(G.edgeFinset ∩ ((⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset) ≤
          #((⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset ↔
        2 * ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} ≤ #s * #sᶜ := by
    have hfin : (G.between ↑s (↑s)ᶜ).edgeFinset =
        (G ⊓ (⊤ : SimpleGraph V).between ↑s (↑s)ᶜ).edgeFinset :=
      edgeFinset_inj.mpr (between_eq_inf_top_between G _ _)
    have htop : ∑ v ∈ s, #{w ∈ sᶜ | (⊤ : SimpleGraph V).Adj v w} = #s * #sᶜ := by
      rw [Finset.sum_congr rfl fun v hv ↦ congrArg Finset.card <| Finset.filter_true_of_mem
        fun w hw ↦ (top_adj _ _).mpr (ne_of_mem_of_not_mem hv (Finset.mem_compl.mp hw))]
      simp
    rw [← edgeFinset_inf, ← hfin, card_edgeFinset_between_compl,
      card_edgeFinset_between_compl, htop]
  rw [isCutMinimal_iff_two_mul_card_inter_le]
  constructor
  · intro h s
    exact (key s).mp (h s)
  · intro h S _
    obtain ⟨s, rfl⟩ : ∃ s : Finset V, (s : Set V) = S := ⟨S.toFinset, by simp⟩
    exact (key s).mpr (h s)

end Finite

/-- The empty graph is cut-minimal. -/
@[simp] theorem isCutMinimal_bot : (⊥ : SimpleGraph V).IsCutMinimal := by
  intro S
  have h : (⊥ : SimpleGraph V).between S Sᶜ = ⊥ := by
    ext u v
    simp [between_adj]
  simp [h]

/-- A cut-minimal graph contains no nonempty complete-graph cut. -/
theorem IsCutMinimal.top_between_eq_bot_of_le {G : SimpleGraph V} (hG : G.IsCutMinimal)
    {S : Set V} (hS : (⊤ : SimpleGraph V).between S Sᶜ ≤ G) :
    (⊤ : SimpleGraph V).between S Sᶜ = ⊥ := by
  have hle := hG S
  rw [between_eq_inf_top_between, inf_of_le_right hS, sdiff_eq_bot_iff.mpr hS, edgeSet_bot,
    Set.encard_empty, nonpos_iff_eq_zero, Set.encard_eq_zero] at hle
  exact edgeSet_eq_empty.mp hle

/-- A complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` is cut-minimal if and only if it is
edgeless. -/
@[simp]
theorem isCutMinimal_top_between_iff (S : Set V) :
    ((⊤ : SimpleGraph V).between S Sᶜ).IsCutMinimal ↔ (⊤ : SimpleGraph V).between S Sᶜ = ⊥ :=
  ⟨fun h ↦ h.top_between_eq_bot_of_le le_rfl, fun h ↦ h ▸ isCutMinimal_bot⟩

/-- A single-edge graph `SimpleGraph.edge u v` is cut-minimal if and only if `u = v` (so the graph
is `⊥`) or there exists a third vertex distinct from `u` and `v`. -/
theorem isCutMinimal_edge_iff (u v : V) :
    (edge u v).IsCutMinimal ↔ u = v ∨ ∃ w : V, w ≠ u ∧ w ≠ v := by
  rcases eq_or_ne u v with rfl | huv
  · simp
  refine ⟨fun h ↦ Or.inr ?_, fun h S ↦ ?_⟩
  · by_contra! hno
    have hle : (⊤ : SimpleGraph V).between {u} ({u} : Set V)ᶜ ≤ edge u v := fun x y hxy ↦ by
      rw [top_between_compl_adj, Set.mem_singleton_iff, Set.mem_singleton_iff] at hxy
      rcases hxy with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
      · exact (edge_adj ..).mpr ⟨Or.inl ⟨rfl, hno y hy⟩, Ne.symm hy⟩
      · exact (edge_adj ..).mpr ⟨Or.inr ⟨hno x hx, rfl⟩, hx⟩
    have hadj : ((⊤ : SimpleGraph V).between {u} ({u} : Set V)ᶜ).Adj u v :=
      (top_between_compl_adj ..).mpr (Or.inl ⟨rfl, huv.symm⟩)
    simp [h.top_between_eq_bot_of_le hle] at hadj
  · obtain ⟨w, hwu, hwv⟩ := h.resolve_left huv
    classical
    by_cases hxor : Xor (u ∈ S) (v ∈ S)
    · have hle1 : ((edge u v).between S Sᶜ).edgeSet.encard ≤ 1 :=
        (Set.encard_le_encard
          (edgeSet_mono (G₂ := edge u v) fun _ _ h' ↦ ((between_adj ..).mp h').1)).trans_eq
          (by rw [edgeSet_edge_of_ne huv, Set.encard_singleton])
      refine hle1.trans (Set.one_le_encard_iff_nonempty.mpr ?_)
      by_cases hxu : Xor (u ∈ S) (w ∈ S)
      · exact ⟨s(u, w), (mem_edgeSet _).mpr <| (sdiff_adj ..).mpr
          ⟨(top_between_compl_adj ..).mpr hxu, by simp [edge_adj, huv, hwv]⟩⟩
      · exact ⟨s(v, w), (mem_edgeSet _).mpr <| (sdiff_adj ..).mpr
          ⟨(top_between_compl_adj ..).mpr (by grind), by simp [edge_adj, huv.symm, hwu]⟩⟩
    · have hempty : ((edge u v).between S Sᶜ).edgeSet = ∅ := by
        ext e
        induction e using Sym2.ind with
        | _ x y =>
          simp only [mem_edgeSet, between_compl_adj, edge_adj, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩, h'⟩
          · exact hxor h'
          · exact hxor h'.symm
      simp [hempty]

/-- At every vertex of a cut-minimal graph, at most as many incident pairs are edges as non-edges,
without finiteness assumptions. -/
theorem IsCutMinimal.encard_incidenceSet_le {G : SimpleGraph V} (hG : G.IsCutMinimal) (v : V) :
    (G.incidenceSet v).encard ≤ (Gᶜ.incidenceSet v).encard := by
  simpa [top_between_sdiff_eq_compl_between] using hG {v}

/-- Switching a cut-minimal graph by any complete-graph cut cannot reduce the extended cardinality
of its edge set. -/
theorem IsCutMinimal.encard_edgeSet_le_symmDiff_top_between {G : SimpleGraph V}
    (hG : G.IsCutMinimal) (S : Set V) :
    G.edgeSet.encard ≤ (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeSet.encard := by
  let H := (⊤ : SimpleGraph V).between S Sᶜ
  have h1 : G.edgeSet = (G.between S Sᶜ).edgeSet ∪ (G.edgeSet \ H.edgeSet) := by
    rw [between_eq_inf_top_between, edgeSet_inf, Set.inter_union_sdiff]
  have h2 : (G ∆ H).edgeSet = (H \ G).edgeSet ∪ (G.edgeSet \ H.edgeSet) := by
    rw [edgeSet_symmDiff, symmDiff_def, Set.union_comm, edgeSet_sdiff]
  have hd1 : Disjoint (G.between S Sᶜ).edgeSet (G.edgeSet \ H.edgeSet) := by
    rw [between_eq_inf_top_between, edgeSet_inf]
    exact disjoint_inf_sdiff
  have hd2 : Disjoint (H \ G).edgeSet (G.edgeSet \ H.edgeSet) := by
    rw [edgeSet_sdiff]
    exact disjoint_sdiff_sdiff
  rw [h1, h2, Set.encard_union_eq hd1, Set.encard_union_eq hd2]
  exact add_le_add_left (hG S) _

section Switching

/-- Switching a cut-minimal graph by any complete-graph cut cannot reduce its finite edge count. -/
theorem IsCutMinimal.card_edgeFinset_le_symmDiff_top_between {G : SimpleGraph V}
    (hG : G.IsCutMinimal) (S : Set V) [Fintype G.edgeSet]
    [Fintype (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeSet] :
    #G.edgeFinset ≤ #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  have h := hG.encard_edgeSet_le_symmDiff_top_between S
  rwa [← coe_edgeFinset, ← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard,
    Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at h

/-- On a finite vertex type, cut-minimality is equivalent to non-decreasing edge count across all
finset cuts. -/
theorem isCutMinimal_iff_forall_finset_card_edgeFinset_le_symmDiff_top_between
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      ∀ s : Finset V,
        #G.edgeFinset ≤ #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
  rw [isCutMinimal_iff_card_le_card_symmDiff]
  refine ⟨fun h s ↦ by rw [edgeFinset_symmDiff]; exact h s, fun h S _ ↦ ?_⟩
  have heq : (G ∆ (⊤ : SimpleGraph V).between (S.toFinset : Set V)
      (S.toFinset : Set V)ᶜ).edgeFinset =
      G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
    rw [edgeFinset_symmDiff]
    congr 1
    exact edgeFinset_inj.mpr (by simp)
  exact heq ▸ h S.toFinset

/-- Every graph on a finite vertex type can be switched by a finset cut to a cut-minimal graph. -/
theorem exists_finset_isCutMinimal_symmDiff_top_between [Finite V] (G : SimpleGraph V) :
    ∃ s : Finset V, (G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).IsCutMinimal := by
  classical
  cases nonempty_fintype V
  obtain ⟨s, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun s : Finset V ↦ #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset)
    Finset.univ_nonempty
  refine ⟨s, (isCutMinimal_iff_forall_finset_card_edgeFinset_le_symmDiff_top_between _).mpr
    fun t ↦ ?_⟩
  have heq : G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ ∆
      (⊤ : SimpleGraph V).between (t : Set V) (t : Set V)ᶜ =
      G ∆ (⊤ : SimpleGraph V).between ((s ∆ t : Finset V) : Set V)
        ((s ∆ t : Finset V) : Set V)ᶜ := by
    rw [Finset.coe_symmDiff, symmDiff_top_between_symmDiff]
  have hcard : ∀ {H₁ H₂ : SimpleGraph V} {inst₁ : Fintype H₁.edgeSet} {inst₂ : Fintype H₂.edgeSet}
      (_ : H₁ = H₂), @Finset.card (Sym2 V) (@edgeFinset V H₁ inst₁) =
        @Finset.card (Sym2 V) (@edgeFinset V H₂ inst₂) := by
    rintro H₁ H₂ inst₁ inst₂ rfl
    exact card_edgeFinset_congr _ _ _
  exact (card_edgeFinset_congr _ _ _).trans_le
    ((hmin (s ∆ t) (Finset.mem_univ _)).trans_eq (hcard heq.symm))

/-- On at least three vertices, every single-edge graph `SimpleGraph.edge u v` is cut-minimal. -/
theorem isCutMinimal_edge_of_three_le_card [Fintype V] (hV : 3 ≤ Fintype.card V) (u v : V) :
    (edge u v).IsCutMinimal := by
  rcases eq_or_ne u v with rfl | huv
  · simp
  classical
  have hpos : 0 < #((Finset.univ.erase u).erase v) := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, Finset.mem_erase] at hw
  exact (isCutMinimal_edge_iff u v).mpr (Or.inr ⟨w, hw.2.1, hw.1⟩)

/-- On at least three vertices, every graph with at most one edge is cut-minimal. -/
theorem isCutMinimal_of_card_edgeFinset_le_one [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hV : 3 ≤ Fintype.card V) (hG : #G.edgeFinset ≤ 1) :
    G.IsCutMinimal := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hG with h0 | h1
  · rw [Finset.card_eq_zero, edgeFinset_eq_empty] at h0
    exact h0 ▸ isCutMinimal_bot
  · obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v :=
        G.mem_edgeSet.mp (mem_edgeFinset.mp (he ▸ Finset.mem_singleton_self _))
      have hG_eq : G = edge u v := by
        rw [← edgeSet_inj, ← coe_edgeFinset, he, Finset.coe_singleton, edgeSet_edge_of_ne huv.ne]
      exact hG_eq ▸ isCutMinimal_edge_of_three_le_card hV u v

/-- In a cut-minimal graph on a finite vertex type, twice the degree of any vertex is at most
`Fintype.card V - 1`. -/
theorem IsCutMinimal.two_mul_degree_le [Fintype V] {G : SimpleGraph V} (hG : G.IsCutMinimal)
    (v : V) [Fintype (G.neighborSet v)] :
    2 * G.degree v ≤ Fintype.card V - 1 := by
  classical
  have h := hG.encard_incidenceSet_le v
  rw [G.encard_incidenceSet, Gᶜ.encard_incidenceSet, G.degree_compl, Nat.cast_le] at h
  omega

/-- On at most four vertices, every vertex of a cut-minimal graph has degree at most `1`. -/
theorem IsCutMinimal.degree_le_one_of_card_le_four [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCutMinimal) (hV : Fintype.card V ≤ 4) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v ≤ 1 := by
  have := hG.two_mul_degree_le v
  omega

/-- In a cut-minimal graph on a finite vertex type, twice the number of edges is at most
`Fintype.card V * ((Fintype.card V - 1) / 2)`. -/
theorem IsCutMinimal.two_mul_card_edgeFinset_le [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsCutMinimal) :
    2 * #G.edgeFinset ≤ Fintype.card V * ((Fintype.card V - 1) / 2) := by
  classical
  rw [G.card_edgeFinset_congr _ G.fintypeEdgeSet, ← G.sum_degrees_eq_twice_card_edges]
  calc ∑ v : V, G.degree v ≤ ∑ _v : V, (Fintype.card V - 1) / 2 :=
        Finset.sum_le_sum fun v _ ↦ by
          have := hG.two_mul_degree_le v
          omega
    _ = Fintype.card V * ((Fintype.card V - 1) / 2) := by simp

/-- On at most two vertices, every cut-minimal graph is edgeless. -/
theorem IsCutMinimal.edgeFinset_eq_empty_of_card_le_two [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsCutMinimal) (hV : Fintype.card V ≤ 2) :
    G.edgeFinset = ∅ := by
  have h := hG.two_mul_card_edgeFinset_le
  have hdiv : (Fintype.card V - 1) / 2 = 0 := by omega
  rw [hdiv, mul_zero] at h
  exact Finset.card_eq_zero.mp (by omega)

/-- On at most four vertices, a cut-minimal graph has at most two edges. -/
theorem IsCutMinimal.card_edgeFinset_le_two_of_card_le_four [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsCutMinimal) (hV : Fintype.card V ≤ 4) :
    #G.edgeFinset ≤ 2 := by
  have h := hG.two_mul_card_edgeFinset_le
  have hle : Fintype.card V * ((Fintype.card V - 1) / 2) ≤ 4 :=
    (Nat.mul_le_mul hV (by omega : (Fintype.card V - 1) / 2 ≤ 1)).trans_eq (mul_one 4)
  omega

/-- On at most four vertices, every cut-minimal graph is `3`-clique-free. -/
theorem IsCutMinimal.cliqueFree_three_of_card_le_four [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCutMinimal) (hV : Fintype.card V ≤ 4) :
    G.CliqueFree 3 := by
  classical
  exact G.cliqueFree_add_two_of_degree_le fun v ↦ hG.degree_le_one_of_card_le_four hV v

end Switching

end SimpleGraph
