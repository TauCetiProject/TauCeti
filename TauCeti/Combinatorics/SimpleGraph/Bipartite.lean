/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Logic.Equiv.Bool

/-!
# Bipartite restrictions and two-colourings

Restricting a graph to pairs between two sets is intersection with the corresponding
restriction of the complete graph (`SimpleGraph.between_eq_inf_top_between`), and on a finite
vertex type the same decomposition holds for `edgeFinset` (`SimpleGraph.edgeFinset_between`),
with `(⊤ : SimpleGraph V).between S T` having `S.toFinset.card * T.toFinset.card` edges when `S`
and `T` are disjoint (`SimpleGraph.card_edgeFinset_top_between`). Complete-graph cuts respect
symmetric difference (`SimpleGraph.top_between_symmDiff`). A bipartition `G.IsBipartiteWith s t`
extends to a covering bipartition on the whole vertex type by adjoining the remaining isolated
vertices to either side (`SimpleGraph.IsBipartiteWith.compl_right` and
`SimpleGraph.IsBipartiteWith.compl_left`), and yields vertex covers given by either side or by
replacing any subset `S` of the left side with its neighbours
(`SimpleGraph.IsBipartiteWith.isVertexCover_left`,
`SimpleGraph.IsBipartiteWith.isVertexCover_right`, and
`SimpleGraph.IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet`).

A walk in a graph coloured by `Bool` has even length exactly when its endpoints have the same
colour (`SimpleGraph.Coloring.even_length_iff_congr`). On a preconnected graph every two vertices
are joined by a walk, so whether two vertices share a colour does not depend on the colouring.
Hence a preconnected graph carries at most two colourings by `Bool`, and any two of them either
agree or are exchanged by `not`. In particular the two colour classes of a connected bipartite
graph are determined up to their order, which is what makes constructions from a bipartition of a
tree, such as the bipartite Coxeter element of a Coxeter system with a tree as Coxeter graph,
independent of the colouring up to exchanging the two classes.

Likewise an endomorphism of a preconnected graph either keeps the colour of every vertex or changes
the colour of every vertex; a permutation doing the latter matches the two colour classes, so the
graph has an even number of vertices (`TauCeti.two_mul_card_filter_eq_true`). A cycle graph has a
two-colouring exactly when it has an even number of vertices or a single vertex; on a cycle, which
of the two happens is read off the parity of the number of steps the endomorphism moves a single
vertex.

## Main results

* `SimpleGraph.edgeFinset_between`, `SimpleGraph.card_edgeFinset_top_between`: edge finset of
  `G.between S T` and edge count of `(⊤ : SimpleGraph V).between S T` for disjoint `S` and `T`.
* `SimpleGraph.card_edgeFinset_between`: the edges between disjoint finite sets `s` and `t` are
  counted by the degrees from `s` into `t`; `SimpleGraph.card_edgeFinset_between_compl` is the
  case of the cut of `s`.
* `SimpleGraph.IsBipartiteWith.compl_right`, `SimpleGraph.IsBipartiteWith.compl_left`: extending a
  bipartition to cover the whole vertex type.
* `SimpleGraph.IsBipartiteWith.isVertexCover_left`,
  `SimpleGraph.IsBipartiteWith.isVertexCover_right`,
  `SimpleGraph.IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet`: vertex covers
  associated with a bipartition.
* `SimpleGraph.IsBipartite.exists_sign`: a bipartite graph carries a sign `±1` changing along
  every edge.
* `SimpleGraph.Coloring.eq_or_eq_recolorOfEquiv_boolNot`: on a preconnected graph, two
  `Bool`-colourings agree or differ by exchanging the colours.
* `SimpleGraph.Coloring.forall_apply_eq_or_forall_apply_eq_not`: on a preconnected graph, an
  endomorphism either keeps the colour of every vertex or changes the colour of every vertex.
* `SimpleGraph.isBipartite_cycleGraph_iff`: a cycle graph is bipartite exactly when it has an even
  number of vertices or a single vertex.
* `SimpleGraph.Coloring.cycleGraph_apply_add_eq_iff_even_val`,
  `SimpleGraph.Coloring.cycleGraph_forall_apply_eq_iff_even_val_apply_zero` and
  `SimpleGraph.Coloring.cycleGraph_forall_apply_eq_not_iff_odd_val_apply_zero`: colours alternate
  around a cycle, so an endomorphism of a cycle preserves the colours exactly when it moves `0` an
  even number of steps, and exchanges them exactly when it moves `0` an odd number of steps.
-/

public section

open scoped symmDiff Finset

namespace SimpleGraph

variable {V : Type*}

/-- Restricting a graph to pairs between two sets is intersection with the corresponding
restriction of the complete graph. -/
theorem between_eq_inf_top_between (G : SimpleGraph V) (s t : Set V) :
    G.between s t = G ⊓ (⊤ : SimpleGraph V).between s t := by
  ext u v
  simp only [between_adj, inf_adj, top_adj]
  exact and_congr_right fun h ↦ (and_iff_right h.ne).symm

/-- The complete-graph cut of `S ∆ T` is the symmetric difference of the cuts of `S` and `T`. -/
theorem top_between_symmDiff (S T : Set V) :
    (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ =
      (⊤ : SimpleGraph V).between S Sᶜ ∆ (⊤ : SimpleGraph V).between T Tᶜ := by
  ext u v
  simp only [between_adj, top_adj, Set.mem_compl_iff, symmDiff_def, Set.mem_union,
    Set.mem_sdiff, sup_adj, sdiff_adj]
  tauto

section Finite

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

end Finite

/-- The edges of `G` between disjoint finite sets `s` and `t` are counted by the degrees from `s`
into `t`. -/
theorem card_edgeFinset_between (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V}
    [Fintype (G.between ↑s ↑t).edgeSet] (h : Disjoint s t) :
    #(G.between ↑s ↑t).edgeFinset = ∑ v ∈ s, #{w ∈ t | G.Adj v w} := by
  have hpairs : ∑ v ∈ s, #{w ∈ t | G.Adj v w} = #{p ∈ s ×ˢ t | G.Adj p.1 p.2} := by
    simp only [Finset.card_filter, Finset.sum_product]
  rw [hpairs]
  symm
  refine Finset.card_bij (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rw [mem_edgeFinset, mem_edgeSet, between_adj]
    exact ⟨hp.2, Or.inl hp.1⟩
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' he
    simp only [Finset.mem_filter, Finset.mem_product] at hp hp'
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hp'.1.2 (Finset.disjoint_left.mp h hp.1.1)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, between_adj, Finset.mem_coe] at he
      obtain ⟨hab, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := he
      · exact ⟨(a, b), by simp [ha, hb, hab], rfl⟩
      · exact ⟨(b, a), by simp [ha, hb, hab.symm], Sym2.eq_swap⟩

/-- The edges of `G` across the cut of a finite set `s` are counted by the degrees from `s` into
its complement. -/
theorem card_edgeFinset_between_compl [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) [Fintype (G.between ↑s (↑s)ᶜ).edgeSet] :
    #(G.between ↑s (↑s)ᶜ).edgeFinset = ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} := by
  classical
  rw [← card_edgeFinset_between G disjoint_compl_right]
  congr! 2
  rw [Finset.coe_compl]

/-- Adjoining all vertices outside `s ∪ t` to the right side yields a bipartition with sides `s`
and `sᶜ` covering the whole vertex type. -/
theorem IsBipartiteWith.compl_right {G : SimpleGraph V} {s t : Set V}
    (h : G.IsBipartiteWith s t) : G.IsBipartiteWith s sᶜ where
  disjoint := disjoint_compl_right
  mem_of_adj _ _ hadj := (h.mem_of_adj hadj).imp
    (And.imp_right fun hx ↦ h.disjoint.subset_compl_left hx)
    (And.imp_left fun hx ↦ h.disjoint.subset_compl_left hx)

/-- Adjoining all vertices outside `s ∪ t` to the left side yields a bipartition with sides `tᶜ`
and `t` covering the whole vertex type. -/
theorem IsBipartiteWith.compl_left {G : SimpleGraph V} {s t : Set V}
    (h : G.IsBipartiteWith s t) : G.IsBipartiteWith tᶜ t :=
  h.symm.compl_right.symm

/-- The left side of a bipartition is a vertex cover. -/
theorem IsBipartiteWith.isVertexCover_left {G : SimpleGraph V} {L R : Set V}
    (h : G.IsBipartiteWith L R) : G.IsVertexCover L :=
  fun _ _ hadj ↦ (h.mem_of_adj hadj).imp And.left And.right

/-- The right side of a bipartition is a vertex cover. -/
theorem IsBipartiteWith.isVertexCover_right {G : SimpleGraph V} {L R : Set V}
    (h : G.IsBipartiteWith L R) : G.IsVertexCover R :=
  h.symm.isVertexCover_left

/-- Removing any set `S` from the left side `L` of a bipartition and adjoining the neighbours of
`S` yields a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet {G : SimpleGraph V}
    {L R : Set V} (h : G.IsBipartiteWith L R) (S : Set V) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u v huv
  rcases h.mem_of_adj huv with ⟨huL, -⟩ | ⟨-, hvL⟩
  · by_cases huS : u ∈ S
    · exact Or.inr (Set.subset_union_right <| Set.mem_biUnion huS huv)
    · exact Or.inl (Set.subset_union_left ⟨huL, huS⟩)
  · by_cases hvS : v ∈ S
    · exact Or.inl (Set.subset_union_right <| Set.mem_biUnion hvS huv.symm)
    · exact Or.inr (Set.subset_union_left ⟨hvL, hvS⟩)

/-- **A cycle graph is bipartite exactly when it has an even number of vertices**, or a single
vertex, in which case it has no edges. -/
@[simp]
theorem isBipartite_cycleGraph_iff {n : ℕ} : (cycleGraph n).IsBipartite ↔ Even n ∨ n = 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have h3 := chromaticNumber_cycleGraph_of_odd n (by have := hn.1.pos; omega) hn.1
    exact absurd (h3.symm.trans_le h.chromaticNumber_le) (by decide)
  · rintro (h | rfl)
    · exact IsBipartite.cycleGraph_of_even h
    · exact (colorable_of_fintype _).mono (by simp)

/-- **The sign of a two-colouring.** A bipartite graph carries a sign `ε v = ±1`, with values in
any type with one and an involutive negation, which changes along every edge. -/
theorem IsBipartite.exists_sign {R : Type*} [One R] [InvolutiveNeg R] {G : SimpleGraph V}
    (hG : G.IsBipartite) :
    ∃ ε : V → R, (∀ ⦃v w⦄, G.Adj v w → ε v = -ε w) ∧ ∀ v, ε v = 1 ∨ ε v = -1 := by
  obtain ⟨c⟩ := hG
  refine ⟨fun v ↦ if c v = 0 then 1 else -1, fun v w h ↦ ?_, fun v ↦ ?_⟩
  · have hc := c.valid h
    beta_reduce
    revert hc
    generalize c v = x, c w = y
    fin_cases x <;> fin_cases y <;> simp
  · beta_reduce
    split_ifs <;> simp

end SimpleGraph

namespace SimpleGraph.Coloring

variable {V : Type*} {G : SimpleGraph V}

/-- **A preconnected graph has at most two colourings by `Bool`**: any two of them agree, or are
exchanged by `not`. -/
theorem eq_or_eq_recolorOfEquiv_boolNot (hG : G.Preconnected) (c c' : G.Coloring Bool) :
    c' = c ∨ c' = G.recolorOfEquiv Equiv.boolNot c := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
  · exact Or.inl (DFunLike.ext _ _ isEmptyElim)
  -- Whether a vertex has the colour of `u` is read off the parity of a walk from `u`, so it is the
  -- same for both colourings.
  have key (v : V) : (c u = c v ↔ c' u = c' v) := by
    obtain ⟨p⟩ := hG u v
    have h := (c.even_length_iff_congr p).symm.trans (c'.even_length_iff_congr p)
    simpa only [Bool.coe_iff_coe] using h
  by_cases hu : c' u = c u
  · refine Or.inl (DFunLike.ext _ _ fun v ↦ ?_)
    have hv := key v
    clear key
    revert hu hv
    generalize c u = a, c v = b, c' u = a', c' v = b'
    decide +revert
  · refine Or.inr (DFunLike.ext _ _ fun v ↦ ?_)
    have hv := key v
    clear key
    suffices c' v = !c v by simpa using this
    revert hu hv
    generalize c u = a, c v = b, c' u = a', c' v = b'
    decide +revert

/-- **An endomorphism of a preconnected graph preserves or exchanges a two-colouring**: either every
vertex keeps its colour, or every vertex changes colour. -/
theorem forall_apply_eq_or_forall_apply_eq_not (hG : G.Preconnected) (c : G.Coloring Bool)
    (f : G →g G) : (∀ v, c (f v) = c v) ∨ ∀ v, c (f v) = !c v := by
  rcases c.eq_or_eq_recolorOfEquiv_boolNot hG (c.comp f) with h | h
  · exact Or.inl fun v ↦ DFunLike.congr_fun h v
  · exact Or.inr fun v ↦ by simpa using DFunLike.congr_fun h v

/-- On a preconnected graph, an endomorphism keeping the colour of one vertex keeps the colour of
every vertex. -/
theorem forall_apply_eq_of_apply_eq (hG : G.Preconnected) (c : G.Coloring Bool) (f : G →g G)
    {v : V} (hv : c (f v) = c v) (w : V) : c (f w) = c w :=
  (c.forall_apply_eq_or_forall_apply_eq_not hG f).resolve_right (fun h ↦ by simp [h] at hv) w

/-- On a preconnected graph, an endomorphism changing the colour of one vertex changes the colour of
every vertex. -/
theorem forall_apply_eq_not_of_apply_ne (hG : G.Preconnected) (c : G.Coloring Bool) (f : G →g G)
    {v : V} (hv : c (f v) ≠ c v) (w : V) : c (f w) = !c w :=
  (c.forall_apply_eq_or_forall_apply_eq_not hG f).resolve_left (fun h ↦ hv (h v)) w

variable {n : ℕ}

open Fin.NatCast in
/-- Moving `m` steps around a two-coloured cycle keeps the colour exactly when `m` is even; this
is `SimpleGraph.Coloring.cycleGraph_apply_add_eq_iff_even_val` before reducing `m` modulo the
length. -/
private theorem apply_add_natCast_eq_iff_even (c : (cycleGraph (n + 2)).Coloring Bool)
    (v : Fin (n + 2)) (m : ℕ) : c (v + (m : Fin (n + 2))) = c v ↔ Even m := by
  induction m with
  | zero => simp
  | succ m ih =>
    set w : Fin (n + 2) := v + (m : Fin (n + 2))
    have hne := c.valid (show (cycleGraph (n + 2)).Adj w (w + 1) by simp [cycleGraph_adj])
    rw [Nat.cast_succ, ← add_assoc, Nat.even_add_one, ← ih]
    revert hne
    generalize c w = a, c (w + 1) = b, c v = d
    decide +revert

/-- **Colours along a cycle alternate**: in a two-colouring of a cycle graph, moving `k` steps
around the cycle keeps the colour exactly when `k` is even. -/
theorem cycleGraph_apply_add_eq_iff_even_val {n : ℕ} (c : (cycleGraph n).Coloring Bool)
    (v k : Fin n) : c (v + k) = c v ↔ Even k.val := by
  match n, c, v, k with
  | 0, _, v, _ => exact v.elim0
  | 1, _, _, k => simp [Subsingleton.elim k 0]
  | n + 2, c, v, k =>
    have h := c.apply_add_natCast_eq_iff_even v k.val
    rwa [Fin.cast_val_eq_self] at h

/-- In a two-colouring of a cycle graph, moving `k` steps around the cycle changes the colour
exactly when `k` is odd. -/
theorem cycleGraph_apply_add_eq_not_iff_odd_val {n : ℕ} (c : (cycleGraph n).Coloring Bool)
    (v k : Fin n) : c (v + k) = !c v ↔ Odd k.val := by
  rw [Bool.eq_not_iff, ← Nat.not_even_iff_odd, ← c.cycleGraph_apply_add_eq_iff_even_val v k]

/-- In a two-colouring of a cycle graph, two vertices have the same colour exactly when the number
of steps from the second to the first is even. -/
theorem cycleGraph_apply_eq_apply_iff_even_val_sub {n : ℕ} (c : (cycleGraph n).Coloring Bool)
    (u v : Fin n) : c u = c v ↔ Even (u - v).val := by
  obtain _ | n := n
  · exact u.elim0
  · rw [← c.cycleGraph_apply_add_eq_iff_even_val v (u - v), add_sub_cancel]

/-- **Which endomorphisms of a cycle graph preserve a two-colouring**: an endomorphism preserves the
colours exactly when it moves the vertex `0` an even number of steps. The rotation
`TauCeti.cycleGraphAddRightIso k` and the reflection `TauCeti.cycleGraphSubLeftIso k` therefore
preserve the colours exactly when `k` is even. -/
theorem cycleGraph_forall_apply_eq_iff_even_val_apply_zero {n : ℕ} [NeZero n]
    (c : (cycleGraph n).Coloring Bool) (f : cycleGraph n →g cycleGraph n) :
    (∀ v, c (f v) = c v) ↔ Even (f 0).val := by
  have h := c.cycleGraph_apply_eq_apply_iff_even_val_sub (f 0) 0
  rw [sub_zero] at h
  exact ⟨fun hf ↦ h.mp (hf 0), fun h0 ↦ c.forall_apply_eq_of_apply_eq preconnected_cycleGraph f
    (h.mpr h0)⟩

/-- **Which endomorphisms of a cycle graph exchange the colours of a two-colouring**: an
endomorphism exchanges the colours exactly when it moves the vertex `0` an odd number of steps. -/
theorem cycleGraph_forall_apply_eq_not_iff_odd_val_apply_zero {n : ℕ} [NeZero n]
    (c : (cycleGraph n).Coloring Bool) (f : cycleGraph n →g cycleGraph n) :
    (∀ v, c (f v) = !c v) ↔ Odd (f 0).val := by
  have h := c.cycleGraph_apply_add_eq_not_iff_odd_val 0 (f 0)
  rw [zero_add] at h
  exact ⟨fun hf ↦ h.mp (hf 0), fun h0 ↦ c.forall_apply_eq_not_of_apply_ne preconnected_cycleGraph f
    (Bool.eq_not_iff.mp (h.mpr h0))⟩

end SimpleGraph.Coloring
