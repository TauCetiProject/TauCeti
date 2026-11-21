/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import TauCeti.Combinatorics.SimpleGraph.OddTriple
public import TauCeti.Combinatorics.SimpleGraph.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import TauCeti.Order.Hom.PowersetCard

/-!
# Three-vertex subsets spanning an odd number of edges

For a finite simple graph `G` on `V`, `G.oddTriangleFinset` is the finset of `3`-element subsets
of `V` that span an odd number of edges of `G` (one or three edges), coinciding with
`G.oddTripleFinset` (`SimpleGraph.oddTriangleFinset_eq_oddTripleFinset`). When `G` is viewed as the
support of a binary `1`-cochain on the complete `2`-complex on `V`, `G.oddTriangleFinset` is the
set of triangles with non-trivial coboundary, and switching `G` by any complete-graph cut leaves it
unchanged (`SimpleGraph.oddTriangleFinset_symmDiff_top_between`).

In a triangle-free graph (`G.CliqueFree 3`), no `3`-element vertex subset spans three edges, so
`G.oddTriangleFinset` consists of the `3`-element subsets spanning a single edge, and its
cardinality satisfies the degree-square identity
`#G.oddTriangleFinset + ∑ v, G.degree v ^ 2 = Fintype.card V * #G.edgeFinset`
(D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, equation (2.5), p. 5).
In particular, when every vertex has degree at most `1`,
`#G.oddTriangleFinset = (Fintype.card V - 2) * #G.edgeFinset`
(`SimpleGraph.card_oddTriangleFinset_of_degree_le_one`).

## Main definitions and results

* `SimpleGraph.oddTriangleFinset`: the finset of `3`-element subsets of `V` spanning an odd number
  of edges of `G`.
* `SimpleGraph.triple_mem_oddTriangleFinset_iff` and
  `SimpleGraph.oddTriangleFinset_symmDiff_top_between`: `Xor` membership criterion on `{a, b, c}`
  and invariance of `oddTriangleFinset` under complete-graph cut switching.
* `SimpleGraph.Iso.map_oddTriangleFinset`, `SimpleGraph.Iso.card_oddTriangleFinset_eq`:
  invariance of `oddTriangleFinset` under graph isomorphism.
* `SimpleGraph.card_oddTriangleFinset_eq_sum`,
  `SimpleGraph.card_oddTriangleFinset_eq_card_filter_lt`: over a linear order, the odd triangles
  are counted by their increasing triples `u < v < w`.
* `SimpleGraph.mem_oddTriangleFinset_iff_of_cliqueFree`: in a `3`-clique-free graph, an odd
  triangle is a `3`-element vertex set spanning a single edge.
* `SimpleGraph.card_oddTriangleFinset_add_sum_degree_sq`,
  `SimpleGraph.card_oddTriangleFinset_eq_of_cliqueFree`, and
  `SimpleGraph.card_oddTriangleFinset_of_degree_le_one`: odd-triangle count in `3`-clique-free
  graphs and graphs of maximum degree at most `1`.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V W : Type*}

section Basic

variable [Fintype V] [DecidableEq V]

/-- The finset of `3`-element subsets of `V` spanning an odd number of edges of `G`. -/
def oddTriangleFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  {s ∈ (univ : Finset V).powersetCard 3 | Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}}

/-- Unfolding characterization of `SimpleGraph.oddTriangleFinset`. -/
theorem oddTriangleFinset_def (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.oddTriangleFinset =
      {s ∈ (univ : Finset V).powersetCard 3 | Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} := by
  rfl

/-- `G.oddTriangleFinset` coincides with `G.oddTripleFinset`. -/
theorem oddTriangleFinset_eq_oddTripleFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.oddTriangleFinset = G.oddTripleFinset := by
  ext s
  simp [oddTriangleFinset, mem_powersetCard, filter_edgeFinset_toFinset_subset]

/-- A vertex finset belongs to `G.oddTriangleFinset` iff it has cardinality `3` and contains an odd
number of edges of `G`. -/
@[simp]
theorem mem_oddTriangleFinset {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} :
    s ∈ G.oddTriangleFinset ↔ #s = 3 ∧ Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s} := by
  simp [oddTriangleFinset, mem_powersetCard]

/-- Membership in `G.oddTriangleFinset` in terms of the induced subgraph on `s`. -/
theorem mem_oddTriangleFinset_iff_induce {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} :
    s ∈ G.oddTriangleFinset ↔ #s = 3 ∧ Odd #(G.induce (s : Set V)).edgeFinset := by
  rw [mem_oddTriangleFinset, card_filter_edgeFinset_toFinset_subset]

/-- The empty graph has no odd triangles. -/
@[simp]
theorem oddTriangleFinset_bot : (⊥ : SimpleGraph V).oddTriangleFinset = ∅ := by
  ext s
  simp only [mem_oddTriangleFinset, notMem_empty, iff_false, not_and, Nat.not_odd_iff_even]
  intro _
  rw [card_eq_zero.mpr (by ext; simp)]
  simp

section Iso

variable [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Graph isomorphisms transport `oddTriangleFinset` by mapping each `3`-element vertex subset. -/
theorem Iso.map_oddTriangleFinset (f : G ≃g H) :
    G.oddTriangleFinset.map (mapEmbedding f.toEquiv.toEmbedding).toEmbedding =
      H.oddTriangleFinset := by
  have hmap : G.map f.toEquiv.toEmbedding = H := by
    ext u v
    obtain ⟨x, rfl⟩ := f.surjective u
    obtain ⟨y, rfl⟩ := f.surjective v
    rw [map_adj]
    simp [f.apply_eq_iff_eq, f.map_adj_iff]
  have hedge : H.edgeFinset = G.edgeFinset.map f.toEquiv.toEmbedding.sym2Map := by
    rw [← edgeFinset_inj.mpr hmap, edgeFinset_map]
  have hcard (s : Finset V) :
      #{e ∈ H.edgeFinset | e.toFinset ⊆ s.map f.toEquiv.toEmbedding} =
        #{e ∈ G.edgeFinset | e.toFinset ⊆ s} := by
    rw [filter_edgeFinset_toFinset_subset, hedge, sym2_map, ← map_inter, card_map,
      ← filter_edgeFinset_toFinset_subset]
  have huniv : (univ : Finset V).map f.toEquiv.toEmbedding = univ := by
    ext w
    obtain ⟨x, rfl⟩ := f.surjective w
    simp
  ext t
  simp only [oddTriangleFinset, mem_map, mem_filter, mem_powersetCard, subset_univ, true_and,
    RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · rintro ⟨s, ⟨hs3, hodd⟩, rfl⟩
    rwa [card_map, and_iff_right hs3, hcard]
  · rintro ⟨ht3, hodd⟩
    have htsub : t ∈ ((univ : Finset V).map f.toEquiv.toEmbedding).powersetCard 3 := by
      rw [huniv, mem_powersetCard]
      exact ⟨subset_univ _, ht3⟩
    rw [powersetCard_map, mem_map] at htsub
    obtain ⟨s, hs, rfl⟩ := htsub
    rw [mem_powersetCard] at hs
    rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hcard] at hodd
    exact ⟨s, ⟨hs.2, hodd⟩, by rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]⟩

/-- Isomorphic finite graphs have the same number of odd triangles. -/
theorem Iso.card_oddTriangleFinset_eq (f : G ≃g H) :
    #G.oddTriangleFinset = #H.oddTriangleFinset := by
  rw [← f.map_oddTriangleFinset, card_map]

end Iso

section CliqueFree

variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem subset_triple_pairs {a b c : V} :
    {e ∈ G.edgeFinset | e.toFinset ⊆ ({a, b, c} : Finset V)} ⊆ {s(a, b), s(a, c), s(b, c)} := by
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := (mem_edgeFinset.mp he.1).ne
    have hu : u ∈ ({a, b, c} : Finset V) := he.2 (by simp)
    have hv : v ∈ ({a, b, c} : Finset V) := he.2 (by simp)
    simp only [mem_insert, mem_singleton] at hu hv ⊢
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact False.elim (huv rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl Sym2.eq_swap
    · exact False.elim (huv rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact Or.inr (Or.inr Sym2.eq_swap)
    · exact False.elim (huv rfl)

/-- In a `3`-clique-free graph, a vertex subset belongs to `G.oddTriangleFinset` iff it has
`3` vertices and contains a single edge of `G`. -/
theorem mem_oddTriangleFinset_iff_of_cliqueFree (hG : G.CliqueFree 3) {s : Finset V} :
    s ∈ G.oddTriangleFinset ↔ #s = 3 ∧ #{e ∈ G.edgeFinset | e.toFinset ⊆ s} = 1 := by
  rw [mem_oddTriangleFinset]
  refine and_congr_right fun hs3 ↦ ⟨fun hodd ↦ ?_, fun h1 ↦ h1 ▸ odd_one⟩
  obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs3
  have hsub := subset_triple_pairs (G := G) (a := a) (b := b) (c := c)
  have hcard_pairs : #({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)) ≤ 3 :=
    (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))
  have hle3 : #{e ∈ G.edgeFinset | e.toFinset ⊆ ({a, b, c} : Finset V)} ≤ 3 :=
    (card_le_card hsub).trans hcard_pairs
  obtain ⟨k, hk⟩ := hodd
  have hk1 : k ≤ 1 := by omega
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk0
  · exfalso
    have heq := eq_of_subset_of_card_le hsub (hk ▸ hcard_pairs)
    have mem_of (e : Sym2 V) (he : e ∈ ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V))) :
        e ∈ G.edgeSet := by
      rw [← mem_edgeFinset]
      exact (mem_filter.mp (heq ▸ he)).1
    exact hG {a, b, c} (is3Clique_triple_iff.mpr
      ⟨mem_of s(a, b) (by simp), mem_of s(a, c) (by simp), mem_of s(b, c) (by simp)⟩)
  · omega

omit [DecidableEq V] in
private theorem sum_dart_nonadj_add_two_mul_sum_degree_sq (hG : G.CliqueFree 3) :
    (∑ d : G.Dart, #{w : V | ¬ G.Adj d.fst w ∧ ¬ G.Adj d.snd w}) +
      2 * ∑ v : V, G.degree v ^ 2 = 2 * (Fintype.card V * #G.edgeFinset) := by
  classical
  have hdisj (d : G.Dart) : Disjoint (G.neighborFinset d.fst) (G.neighborFinset d.snd) := by
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    rw [mem_neighborFinset] at hw₁ hw₂
    exact hG {d.fst, d.snd, w} (is3Clique_triple_iff.mpr ⟨d.adj, hw₁, hw₂⟩)
  have hfiber (d : G.Dart) :
      #{w : V | ¬ G.Adj d.fst w ∧ ¬ G.Adj d.snd w} + (G.degree d.fst + G.degree d.snd) =
        Fintype.card V := by
    have hcompl : ({w : V | ¬ G.Adj d.fst w ∧ ¬ G.Adj d.snd w} : Finset V) =
        (G.neighborFinset d.fst ∪ G.neighborFinset d.snd)ᶜ := by
      ext w
      simp
    rw [hcompl, ← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← card_union_of_disjoint (hdisj d), card_compl_add_card]
  have hsum_fst : ∑ d : G.Dart, G.degree d.fst = ∑ v : V, G.degree v ^ 2 := by
    rw [← sum_fiberwise_of_maps_to (g := fun d : G.Dart ↦ d.fst) (t := univ)
      (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun v _ ↦ ?_
    have hconst : ∑ x ∈ {d : G.Dart | d.fst = v}, G.degree x.fst =
        ∑ _x ∈ {d : G.Dart | d.fst = v}, G.degree v :=
      sum_congr rfl fun d hd ↦ by rw [(mem_filter.mp hd).2]
    rw [hconst, sum_const, smul_eq_mul, G.dart_fst_fiber_card_eq_degree, sq]
  have hsum_snd : ∑ d : G.Dart, G.degree d.snd = ∑ v : V, G.degree v ^ 2 := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm Dart.symm (Dart.symm_involutive (G := G)))]
    exact hsum_fst
  have htot := sum_congr (s₁ := (univ : Finset G.Dart)) rfl fun d _ ↦ hfiber d
  rw [sum_add_distrib, sum_add_distrib, hsum_fst, hsum_snd, sum_const, card_univ, smul_eq_mul,
    G.dart_card_eq_twice_card_edges, ← two_mul] at htot
  rw [htot, mul_assoc, mul_comm #G.edgeFinset]

private theorem filter_edgeFinset_triple_of_nonadj {d : G.Dart} {w : V}
    (hw₁ : ¬ G.Adj d.fst w) (hw₂ : ¬ G.Adj d.snd w) :
    {e ∈ G.edgeFinset | e.toFinset ⊆ ({d.fst, d.snd, w} : Finset V)} = {d.edge} := by
  ext e
  simp only [mem_filter, mem_edgeFinset, mem_singleton]
  refine ⟨fun ⟨he, hsub⟩ ↦ ?_, fun h ↦ h ▸ ⟨d.edge_mem, ?_⟩⟩
  · induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := G.mem_edgeSet.mp he
      have hx : x ∈ ({d.fst, d.snd, w} : Finset V) := hsub (by simp)
      have hy : y ∈ ({d.fst, d.snd, w} : Finset V) := hsub (by simp)
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact False.elim (hxy.ne rfl)
      · rfl
      · exact False.elim (hw₁ hxy)
      · exact Sym2.eq_swap
      · exact False.elim (hxy.ne rfl)
      · exact False.elim (hw₂ hxy)
      · exact False.elim (hw₁ hxy.symm)
      · exact False.elim (hw₂ hxy.symm)
      · exact False.elim (hxy.ne rfl)
  · intro x hx
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hx) with rfl | rfl <;> simp

private theorem dart_nonadj_mem_oddTriangleFinset {d : G.Dart} {w : V}
    (hw₁ : ¬ G.Adj d.fst w) (hw₂ : ¬ G.Adj d.snd w) :
    ({d.fst, d.snd, w} : Finset V) ∈ G.oddTriangleFinset := by
  rw [mem_oddTriangleFinset, filter_edgeFinset_triple_of_nonadj hw₁ hw₂, card_singleton]
  exact ⟨card_eq_three.mpr
    ⟨d.fst, d.snd, w, d.adj.ne, fun h ↦ hw₂ (h ▸ d.adj.symm), fun h ↦ hw₁ (h ▸ d.adj), rfl⟩,
    odd_one⟩

private theorem exists_dart_nonadj_of_mem_oddTriangleFinset (hG : G.CliqueFree 3) {s : Finset V}
    (hs : s ∈ G.oddTriangleFinset) :
    ∃ (d₀ : G.Dart) (w : V), ¬ G.Adj d₀.fst w ∧ ¬ G.Adj d₀.snd w ∧
      ({d₀.fst, d₀.snd, w} : Finset V) = s := by
  obtain ⟨hs3, h1⟩ := (mem_oddTriangleFinset_iff_of_cliqueFree hG).mp hs
  obtain ⟨e, he⟩ := card_eq_one.mp h1
  have he_mem : e ∈ {e' ∈ G.edgeFinset | e'.toFinset ⊆ s} := he ▸ mem_singleton_self e
  rw [mem_filter, mem_edgeFinset] at he_mem
  induction e using Sym2.ind with
  | _ u v =>
    let d₀ : G.Dart := ⟨(u, v), G.mem_edgeSet.mp he_mem.1⟩
    have hu : u ∈ s := he_mem.2 (by simp)
    have hv : v ∈ s := he_mem.2 (by simp)
    have hcard_sdiff : #(s \ {u, v}) = 1 := by
      have hsub : ({u, v} : Finset V) ⊆ s := fun x hx ↦ by
        rcases mem_insert.mp hx with rfl | hx'
        · exact hu
        · exact mem_singleton.mp hx' ▸ hv
      rw [card_sdiff_of_subset hsub, hs3, card_pair d₀.adj.ne]
    obtain ⟨w, hw⟩ := card_eq_one.mp hcard_sdiff
    have hw_mem : w ∈ s \ {u, v} := hw ▸ mem_singleton_self w
    rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hw_mem
    have hnonadj {x : V} (hx : x ∈ s) (hadj : G.Adj x w) : False := by
      have hmem : s(x, w) ∈ {e' ∈ G.edgeFinset | e'.toFinset ⊆ s} := by
        rw [mem_filter, mem_edgeFinset]
        refine ⟨G.mem_edgeSet.mpr hadj, fun y hy ↦ ?_⟩
        rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hy) with rfl | rfl
        · exact hx
        · exact hw_mem.1
      rcases Sym2.eq_iff.mp (mem_singleton.mp (he ▸ hmem)) with ⟨-, hwv⟩ | ⟨-, hwu⟩
      · exact hw_mem.2.2 hwv
      · exact hw_mem.2.1 hwu
    refine ⟨d₀, w, hnonadj hu, hnonadj hv, ?_⟩
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hu
      · exact hv
      · exact hw_mem.1
    · by_cases hxu : x = u
      · simp [d₀, hxu]
      · by_cases hxv : x = v
        · simp [d₀, hxv]
        · have hxw : x ∈ s \ {u, v} := by simp [hx, hxu, hxv]
          rw [hw, mem_singleton] at hxw
          simp [hxw]

private theorem card_dart_nonadj_fiber (hG : G.CliqueFree 3) {s : Finset V}
    (hs : s ∈ G.oddTriangleFinset) :
    #{p : G.Dart × V | (¬ G.Adj p.1.fst p.2 ∧ ¬ G.Adj p.1.snd p.2) ∧
      ({p.1.fst, p.1.snd, p.2} : Finset V) = s} = 2 := by
  obtain ⟨d₀, w, hn1, hn2, rfl⟩ := exists_dart_nonadj_of_mem_oddTriangleFinset hG hs
  have hedge := filter_edgeFinset_triple_of_nonadj hn1 hn2
  have hfib_eq :
      ({p : G.Dart × V | (¬ G.Adj p.1.fst p.2 ∧ ¬ G.Adj p.1.snd p.2) ∧
        ({p.1.fst, p.1.snd, p.2} : Finset V) = {d₀.fst, d₀.snd, w}} : Finset (G.Dart × V)) =
      {(d₀, w), (d₀.symm, w)} := by
    ext ⟨d, w'⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, hset⟩
      have hd_or : d = d₀ ∨ d = d₀.symm := by
        apply (dart_edge_eq_iff d d₀).mp
        rw [← mem_singleton, ← hedge, ← hset, filter_edgeFinset_triple_of_nonadj hd1 hd2,
          mem_singleton]
      have hw'_ne1 : w' ≠ d.fst := fun h ↦ hd2 (h ▸ d.adj.symm)
      have hw'_ne2 : w' ≠ d.snd := fun h ↦ hd1 (h ▸ d.adj)
      have hw' : w' ∈ ({d₀.fst, d₀.snd, w} : Finset V) := hset ▸ by simp
      simp only [mem_insert, mem_singleton] at hw'
      rcases hd_or with rfl | rfl
      · exact Or.inl ⟨rfl, hw'.resolve_left hw'_ne1 |>.resolve_left hw'_ne2⟩
      · exact Or.inr ⟨rfl, hw'.resolve_left hw'_ne2 |>.resolve_left hw'_ne1⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨hn1, hn2⟩, rfl⟩
      · refine ⟨⟨hn2, hn1⟩, ?_⟩
        ext x
        simp [or_left_comm]
  rw [hfib_eq, card_pair]
  intro h
  exact d₀.symm_ne.symm (Prod.mk.inj h).1

/-- **Kozlov's odd-triangle identity**: in a `3`-clique-free finite graph, the number of `3`-vertex
subsets spanning an odd number of edges plus the sum of squared vertex degrees equals
`Fintype.card V * #G.edgeFinset` (Kozlov, arXiv:1610.07136v2, equation (2.5)). -/
theorem card_oddTriangleFinset_add_sum_degree_sq (hG : G.CliqueFree 3) :
    #G.oddTriangleFinset + ∑ v : V, G.degree v ^ 2 = Fintype.card V * #G.edgeFinset := by
  let P : Finset (G.Dart × V) := {p : G.Dart × V | ¬ G.Adj p.1.fst p.2 ∧ ¬ G.Adj p.1.snd p.2}
  have hP_sum : #P = ∑ d : G.Dart, #{w : V | ¬ G.Adj d.fst w ∧ ¬ G.Adj d.snd w} := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun d _ ↦ card_nbij' Prod.snd (fun w ↦ (d, w)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [P, mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      exact hp.2 ▸ hp.1
    · intro w hw
      simp only [P, mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hw, trivial⟩
    · intro p hp
      simp only [mem_coe, mem_filter] at hp
      exact Prod.ext hp.2.symm rfl
    · intro _ _
      rfl
  have hP_odd : #P = 2 * #G.oddTriangleFinset := by
    rw [card_eq_sum_card_fiberwise
      (f := fun p : G.Dart × V ↦ ({p.1.fst, p.1.snd, p.2} : Finset V))
      (t := G.oddTriangleFinset)
      (fun p hp ↦ by
        simp only [P, mem_coe, mem_filter, mem_univ, true_and] at hp
        exact dart_nonadj_mem_oddTriangleFinset hp.1 hp.2)]
    have hconst :
        (∑ s ∈ G.oddTriangleFinset, #{p ∈ P | ({p.1.fst, p.1.snd, p.2} : Finset V) = s}) =
          ∑ _s ∈ G.oddTriangleFinset, 2 := by
      refine sum_congr rfl fun s hs ↦ ?_
      rw [filter_filter]
      exact card_dart_nonadj_fiber hG hs
    rw [hconst, sum_const, smul_eq_mul, mul_comm]
  have hmain := sum_dart_nonadj_add_two_mul_sum_degree_sq hG
  omega

/-- Explicit formula for `#G.oddTriangleFinset` in a `3`-clique-free finite graph. -/
theorem card_oddTriangleFinset_eq_of_cliqueFree (hG : G.CliqueFree 3) :
    #G.oddTriangleFinset = Fintype.card V * #G.edgeFinset - ∑ v : V, G.degree v ^ 2 := by
  have h := G.card_oddTriangleFinset_add_sum_degree_sq hG
  omega

omit [DecidableEq V] in
/-- A finite graph in which every vertex has degree at most `1` is `3`-clique-free. -/
theorem cliqueFree_three_of_degree_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 1) : G.CliqueFree 3 := by
  classical
  intro t ht
  have hcard := ht.card_eq
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < #t)
  have hsub : t.erase v ⊆ G.neighborFinset v := fun w hw ↦ by
    rw [mem_erase] at hw
    exact (G.mem_neighborFinset v w).mpr (ht.isClique hv hw.2 hw.1.symm)
  have hle : #(t.erase v) ≤ G.degree v :=
    G.card_neighborFinset_eq_degree v ▸ card_le_card hsub
  have hvdeg := hdeg v
  rw [card_erase_of_mem hv, hcard] at hle
  omega

/-- In a finite graph of maximum degree at most `1`, the number of `3`-vertex subsets spanning an
odd number of edges equals `(Fintype.card V - 2) * #G.edgeFinset`. -/
theorem card_oddTriangleFinset_of_degree_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hdeg : ∀ v, G.degree v ≤ 1) :
    #G.oddTriangleFinset = (Fintype.card V - 2) * #G.edgeFinset := by
  have hchoose : ∑ v : V, (G.degree v).choose 2 = 0 :=
    sum_eq_zero fun v _ ↦ Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le (hdeg v))
  have hcf := G.cliqueFree_three_of_degree_le_one hdeg
  have h := hcf.card_oddTripleFinset_add_two_mul_sum_degree_choose_two
  rw [← G.oddTriangleFinset_eq_oddTripleFinset, hchoose, mul_zero, add_zero] at h
  rw [h]
  exact congrArg ((Fintype.card V - 2) * ·)
    (congrArg card ((@edgeFinset_inj _ G G G.fintypeEdgeSet _).mpr rfl))

end CliqueFree

section Triples

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three vertices form an odd triangle exactly when an odd number of the three pairs are adjacent.
If two of the vertices coincide, both sides are false. -/
@[simp 1100, grind =]
theorem triple_mem_oddTriangleFinset_iff {a b c : V} :
    {a, b, c} ∈ G.oddTriangleFinset ↔ Xor (G.Adj a b) (Xor (G.Adj a c) (G.Adj b c)) := by
  rw [mem_oddTriangleFinset, filter_edgeFinset_toFinset_subset, ← mem_oddTripleFinset,
    triple_mem_oddTripleFinset_iff]

end Triples

/-- Switching a finite graph by a complete-graph cut preserves `oddTriangleFinset`. -/
@[simp]
theorem oddTriangleFinset_symmDiff_top_between (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).oddTriangleFinset = G.oddTriangleFinset := by
  ext s
  by_cases hs : #s = 3
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs
    simp only [triple_mem_oddTriangleFinset_iff]
    rw [(G ∆ _).adj_comm a c, G.adj_comm a c, xor_comm ((G ∆ _).Adj c a), xor_comm (G.Adj c a)]
    exact G.xor_symmDiff_top_between_compl_adj S a b c
  · simp [mem_oddTriangleFinset, hs]

end Basic

section Order

variable [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Over a linear order, the odd triangles are counted by their increasing triples `u < v < w`:
each odd triangle is `{u, v, w}` for exactly one such triple. -/
theorem card_oddTriangleFinset_eq_sum :
    #G.oddTriangleFinset = ∑ u : V, ∑ v : V, ∑ w : V,
      if u < v ∧ v < w ∧ Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) then 1 else 0 := by
  have h : #G.oddTriangleFinset = #({p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      {p.1, p.2.1, p.2.2} ∈ G.oddTriangleFinset} : Finset _) := by
    symm
    refine card_bij (fun p _ => {p.1, p.2.1, p.2.2}) (fun p hp => (mem_filter.mp hp).2.2.2) ?_ ?_
    · rintro ⟨a, b, c⟩ ha ⟨a', b', c'⟩ hb h
      obtain ⟨-, hab, hbc, -⟩ := mem_filter.mp ha
      obtain ⟨-, hab', hbc', -⟩ := mem_filter.mp hb
      have := Set.powersetCard.ofLtTriple.injective (a₁ := ⟨(a, b, c), hab, hbc⟩)
        (a₂ := ⟨(a', b', c'), hab', hbc'⟩)
        (Subtype.ext (by simpa only [Set.powersetCard.val_ofLtTriple] using h))
      simpa using congrArg Subtype.val this
    · intro s hs
      obtain ⟨a, b, c, hab, hbc, hs3⟩ :=
        Set.powersetCard.exists_lt_lt_val_eq ⟨s, (mem_oddTriangleFinset.mp hs).1⟩
      refine ⟨(a, b, c), ?_, hs3.symm⟩
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hab, hbc, hs3 ▸ hs⟩
  rw [h, card_filter]
  simp only [Fintype.sum_prod_type, triple_mem_oddTriangleFinset_iff]

end Order

/-- On a finite linearly ordered vertex type, `#G.oddTriangleFinset` counts the strictly increasing
vertex triples `(u, v, w)` around which an odd number of pairs are adjacent in `G`. -/
theorem card_oddTriangleFinset_eq_card_filter_lt [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.oddTriangleFinset =
      #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} := by
  symm
  refine card_bij (fun p _ ↦ ({p.1, p.2.1, p.2.2} : Finset V)) ?_ ?_ ?_
  · rintro ⟨u, v, w⟩ hp
    obtain ⟨-, -, hxor⟩ := (mem_filter.mp hp).2
    rw [triple_mem_oddTriangleFinset_iff, G.adj_comm u w, xor_comm (G.Adj w u)]
    exact hxor
  · rintro ⟨u₁, v₁, w₁⟩ hp₁ ⟨u₂, v₂, w₂⟩ hp₂ htri
    obtain ⟨huv₁, hvw₁, -⟩ := (mem_filter.mp hp₁).2
    obtain ⟨huv₂, hvw₂, -⟩ := (mem_filter.mp hp₂).2
    exact congrArg Subtype.val
      (Set.powersetCard.ofLtTriple.injective
        (a₁ := ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩) (a₂ := ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩)
        (Subtype.ext <| (Set.powersetCard.val_ofLtTriple ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩).trans
          (htri.trans (Set.powersetCard.val_ofLtTriple ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩).symm)))
  · intro s hs
    obtain ⟨hs3, -⟩ := mem_oddTriangleFinset.mp hs
    obtain ⟨u, v, w, huv, hvw, rfl⟩ := Set.powersetCard.exists_lt_lt_val_eq ⟨s, hs3⟩
    refine ⟨(u, v, w), mem_filter.mpr ⟨mem_univ _, huv, hvw, ?_⟩, rfl⟩
    have hxor := triple_mem_oddTriangleFinset_iff.mp hs
    rwa [G.adj_comm u w, xor_comm (G.Adj w u)] at hxor

end SimpleGraph
