/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Sym
public import Mathlib.Order.Sym2
import TauCeti.Order.Sym2

/-!
# Finite simple graphs

A nonempty graph with finitely many edges has an edge minimizing any linearly ordered weight.

On a finite vertex set, `G ↦ G.edgeFinset` maps the graphs between `F` and `H` bijectively onto
the finsets of pairs between `F.edgeFinset` and `H.edgeFinset`. Consequently a product or sum over
an interval of graphs, of a factor that depends on the graph only through its edge set, is one over
an interval of the Boolean lattice `Finset (Sym2 V)`, where the finset interval API applies.

When the vertex type carries a linear order, `Sym2.sortEquiv` identifies `G.edgeSet` with strictly
increasing adjacent pairs `{p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}`, turning products, sums, and
cardinalities over `G.edgeFinset` into ones over `{p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2}`.

## Main results

* `SimpleGraph.neighborSetFintypeOfFinite` — a `Fintype` structure on the neighbour sets of a graph
  on a finite vertex type, for local selection where decidable adjacency is unavailable.
* `SimpleGraph.exists_minimum_weight_edge` — a finite nonempty edge set has a minimum-weight edge.
* `SimpleGraph.Iso.sum_neighborFinset_comp` — neighbour sums commute with graph isomorphisms.
* `SimpleGraph.edgeSet_fromEdgeSet_of_subset` — a set of edges of `G` is the edge set of the
  graph it generates.
* `SimpleGraph.edgeFinset_edge_of_ne`, `SimpleGraph.card_edgeFinset_edge_of_ne` — the edge finset
  and cardinality of a single-edge graph `SimpleGraph.edge u v` (`u ≠ v`).
* `SimpleGraph.card_edgeFinset_congr` — `#G.edgeFinset` is independent of the `Fintype G.edgeSet`
  instance.
* `SimpleGraph.edgeFinset_inter_sym2_triple`, `SimpleGraph.edgeFinset_inter_sym2_triple_subset`,
  `SimpleGraph.card_edgeFinset_inter_sym2_triple`, and
  `SimpleGraph.edgeFinset_inter_sym2_triple_of_adj_of_not_adj` — edges of `G` spanned by a vertex
  triple `{a, b, c}`.
* `SimpleGraph.prod_filter_le_le_eq_prod_Icc_edgeFinset` and its additive version
  `SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset` — a product (sum) over the graphs between
  `F` and `H` of a function of their edge finsets is the product (sum) of that function over
  `Finset.Icc F.edgeFinset H.edgeFinset`.
* `SimpleGraph.edgeSetEquivLtAdj`, `SimpleGraph.prod_edgeFinset_eq_prod_filter_lt`,
  `SimpleGraph.sum_edgeFinset_eq_sum_filter_lt`, and
  `SimpleGraph.card_edgeFinset_eq_card_filter_lt` — the equivalence between `G.edgeSet` and
  strictly ordered adjacent pairs, and the resulting product, sum, and cardinality identities.
-/

public section

open Finset

namespace SimpleGraph

variable {V K M : Type*}

/-- The neighbour sets of a graph on a finite vertex type are finite, from finiteness alone. This
is not an instance: with `DecidableRel G.Adj`, instance search finds the subtype `Fintype`
(`Subtype.fintype`), and the two structures are not definitionally equal. Files that need a
`Fintype` on neighbour sets without decidable adjacency select it as a local instance. It is
exposed because it is instance-reducible: statements elaborated with it as a local instance
record the unfolded `Fintype.ofFinite`, and importers must see the body to match them. -/
@[instance_reducible, expose]
noncomputable def neighborSetFintypeOfFinite [Finite V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- A graph with a finite nonempty edge set has an edge of minimum weight. -/
theorem exists_minimum_weight_edge (G : SimpleGraph V) [Finite G.edgeSet] (hG : G ≠ ⊥)
    [LinearOrder K] (w : Sym2 V → K) :
    ∃ u v, G.Adj u v ∧ ∀ e ∈ G.edgeSet, w s(u, v) ≤ w e := by
  let _ := Fintype.ofFinite G.edgeSet
  obtain ⟨e, he, hmin⟩ := G.edgeFinset.exists_min_image w (edgeFinset_nonempty.2 hG)
  induction e using Sym2.inductionOn with
  | _ u v =>
    exact ⟨u, v, G.mem_edgeSet.1 (mem_edgeFinset.1 he), fun e he' ↦ hmin e (mem_edgeFinset.2 he')⟩

/-- Summing a pulled-back function over neighbours commutes with a graph isomorphism. -/
theorem Iso.sum_neighborFinset_comp {W R : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] [AddCommMonoid R]
    (e : G ≃g H) (i : V) (a : W → R) :
    ∑ j ∈ G.neighborFinset i, a (e j) = ∑ j ∈ H.neighborFinset (e i), a j := by
  exact Finset.sum_equiv e.toEquiv
    (fun j ↦ by
      simpa only [mem_neighborFinset, RelIso.coe_fn_toEquiv] using e.map_adj_iff.symm)
    (fun _ _ ↦ by rw [RelIso.coe_fn_toEquiv])

/-- A set of pairs contained in the edges of a graph `G` carries no diagonal pair, so it is the
edge set of the graph it generates. -/
theorem edgeSet_fromEdgeSet_of_subset {G : SimpleGraph V} {s : Set (Sym2 V)}
    (hs : s ⊆ G.edgeSet) : (fromEdgeSet s).edgeSet = s := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  exact fun e he ↦ not_isDiag_of_mem_edgeSet G (hs he)

/-- The edge finset of a single-edge graph `SimpleGraph.edge u v` (`u ≠ v`) is `{s(u, v)}`. -/
@[simp]
theorem edgeFinset_edge_of_ne {u v : V} (huv : u ≠ v) [Fintype (edge u v).edgeSet] :
    (edge u v).edgeFinset = {s(u, v)} :=
  coe_injective <| by rw [coe_edgeFinset, Finset.coe_singleton, edgeSet_edge_of_ne huv]

/-- A single-edge graph `SimpleGraph.edge u v` (`u ≠ v`) has `1` edge. -/
theorem card_edgeFinset_edge_of_ne {u v : V} (huv : u ≠ v) [Fintype (edge u v).edgeSet] :
    #(edge u v).edgeFinset = 1 := by
  rw [edgeFinset_edge_of_ne huv, card_singleton]

/-- The cardinality of `G.edgeFinset` does not depend on the `Fintype G.edgeSet` instance. -/
theorem card_edgeFinset_congr (G : SimpleGraph V) (h₁ h₂ : Fintype G.edgeSet) :
    @Finset.card (Sym2 V) (@edgeFinset V G h₁) = @Finset.card (Sym2 V) (@edgeFinset V G h₂) := by
  have h : ((@edgeFinset V G h₁).card : ℕ∞) = (@edgeFinset V G h₂).card := by
    rw [← Set.encard_coe_eq_coe_finsetCard, ← Set.encard_coe_eq_coe_finsetCard,
      @coe_edgeFinset V G h₁, @coe_edgeFinset V G h₂]
  exact Nat.cast_injective h

/-- The edges of `G` spanned by three vertices `a`, `b`, `c` are the candidate pairs among
`{s(a, b), s(a, c), s(b, c)}` that belong to `G.edgeSet`. -/
theorem edgeFinset_inter_sym2_triple [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    [DecidableRel G.Adj] (a b c : V) :
    G.edgeFinset ∩ ({a, b, c} : Finset V).sym2 =
      ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter (· ∈ G.edgeSet) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_inter, mem_edgeFinset, mem_sym2_iff, Sym2.mem_iff, mem_filter,
      mem_insert, mem_singleton, mem_edgeSet, Sym2.eq_iff]
    constructor
    · rintro ⟨hxy, hx⟩
      have hx' := hx x (Or.inl rfl)
      have hy' := hx y (Or.inr rfl)
      refine ⟨?_, hxy⟩
      rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> simp_all
    · grind

/-- Every edge of `G` spanned by `{a, b, c}` is one of `s(a, b)`, `s(a, c)`, `s(b, c)`. -/
theorem edgeFinset_inter_sym2_triple_subset [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (a b c : V) :
    G.edgeFinset ∩ ({a, b, c} : Finset V).sym2 ⊆ {s(a, b), s(a, c), s(b, c)} := by
  classical
  rw [edgeFinset_inter_sym2_triple]
  exact filter_subset _ _

/-- The edges spanned by three distinct vertices are counted pair by pair. -/
theorem card_edgeFinset_inter_sym2_triple [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    [DecidableRel G.Adj] {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #(G.edgeFinset ∩ ({a, b, c} : Finset V).sym2) =
      (if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) +
        (if G.Adj b c then 1 else 0) := by
  rw [edgeFinset_inter_sym2_triple, card_filter, sum_insert, sum_insert, sum_singleton]
  · simp [add_assoc]
  · simp [hab, hbc.symm]
  · simp [hbc, hab.symm, hac]

/-- When `a` and `b` are adjacent in `G` and `c` is adjacent to neither `a` nor `b`, the only
edge of `G` spanned by `{a, b, c}` is `s(a, b)`. -/
theorem edgeFinset_inter_sym2_triple_of_adj_of_not_adj [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] {a b c : V} (hab : G.Adj a b) (hac : ¬ G.Adj a c) (hbc : ¬ G.Adj b c) :
    G.edgeFinset ∩ ({a, b, c} : Finset V).sym2 = {s(a, b)} := by
  classical
  rw [edgeFinset_inter_sym2_triple]
  ext e
  simp only [mem_filter, mem_insert, mem_singleton]
  exact ⟨fun ⟨hmem, he⟩ ↦ hmem.elim id
      (fun h ↦ h.elim (fun h' ↦ (hac (G.mem_edgeSet.mp (h' ▸ he))).elim)
        (fun h' ↦ (hbc (G.mem_edgeSet.mp (h' ▸ he))).elim)),
    fun h ↦ ⟨Or.inl h, h ▸ G.mem_edgeSet.mpr hab⟩⟩

section Interval

variable [Fintype V] [DecidableEq V] [CommMonoid M]

/-- Multiplying a function of the edge finset over the graphs between `F` and `H` is multiplying
it over the edge finsets between theirs. -/
@[to_additive /-- Summing a function of the edge finset over the graphs between `F` and `H` is
summing it over the edge finsets between theirs. -/]
theorem prod_filter_le_le_eq_prod_Icc_edgeFinset (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V ↦ F ≤ G ∧ G ≤ H]
    [∀ G : SimpleGraph V, Fintype G.edgeSet] (f : Finset (Sym2 V) → M) :
    ∏ G with F ≤ G ∧ G ≤ H, f G.edgeFinset = ∏ s ∈ Icc F.edgeFinset H.edgeFinset, f s := by
  -- An edge set below `H.edgeFinset` carries no diagonal pair, so it is the edge set of a graph.
  have hset : ∀ s ∈ Icc F.edgeFinset H.edgeFinset,
      (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := fun s hs ↦ coe_injective <| by
    rw [coe_edgeFinset, edgeSet_fromEdgeSet_of_subset fun e he ↦
      mem_edgeFinset.1 ((mem_Icc.1 hs).2 (mem_coe.1 he))]
  refine prod_nbij' (fun G ↦ G.edgeFinset) (fun s ↦ fromEdgeSet (s : Set (Sym2 V)))
    (fun G hG ↦ ?_) (fun s hs ↦ ?_) (fun G _ ↦ ?_) hset (fun G _ ↦ rfl)
  · simpa [edgeFinset_subset_edgeFinset] using hG
  · refine mem_coe.2 ((mem_filter_univ _).2 ?_)
    rw [← edgeFinset_subset_edgeFinset, ← edgeFinset_subset_edgeFinset, hset s hs]
    exact mem_Icc.1 hs
  · rw [coe_edgeFinset, fromEdgeSet_edgeSet]

end Interval

section Ordered

/-- When the vertex type is linearly ordered, `Sym2.sortEquiv` identifies the edges of `G` with the
strictly increasing adjacent vertex pairs. -/
def edgeSetEquivLtAdj [LinearOrder V] (G : SimpleGraph V) :
    G.edgeSet ≃ {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2} where
  toFun e :=
    have hadj : G.Adj e.val.inf e.val.sup := G.mem_edgeSet.mp (e.val.mk_inf_sup.symm ▸ e.property)
    ⟨(e.val.inf, e.val.sup), lt_of_le_of_ne (Sym2.inf_le_sup e.val) hadj.ne, hadj⟩
  invFun p := ⟨s(p.val.1, p.val.2), G.mem_edgeSet.mpr p.property.2⟩
  left_inv e := Subtype.ext e.val.mk_inf_sup
  right_inv p := Subtype.ext (by simp [p.property.1.le])

/-- `SimpleGraph.edgeSetEquivLtAdj` sends an edge `e` to `(e.inf, e.sup)`. -/
@[simp]
theorem coe_edgeSetEquivLtAdj_apply [LinearOrder V] (G : SimpleGraph V) (e : G.edgeSet) :
    (G.edgeSetEquivLtAdj e : V × V) = ((e : Sym2 V).inf, (e : Sym2 V).sup) :=
  (rfl)

/-- The inverse of `SimpleGraph.edgeSetEquivLtAdj` sends an ordered adjacent pair `(u, v)` to the
unordered edge `s(u, v)`. -/
@[simp]
theorem coe_edgeSetEquivLtAdj_symm_apply [LinearOrder V] (G : SimpleGraph V)
    (p : {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}) :
    (G.edgeSetEquivLtAdj.symm p : Sym2 V) = s(p.val.1, p.val.2) :=
  (rfl)

/-- On a finite linearly ordered vertex type, a product over `G.edgeFinset` equals the product over
strictly increasing adjacent pairs `(u, v)`. -/
@[to_additive /-- On a finite linearly ordered vertex type, a sum over `G.edgeFinset` equals the
sum over strictly increasing adjacent pairs `(u, v)`. -/]
theorem prod_edgeFinset_eq_prod_filter_lt [Fintype V] [LinearOrder V] [CommMonoid M]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet] (f : Sym2 V → M) :
    ∏ e ∈ G.edgeFinset, f e = ∏ p : V × V with p.1 < p.2 ∧ G.Adj p.1 p.2, f s(p.1, p.2) := by
  rw [prod_subtype G.edgeFinset (p := (· ∈ G.edgeSet)) (fun _ ↦ G.mem_edgeFinset),
    prod_subtype ({p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2} : Finset (V × V))
      (p := fun p : V × V ↦ p.1 < p.2 ∧ G.Adj p.1 p.2) (F := inferInstance) (by simp),
    ← G.edgeSetEquivLtAdj.symm.prod_comp (fun e : G.edgeSet ↦ f e.val)]
  simp only [coe_edgeSetEquivLtAdj_symm_apply]

/-- On a finite linearly ordered vertex type, `#G.edgeFinset` counts the strictly increasing
adjacent vertex pairs. -/
theorem card_edgeFinset_eq_card_filter_lt [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet] :
    #G.edgeFinset = #{p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2} := by
  simpa using G.sum_edgeFinset_eq_sum_filter_lt (fun _ ↦ (1 : ℕ))

end Ordered

end SimpleGraph
