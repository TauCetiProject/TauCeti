/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import TauCeti.Combinatorics.SimpleGraph.Coloring.Edge
public import TauCeti.Combinatorics.SimpleGraph.Matching.Regular

/-!
# Kőnig's edge-colouring theorem and chromatic index of bipartite simple graphs

Kőnig's edge-colouring theorem states that a bipartite graph admits a proper `k`-edge-colouring if
and only if every vertex is incident with at most `k` edges, so its chromatic index equals the
supremum of its vertex degrees.

This file proves Kőnig's theorem for arbitrary bipartite simple graphs — without finiteness or
decidability assumptions on the vertex or edge sets — together with its locally finite (`degree`
and `ncard`) and finite (`maxDegree`) specializations:

1. **Locally finite regular bipartite graphs** (`SimpleGraph.IsRegularOfDegree.edgeColorable` and
   `SimpleGraph.IsRegularOfDegree.chromaticIndex_eq`): on a locally finite `k`-regular bipartite
   simple graph, the perfect-matching decomposition into `k` matchings gives a proper
   `k`-edge-colouring directly, and `χ'(G) = k` whenever `V` is nonempty.
2. **General bipartite simple graphs**
   (`SimpleGraph.IsBipartite.edgeColorable_iff_forall_encard_neighborSet_le` and
   `SimpleGraph.IsBipartite.chromaticIndex_eq_iSup_encard_neighborSet`): for any bipartite simple
   graph `G`, `G.EdgeColorable k` holds iff `(G.neighborSet v).encard ≤ k` for every `v`, and
   `G.chromaticIndex = ⨆ v, (G.neighborSet v).encard`. Specialising yields the `degree` formulation
   under `[G.LocallyFinite]`, the `ncard` formulation under `[∀ v : V, Finite (G.neighborSet v)]`
   (which requires no `Fintype` or `DecidableRel` instances and automatically covers both
   `[G.LocallyFinite]` and `[Finite V]`), and the `G.maxDegree` equivalence and chromatic-index
   formula on finite graphs.

As applications, we compute the chromatic index of `completeBipartiteGraph V W` (for arbitrary
nonempty `V` and `W`, finite or infinite), even `cycleGraph n`, and `pathGraph n`.

## Implementation notes

Rather than reducing to the finite multigraph Kőnig theorem — which requires finitely many edges —
we embed a locally finite bipartite simple graph `G` of degree at most `k > 0` into a locally
finite `k`-regular bipartite simple graph `regularCompletion G k` on `V × Fin k × Bool` by taking
`k` copies of `(G, false)` and `k` copies of `(G, true)` and joining `(v, i, false)` to
`(v, j, true)` whenever `(i + j : Fin k).val < k - G.degree v`. Applying
`SimpleGraph.IsRegularOfDegree.edgeColorable` (which handles infinite vertex sets via Mathlib's
compactness-based Hall theorem) and pulling back along `v ↦ (v, 0, false)` proves the locally
finite theorem, from which the unrestricted `encard` theorem follows because a finite uniform bound
`(G.neighborSet v).encard ≤ k` forces `G` to be locally finite.

## Main results

* `SimpleGraph.IsRegularOfDegree.edgeColorable` and
  `SimpleGraph.IsRegularOfDegree.chromaticIndex_eq`: a locally finite `k`-regular bipartite graph
  is `k`-edge-colourable and (when `Nonempty V`) has chromatic index `k`.
* `SimpleGraph.IsBipartite.edgeColorable_iff_forall_encard_neighborSet_le`,
  `SimpleGraph.IsBipartite.exists_matching_partition_iff_forall_encard_neighborSet_le`, and
  `SimpleGraph.IsBipartite.chromaticIndex_eq_iSup_encard_neighborSet`: Kőnig's edge-colouring
  theorem and chromatic-index formula for arbitrary bipartite simple graphs.
* `SimpleGraph.IsBipartite.edgeColorable_iff_forall_degree_le` and
  `SimpleGraph.IsBipartite.chromaticIndex_eq_iSup_degree`: locally finite `degree` formulations.
* `SimpleGraph.IsBipartite.edgeColorable_iff_forall_ncard_neighborSet_le` and
  `SimpleGraph.IsBipartite.chromaticIndex_eq_iSup_ncard_neighborSet`: `ncard` formulations under
  `[∀ v : V, Finite (G.neighborSet v)]`.
* `SimpleGraph.IsBipartite.edgeColorable_iff_maxDegree_le`,
  `SimpleGraph.IsBipartite.edgeColorable_maxDegree`, and
  `SimpleGraph.IsBipartite.chromaticIndex_eq_maxDegree`: finite `maxDegree` formulations.
* `SimpleGraph.CompleteBipartiteGraph.chromaticIndex`,
  `SimpleGraph.chromaticIndex_cycleGraph_of_even`, and `SimpleGraph.chromaticIndex_pathGraph`:
  chromatic indices of complete bipartite, even cycle, and path graphs.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916), 104--119.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Function Set

universe u v

namespace SimpleGraph

section General

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

/-! ### Locally finite regular bipartite graphs -/

/-- Every locally finite `k`-regular bipartite simple graph is `k`-edge-colourable, even on an
infinite vertex type. -/
theorem IsRegularOfDegree.edgeColorable [G.LocallyFinite] (hG : G.IsRegularOfDegree k)
    (hbip : G.IsBipartite) : G.EdgeColorable k := by
  obtain ⟨M, hM, hdisj, hcover⟩ := hG.exists_perfectMatching_decomposition hbip
  exact G.edgeColorable_iff_exists_matchings.2 ⟨M, fun i ↦ (hM i).1, hdisj, hcover⟩

/-- A nonempty locally finite `k`-regular bipartite simple graph has chromatic index `k`. -/
theorem IsRegularOfDegree.chromaticIndex_eq [G.LocallyFinite] [Nonempty V]
    (hG : G.IsRegularOfDegree k) (hbip : G.IsBipartite) :
    G.chromaticIndex = k := by
  refine le_antisymm (G.chromaticIndex_le_iff_edgeColorable.2 (hG.edgeColorable hbip)) ?_
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← hG.degree_eq v]
  exact G.degree_le_chromaticIndex v

/-! ### Regular completion of a locally finite bipartite simple graph -/

/-- Auxiliary bipartite graph on `V × Fin k × Bool` built from `k` copies of `(G, false)` and `k`
copies of `(G, true)` by adding `k - (G.neighborSet v).ncard` cross-edges between
`{v} × Fin k × {false}` and `{v} × Fin k × {true}` at each vertex `v`. -/
private def regularCompletion (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (V × Fin k × Bool) where
  Adj p q :=
    (p.snd = q.snd ∧ G.Adj p.fst q.fst) ∨
      (p.fst = q.fst ∧ p.snd.snd ≠ q.snd.snd ∧
        (p.snd.fst + q.snd.fst).val < k - (G.neighborSet p.fst).ncard)
  symm := ⟨fun p q h ↦ by
    rcases eq_zero_or_neZero k with rfl | _
    · exact p.snd.fst.elim0
    · rcases h with ⟨h2, hadj⟩ | ⟨h1, hb, hlt⟩
      · exact Or.inl ⟨h2.symm, hadj.symm⟩
      · refine Or.inr ⟨h1.symm, hb.symm, ?_⟩
        rwa [add_comm q.snd.fst p.snd.fst, ← h1]⟩
  loopless := ⟨fun p h ↦ by
    rcases h with ⟨_, hadj⟩ | ⟨_, hb, _⟩
    · exact G.loopless.irrefl _ hadj
    · exact hb rfl⟩

/-- `regularCompletion G k` inherits bipartiteness from `G` by flipping the `2`-colouring of `G`
across the `Bool` coordinate. -/
private theorem isBipartite_regularCompletion (hbip : G.IsBipartite) :
    (regularCompletion G k).IsBipartite := by
  obtain ⟨C⟩ := hbip
  let c : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv C
  refine ⟨(regularCompletion G k).recolorOfEquiv finTwoEquiv.symm
    (Coloring.mk (fun p ↦ bne (c p.fst) p.snd.snd) fun {p q} h ↦ ?_)⟩
  rcases h with ⟨h2, hadj⟩ | ⟨h1, hb, -⟩
  · have hne : c p.fst ≠ c q.fst := c.valid hadj
    have : p.snd.snd = q.snd.snd := congrArg Prod.snd h2
    cases hcp : c p.fst <;> cases hcq : c q.fst <;> cases hp : p.snd.snd <;> simp_all
  · rw [h1]
    cases hcq : c q.fst <;> cases hp : p.snd.snd <;> cases hq : q.snd.snd <;> simp_all

/-- Explicit description of the neighbour set of `p` in `regularCompletion G k` as the union of
its `G`-neighbours in the same `(Fin k × Bool)` fibre and its cross-neighbours in `!p.snd.snd`. -/
private theorem neighborSet_regularCompletion (G : SimpleGraph V) (k : ℕ)
    (p : V × Fin k × Bool) :
    (regularCompletion G k).neighborSet p =
      ((fun v ↦ (v, p.snd)) '' G.neighborSet p.fst) ∪
        ((fun j ↦ (p.fst, j, !p.snd.snd)) ''
          {j : Fin k | (p.snd.fst + j).val < k - (G.neighborSet p.fst).ncard}) := by
  rcases p with ⟨u, i, b⟩
  ext ⟨v, j, b'⟩
  simp only [mem_neighborSet, regularCompletion, mem_union, mem_image, mem_ofPred_eq,
    Prod.mk.injEq]
  constructor
  · rintro (⟨⟨rfl, rfl⟩, hadj⟩ | ⟨rfl, hb, hlt⟩)
    · exact Or.inl ⟨v, hadj, rfl, rfl, rfl⟩
    · refine Or.inr ⟨j, hlt, rfl, rfl, ?_⟩
      cases b <;> cases b' <;> simp_all
  · rintro (⟨w, hadj, rfl, rfl, rfl⟩ | ⟨j', hlt, rfl, rfl, rfl⟩)
    · exact Or.inl ⟨⟨rfl, rfl⟩, hadj⟩
    · refine Or.inr ⟨rfl, ?_, hlt⟩
      cases b <;> simp

/-- When every vertex of `G` has degree at most `k`, every vertex of `regularCompletion G k` has
neighbour-set cardinality `k`. -/
private theorem ncard_neighborSet_regularCompletion [G.LocallyFinite] [NeZero k]
    (hk : ∀ v : V, G.degree v ≤ k) (p : V × Fin k × Bool) :
    ((regularCompletion G k).neighborSet p).ncard = k := by
  let A : Set (V × Fin k × Bool) := (fun v ↦ (v, p.snd)) '' G.neighborSet p.fst
  let S : Set (Fin k) := {j : Fin k | (p.snd.fst + j).val < k - (G.neighborSet p.fst).ncard}
  let B : Set (V × Fin k × Bool) := (fun j ↦ (p.fst, j, !p.snd.snd)) '' S
  have hdisj : Disjoint A B := Set.disjoint_left.2 fun _ ⟨_, _, ha⟩ ⟨_, _, hb⟩ ↦ by
    have := (congrArg (fun q ↦ q.snd.snd) ha).trans (congrArg (fun q ↦ q.snd.snd) hb).symm
    cases p.snd.snd <;> simp at this
  have hS : S = (fun x : Fin (k - (G.neighborSet p.fst).ncard) ↦
      Fin.castLE (Nat.sub_le k (G.neighborSet p.fst).ncard) x - p.snd.fst) '' univ := by
    ext j
    simp only [S, mem_ofPred_eq, mem_image, mem_univ, true_and]
    refine ⟨fun hj ↦ ⟨⟨(p.snd.fst + j).val, hj⟩, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
    · exact add_sub_cancel_left p.snd.fst j
    · rw [← hx, add_sub_cancel]
      exact x.isLt
  rw [neighborSet_regularCompletion,
    ncard_union_eq hdisj ((G.neighborSet p.fst).toFinite.image _) ((toFinite S).image _),
    ncard_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h),
    ncard_image_of_injective _ (fun _ _ h ↦ congrArg (fun q ↦ q.snd.fst) h), hS,
    ncard_image_of_injective _ (fun _ _ h ↦ Fin.castLE_injective _ (sub_left_inj.1 h)),
    ncard_univ, Nat.card_fin, ncard_neighborSet]
  exact Nat.add_sub_of_le (hk p.fst)

/-! ### Kőnig's edge-colouring theorem for bipartite simple graphs -/

namespace IsBipartite

/-- **Kőnig's edge-colouring theorem for locally finite simple graphs.** A locally finite bipartite
simple graph (whose vertex and edge sets may be infinite) is `k`-edge-colourable if and only if
every vertex has degree at most `k`. -/
theorem edgeColorable_iff_forall_degree_le [G.LocallyFinite] (hbip : G.IsBipartite) :
    G.EdgeColorable k ↔ ∀ v : V, G.degree v ≤ k := by
  constructor
  · intro hc v
    obtain ⟨c⟩ := hc
    simpa using EdgeColoring.degree_le_card c v
  · intro hk
    rcases eq_zero_or_neZero k with rfl | _
    · refine G.edgeColorable_zero_iff.2 ?_
      ext u v
      simp only [bot_adj, iff_false]
      exact fun huv ↦ by have := huv.degree_pos_left; have := hk u; omega
    · classical
      let H := regularCompletion G k
      have hHfin (p : V × Fin k × Bool) : (H.neighborSet p).Finite := by
        rw [neighborSet_regularCompletion]
        exact ((G.neighborSet p.fst).toFinite.image _).union ((toFinite _).image _)
      let _ : H.LocallyFinite := fun p ↦ (hHfin p).fintype
      have hreg : H.IsRegularOfDegree k := fun p ↦ by
        rw [← H.ncard_neighborSet p]
        exact ncard_neighborSet_regularCompletion hk p
      let f : Copy G H :=
        ⟨⟨fun v ↦ (v, 0, false), fun h ↦ Or.inl ⟨rfl, h⟩⟩, fun _ _ h ↦ congrArg Prod.fst h⟩
      exact (hreg.edgeColorable (isBipartite_regularCompletion hbip)).of_isContained ⟨f⟩

/-- **Kőnig's edge-colouring theorem for arbitrary bipartite simple graphs.** A bipartite simple
graph `G` is `k`-edge-colourable if and only if `(G.neighborSet v).encard ≤ k` for every vertex
`v`. -/
theorem edgeColorable_iff_forall_encard_neighborSet_le (hbip : G.IsBipartite) :
    G.EdgeColorable k ↔ ∀ v : V, (G.neighborSet v).encard ≤ k := by
  constructor
  · intro hc v
    exact (G.encard_neighborSet_le_chromaticIndex v).trans
      (G.chromaticIndex_le_iff_edgeColorable.2 hc)
  · intro hk
    classical
    have hfin (v : V) : (G.neighborSet v).Finite :=
      encard_lt_top_iff.1 ((hk v).trans_lt (ENat.natCast_lt_top k))
    let _ : G.LocallyFinite := fun v ↦ (hfin v).fintype
    refine hbip.edgeColorable_iff_forall_degree_le.2 fun v ↦ ?_
    rw [← G.ncard_neighborSet v]
    exact Nat.cast_le.1 (((hfin v).cast_ncard_eq).trans_le (hk v))

/-- In any bipartite simple graph, `G.edgeSet` is the pairwise disjoint union of `k` matchings if
and only if `(G.neighborSet v).encard ≤ k` for every vertex `v`. -/
theorem exists_matching_partition_iff_forall_encard_neighborSet_le (hbip : G.IsBipartite) :
    (∃ M : Fin k → G.Subgraph, (∀ i, (M i).IsMatching) ∧
      Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet) ↔
      ∀ v : V, (G.neighborSet v).encard ≤ k := by
  rw [← G.edgeColorable_iff_exists_matchings, hbip.edgeColorable_iff_forall_encard_neighborSet_le]

/-- For any bipartite simple graph, `G.chromaticIndex ≤ k` iff `(G.neighborSet v).encard ≤ k` for
every vertex `v`. -/
theorem chromaticIndex_le_iff_forall_encard_neighborSet_le (hbip : G.IsBipartite) :
    G.chromaticIndex ≤ k ↔ ∀ v : V, (G.neighborSet v).encard ≤ k := by
  rw [G.chromaticIndex_le_iff_edgeColorable, hbip.edgeColorable_iff_forall_encard_neighborSet_le]

/-- **Chromatic index of a bipartite simple graph.** For every bipartite simple graph `G` (finite
or infinite, without local-finiteness or decidability assumptions), `G.chromaticIndex` equals the
supremum of `(G.neighborSet v).encard` over `v : V` (which is `0` when `V` is empty or `G = ⊥`). -/
theorem chromaticIndex_eq_iSup_encard_neighborSet (hbip : G.IsBipartite) :
    G.chromaticIndex = ⨆ v : V, (G.neighborSet v).encard := by
  refine le_antisymm ?_ (iSup_le G.encard_neighborSet_le_chromaticIndex)
  rcases eq_or_ne (⨆ v : V, (G.neighborSet v).encard) ⊤ with htop | htop
  · simp [htop]
  · have hcast := ENat.natCast_toNat_eq_self.2 htop
    rw [← hcast, hbip.chromaticIndex_le_iff_forall_encard_neighborSet_le]
    exact fun v ↦ (le_iSup (fun u : V ↦ (G.neighborSet u).encard) v).trans_eq hcast.symm

/-- In any locally finite bipartite simple graph, `G.chromaticIndex` is the supremum of vertex
degrees. -/
theorem chromaticIndex_eq_iSup_degree [G.LocallyFinite] (hbip : G.IsBipartite) :
    G.chromaticIndex = ⨆ v : V, (G.degree v : ℕ∞) := by
  rw [hbip.chromaticIndex_eq_iSup_encard_neighborSet]
  refine iSup_congr fun v ↦ ?_
  rw [← G.ncard_neighborSet v, (toFinite (G.neighborSet v)).cast_ncard_eq]

/-- A bipartite simple graph whose vertices have finitely many neighbours is `k`-edge-colourable if
and only if every vertex has at most `k` neighbours. -/
theorem edgeColorable_iff_forall_ncard_neighborSet_le [∀ v : V, Finite (G.neighborSet v)]
    (hbip : G.IsBipartite) :
    G.EdgeColorable k ↔ ∀ v : V, (G.neighborSet v).ncard ≤ k := by
  rw [hbip.edgeColorable_iff_forall_encard_neighborSet_le]
  refine forall_congr' fun v ↦ ?_
  rw [← (G.neighborSet v).toFinite.cast_ncard_eq, Nat.cast_le]

/-- In a bipartite simple graph whose vertices have finitely many neighbours, `G.edgeSet` is the
pairwise disjoint union of `k` matchings if and only if every vertex has at most `k` neighbours. -/
theorem exists_matching_partition_iff_forall_ncard_neighborSet_le
    [∀ v : V, Finite (G.neighborSet v)] (hbip : G.IsBipartite) :
    (∃ M : Fin k → G.Subgraph, (∀ i, (M i).IsMatching) ∧
      Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet) ↔
      ∀ v : V, (G.neighborSet v).ncard ≤ k := by
  rw [← G.edgeColorable_iff_exists_matchings, hbip.edgeColorable_iff_forall_ncard_neighborSet_le]

/-- For a bipartite simple graph whose vertices have finitely many neighbours,
`G.chromaticIndex ≤ k` iff every vertex has at most `k` neighbours. -/
theorem chromaticIndex_le_iff_forall_ncard_neighborSet_le [∀ v : V, Finite (G.neighborSet v)]
    (hbip : G.IsBipartite) :
    G.chromaticIndex ≤ k ↔ ∀ v : V, (G.neighborSet v).ncard ≤ k := by
  rw [G.chromaticIndex_le_iff_edgeColorable, hbip.edgeColorable_iff_forall_ncard_neighborSet_le]

/-- For a bipartite simple graph whose vertices have finitely many neighbours, `G.chromaticIndex`
equals the supremum of `(G.neighborSet v).ncard` over `v : V`. -/
theorem chromaticIndex_eq_iSup_ncard_neighborSet [∀ v : V, Finite (G.neighborSet v)]
    (hbip : G.IsBipartite) :
    G.chromaticIndex = ⨆ v : V, ((G.neighborSet v).ncard : ℕ∞) := by
  rw [hbip.chromaticIndex_eq_iSup_encard_neighborSet]
  exact iSup_congr fun v ↦ (G.neighborSet v).toFinite.cast_ncard_eq.symm

/-- **Kőnig's edge-colouring theorem for finite simple graphs.** A finite bipartite simple graph is
`k`-edge-colourable if and only if its maximum degree is at most `k`. -/
theorem edgeColorable_iff_maxDegree_le [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.EdgeColorable k ↔ G.maxDegree ≤ k := by
  rw [hbip.edgeColorable_iff_forall_degree_le]
  exact ⟨G.maxDegree_le_of_forall_degree_le k, fun hk v ↦ (G.degree_le_maxDegree v).trans hk⟩

/-- Every finite bipartite simple graph is `(G.maxDegree)`-edge-colourable. -/
theorem edgeColorable_maxDegree [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.EdgeColorable G.maxDegree :=
  hbip.edgeColorable_iff_maxDegree_le.2 le_rfl

/-- **Kőnig's line-colouring theorem.** The chromatic index of a finite bipartite simple graph is
its maximum degree (`0` when `V` is empty). -/
theorem chromaticIndex_eq_maxDegree [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.chromaticIndex = G.maxDegree :=
  le_antisymm (G.chromaticIndex_le_iff_edgeColorable.2 hbip.edgeColorable_maxDegree)
    G.maxDegree_le_chromaticIndex

end IsBipartite

end General

/-! ### Chromatic index of canonical bipartite graphs -/

/-- On finite parts `V` and `W`, `completeBipartiteGraph V W` is
`(max (Nat.card V) (Nat.card W))`-edge-colourable, including when either part is empty. -/
theorem CompleteBipartiteGraph.edgeColorable_max (V : Type u) (W : Type v) [Finite V] [Finite W] :
    (completeBipartiteGraph V W).EdgeColorable (max (Nat.card V) (Nat.card W)) := by
  rw [(IsBipartite.completeBipartiteGraph V W).edgeColorable_iff_forall_encard_neighborSet_le]
  rintro (v | w)
  · have h : (completeBipartiteGraph V W).neighborSet (Sum.inl v) = Sum.inr '' univ := by
      ext (_ | _) <;> simp
    rw [h, Sum.inr_injective.encard_image, encard_univ, ENat.card_eq_coe_natCard]
    exact Nat.cast_le.2 (le_max_right _ _)
  · have h : (completeBipartiteGraph V W).neighborSet (Sum.inr w) = Sum.inl '' univ := by
      ext (_ | _) <;> simp
    rw [h, Sum.inl_injective.encard_image, encard_univ, ENat.card_eq_coe_natCard]
    exact Nat.cast_le.2 (le_max_left _ _)

/-- For any nonempty types `V` and `W` (finite or infinite), the chromatic index of
`completeBipartiteGraph V W` is `max (ENat.card V) (ENat.card W)`. -/
theorem CompleteBipartiteGraph.chromaticIndex (V : Type u) (W : Type v) [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticIndex = max (ENat.card V) (ENat.card W) := by
  rw [(IsBipartite.completeBipartiteGraph V W).chromaticIndex_eq_iSup_encard_neighborSet, iSup_sum]
  have hinl (v : V) :
      ((completeBipartiteGraph V W).neighborSet (Sum.inl v)).encard = ENat.card W := by
    have h : (completeBipartiteGraph V W).neighborSet (Sum.inl v) = Sum.inr '' univ := by
      ext (_ | _) <;> simp
    rw [h, Sum.inr_injective.encard_image, encard_univ]
  have hinr (w : W) :
      ((completeBipartiteGraph V W).neighborSet (Sum.inr w)).encard = ENat.card V := by
    have h : (completeBipartiteGraph V W).neighborSet (Sum.inr w) = Sum.inl '' univ := by
      ext (_ | _) <;> simp
    rw [h, Sum.inl_injective.encard_image, encard_univ]
  simp_rw [hinl, hinr, ciSup_const]
  exact sup_comm _ _

/-- `cycleGraph 2` has chromatic index `1`. -/
@[simp]
theorem chromaticIndex_cycleGraph_two : (cycleGraph 2).chromaticIndex = 1 := by
  have hreg : (cycleGraph 2).IsRegularOfDegree 1 := by
    intro v
    fin_cases v <;> decide
  exact hreg.chromaticIndex_eq (IsBipartite.cycleGraph_of_even ⟨1, rfl⟩)

/-- An even cycle graph on `n ≥ 3` vertices has chromatic index `2`. -/
theorem chromaticIndex_cycleGraph_of_even (n : ℕ) (hn : 3 ≤ n) (hEven : Even n) :
    (cycleGraph n).chromaticIndex = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hreg : (cycleGraph (m + 3)).IsRegularOfDegree 2 := fun _ ↦ cycleGraph_degree_three_le
  exact hreg.chromaticIndex_eq (IsBipartite.cycleGraph_of_even hEven)

/-- `pathGraph 2` has chromatic index `1`. -/
@[simp]
theorem chromaticIndex_pathGraph_two : (pathGraph 2).chromaticIndex = 1 := by
  have hreg : (pathGraph 2).IsRegularOfDegree 1 := by
    intro v
    fin_cases v <;> decide
  exact hreg.chromaticIndex_eq (IsBipartite.pathGraph 2)

/-- A path graph on `n ≥ 3` vertices has chromatic index `2`. -/
theorem chromaticIndex_pathGraph (n : ℕ) (hn : 3 ≤ n) : (pathGraph n).chromaticIndex = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← Nat.cast_two,
      (IsBipartite.pathGraph n).chromaticIndex_le_iff_forall_ncard_neighborSet_le]
    intro v
    have hsub : (pathGraph n).neighborSet v ⊆
        {w : Fin n | w.val = v.val - 1} ∪ {w : Fin n | w.val = v.val + 1} := by
      intro w hw
      rw [mem_neighborSet, pathGraph_adj] at hw
      simp only [mem_union, mem_ofPred_eq]
      rcases hw with hw | hw
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hs₁ : ({w : Fin n | w.val = v.val - 1} : Set (Fin n)).ncard ≤ 1 :=
      (ncard_le_one_iff).2 fun ha hb ↦ Fin.ext (ha.trans hb.symm)
    have hs₂ : ({w : Fin n | w.val = v.val + 1} : Set (Fin n)).ncard ≤ 1 :=
      (ncard_le_one_iff).2 fun ha hb ↦ Fin.ext (ha.trans hb.symm)
    exact (ncard_le_ncard hsub).trans ((ncard_union_le _ _).trans (Nat.add_le_add hs₁ hs₂))
  · have hv : (1 : ℕ) < n := by omega
    have h0 : ((pathGraph n).Adj ⟨1, hv⟩ ⟨0, by omega⟩) := by simp [pathGraph_adj]
    have h2 : ((pathGraph n).Adj ⟨1, hv⟩ ⟨2, hn⟩) := by simp [pathGraph_adj]
    have hsub : ({⟨0, by omega⟩, ⟨2, hn⟩} : Set (Fin n)) ⊆ (pathGraph n).neighborSet ⟨1, hv⟩ := by
      rintro w (rfl | rfl)
      · exact h0
      · exact h2
    have hcard : (2 : ℕ) ≤ ((pathGraph n).neighborSet ⟨1, hv⟩).ncard := by
      have hle := ncard_le_ncard hsub
      rwa [ncard_pair (by simp [Fin.ext_iff])] at hle
    exact (Nat.cast_le.2 hcard).trans ((pathGraph n).ncard_neighborSet_le_chromaticIndex ⟨1, hv⟩)

end SimpleGraph
