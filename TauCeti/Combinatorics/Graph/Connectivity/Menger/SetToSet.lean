/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Network.Menger.SetToSet

/-!
# Menger's theorem between vertex sets in multigraphs

Let `G : Graph α β` be a multigraph with finitely many actual vertices, and let `A` and `B` be
finite sets of actual vertices. An *`A`–`B` path* runs from a vertex of `A` to a vertex of `B`,
with no other vertex in either terminal set. A vertex-capacitated packing is a finite indexed
family of such paths, repetitions allowed, in which each vertex `v`, including the endpoints,
occurs in at most `c v` members. A separator may meet `A` and `B`; its weight is the sum of the
capacities of its vertices.

This file proves that some vertex-capacitated packing and some separator have equal size and
weight. At unit capacity it gives pairwise vertex-disjoint paths and a separator of the same
cardinality. The terminal sets may be empty or overlap. In particular, a vertex of `A ∩ B` may
give a zero-length path, and every separator contains it. No finiteness assumption is made on the
edge set, so loops and arbitrary parallel edges are allowed.

## Main results

* `Graph.card_le_sum_of_forall_not_reachable_deleteVerts`: weak duality for vertex-capacitated
  packings between vertex sets.
* `Graph.exists_paths_setSeparator_sum_eq`: vertex-capacitated set-to-set Menger in witness form.
* `Graph.exists_paths_setSeparator_card_eq`: set-to-set Menger for vertex-disjoint paths.
* `Graph.forall_exists_reachable_deleteVerts_iff_exists_paths`: the corresponding predicate form.

Attainment is transported from the directed theorem for the bidirected arrow family on `V(G)`.
The walk equivalence preserves vertex sequences, paths, and disjointness.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

open Finset TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Vertex-capacitated packings -/

/-- **Weak duality for vertex-capacitated set-to-set packings.** A family of walks, each from a
vertex of `A` to a vertex of `B`, in which every vertex `v` lies on at most `c v` members, has at
most `∑ v ∈ X, c v` members whenever deleting `X` destroys reachability from every vertex of `A`
to every vertex of `B`. -/
theorem card_le_sum_of_forall_not_reachable_deleteVerts [DecidableEq α] {A B : Finset α}
    (hA : (A : Set α) ⊆ V(G)) {ι : Type*} [Fintype ι] {a b : ι → α}
    {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B) {c : α → ℕ}
    (hP : ∀ x, #{i | x ∈ (P i).support} ≤ c x) {X : Finset α}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteVerts X).Reachable a b) :
    Fintype.card ι ≤ ∑ x ∈ X, c x := by
  have h (i : ι) : ∃ x ∈ (P i).support, x ∈ X := by
    by_contra! hi
    exact hX (a i) (ha i) (b i) (hb i)
      (reachable_deleteVerts_iff_exists_walk.2 ⟨P i, hA (ha i), hi⟩)
  choose f hf hfX using h
  rw [← card_univ, card_eq_sum_card_fiberwise fun i _ ↦ hfX i]
  refine sum_le_sum fun x hx ↦ (card_le_card fun i hi ↦ ?_).trans (hP x)
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi ▸ hf i

/-- **Vertex-capacitated Menger's theorem between vertex sets in a multigraph.** Let `A` and `B`
be finite sets of actual vertices of a multigraph with finitely many actual vertices. Some family
of `k` paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with its other vertices in neither terminal
set, and some set `X` of actual vertices satisfy the following: every vertex `v` lies on at most
`c v` members, deleting `X` destroys all `A`–`B` reachability, and `∑ v ∈ X, c v = k`. -/
theorem exists_paths_setSeparator_sum_eq [Finite V(G)] [DecidableEq α] (c : α → ℕ)
    (A B : Finset α) (hA : (A : Set α) ⊆ V(G)) (hB : (B : Set α) ⊆ V(G)) :
    ∃ (k : ℕ) (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)) (X : Finset α),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ x ∈ (P i).support, x ≠ a i → x ≠ b i → x ∉ A ∧ x ∉ B) ∧
      (∀ x, #{i | x ∈ (P i).support} ≤ c x) ∧ (X : Set α) ⊆ V(G) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteVerts X).Reachable a b) ∧ ∑ x ∈ X, c x = k := by
  classical
  let A' := A.subtype (· ∈ V(G))
  let B' := B.subtype (· ∈ V(G))
  obtain ⟨k, a, b, P, X, ha, hb, hpath, hint, hPv, hX, hk⟩ :=
    TauCeti.exists_paths_setSeparator_sum_eq (Q := G.BidirectedHom) (fun x ↦ c x) A' B'
  refine ⟨k, fun i ↦ a i, fun i ↦ b i, fun i ↦ (P i).toGraphWalk,
    X.map (Function.Embedding.subtype _), fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ (P i).isPath_toGraphWalk_iff.2 (hpath i), ?_, ?_, map_subtype_subset X, ?_, ?_⟩
  · exact Finset.mem_subtype.1 (ha i)
  · exact Finset.mem_subtype.1 (hb i)
  · intro i x hx hxa hxb
    obtain ⟨hxG, hxP⟩ := (P i).mem_support_toGraphWalk_iff.1 hx
    have hi := hint i ⟨x, hxG⟩ hxP
      (fun h ↦ hxa (congrArg Subtype.val h)) (fun h ↦ hxb (congrArg Subtype.val h))
    exact ⟨fun hxA ↦ hi.1 (Finset.mem_subtype.2 hxA),
      fun hxB ↦ hi.2 (Finset.mem_subtype.2 hxB)⟩
  · intro x
    by_cases hxG : x ∈ V(G)
    · refine (card_le_card fun i hi ↦ ?_).trans (hPv ⟨x, hxG⟩)
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact ((P i).mem_support_toGraphWalk_iff.1 hi).2
    · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ hi ↦
        hxG ((P i).mem_support_toGraphWalk_iff.1 hi).1)]
      exact Nat.zero_le _
  · intro x hxA y hyB
    exact not_reachable_deleteVerts_map_subtype
      (hX _ (Finset.mem_subtype.2 hxA : (⟨x, hA hxA⟩ : V(G)) ∈ A')
        _ (Finset.mem_subtype.2 hyB : (⟨y, hB hyB⟩ : V(G)) ∈ B'))
  · simpa [sum_map] using hk

/-! ### Vertex-disjoint paths -/

/-- **Weak duality for vertex-disjoint set-to-set walks.** A family of pairwise vertex-disjoint
walks, each from a vertex of `A` to a vertex of `B`, has at most `#X` members whenever deleting
`X` destroys reachability from every vertex of `A` to every vertex of `B`. -/
theorem card_le_card_of_forall_not_reachable_deleteVerts {A B : Finset α}
    (hA : (A : Set α) ⊆ V(G)) {ι : Type*} [Fintype ι] {a b : ι → α}
    {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hP : Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) {X : Finset α}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteVerts X).Reachable a b) :
    Fintype.card ι ≤ #X := by
  classical
  refine (card_le_sum_of_forall_not_reachable_deleteVerts (P := P) hA ha hb (c := 1)
    (fun x ↦ ?_) hX).trans_eq (by simp)
  refine card_le_one.2 fun i hi j hj ↦ ?_
  by_contra hij
  simp only [mem_filter, mem_univ, true_and] at hi hj
  exact hP hij hi hj

/-- **Menger's theorem for vertex-disjoint paths between vertex sets in a multigraph.** Let `A`
and `B` be finite sets of actual vertices of a multigraph with finitely many actual vertices.
Some family of `k` pairwise vertex-disjoint paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with
its other vertices in neither terminal set, and some set `X` of `k` actual vertices whose deletion
destroys all `A`–`B` reachability exist. -/
theorem exists_paths_setSeparator_card_eq [Finite V(G)] (A B : Finset α)
    (hA : (A : Set α) ⊆ V(G)) (hB : (B : Set α) ⊆ V(G)) :
    ∃ (k : ℕ) (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)) (X : Finset α),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ x ∈ (P i).support, x ≠ a i → x ≠ b i → x ∉ A ∧ x ∉ B) ∧
      (Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) ∧
      (X : Set α) ⊆ V(G) ∧ (∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteVerts X).Reachable a b) ∧ #X = k := by
  classical
  obtain ⟨k, a, b, P, X, ha, hb, hpath, hint, hPv, hXV, hX, hk⟩ :=
    exists_paths_setSeparator_sum_eq (G := G) 1 A B hA hB
  refine ⟨k, a, b, P, X, ha, hb, hpath, hint, fun i j hij x hxi hxj ↦ ?_, hXV, hX,
    by simpa using hk⟩
  have htwo : 1 < #{l | x ∈ (P l).support} :=
    one_lt_card.2 ⟨i, by simpa using hxi, j, by simpa using hxj, hij⟩
  exact (hPv x).not_gt htwo

/-- **Menger's theorem for vertex-disjoint paths between vertex sets in a multigraph, predicate
form.** Let `A` and `B` be finite sets of actual vertices of a multigraph with finitely many actual
vertices. Deleting any set of fewer than `k` vertices leaves some vertex of `B` reachable from
some vertex of `A` exactly when there are `k` pairwise vertex-disjoint `A`–`B` paths whose
interiors avoid both terminal sets. -/
theorem forall_exists_reachable_deleteVerts_iff_exists_paths [Finite V(G)] (A B : Finset α)
    (hA : (A : Set α) ⊆ V(G)) (hB : (B : Set α) ⊆ V(G)) (k : ℕ) :
    (∀ X : Finset α, #X < k → ∃ a ∈ A, ∃ b ∈ B, (G.deleteVerts X).Reachable a b) ↔
      ∃ (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ x ∈ (P i).support, x ≠ a i → x ≠ b i → x ∉ A ∧ x ∉ B) ∧
        Pairwise fun i j ↦ (P i).support.Disjoint (P j).support := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, P, ha, hb, _, _, hP⟩ X hX ↦ ?_⟩
  · obtain ⟨m, a, b, P, X, ha, hb, hpath, hint, hdisj, -, hX, hXm⟩ :=
      exists_paths_setSeparator_card_eq (G := G) A B hA hB
    have hkm : k ≤ m := hXm ▸ not_lt.1 fun hlt ↦
      let ⟨a, ha, b, hb, hab⟩ := h X hlt
      hX a ha b hb hab
    exact ⟨fun i ↦ a (Fin.castLE hkm i), fun i ↦ b (Fin.castLE hkm i),
      fun i ↦ P (Fin.castLE hkm i), fun i ↦ ha _, fun i ↦ hb _, fun i ↦ hpath _,
      fun i ↦ hint _, fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    push Not at h
    exact hX.not_ge (by simpa using
      card_le_card_of_forall_not_reachable_deleteVerts hA ha hb hP h)

end Graph
