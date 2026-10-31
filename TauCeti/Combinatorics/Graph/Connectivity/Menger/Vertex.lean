/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Network.Menger.Vertex
public import Mathlib.Data.Set.Card

/-!
# Menger's theorem for vertex-disjoint paths in multigraphs

Let `G : Graph α β` be a multigraph and let `s ≠ t` be points that no edge of `G` joins. Two walks
of `G` from `s` to `t` are *internally disjoint* when they share no vertex other than `s` and `t`.
A *vertex separator* is a set `X` of actual vertices, avoiding `s` and `t`, such that `s` and `t`
are not reachable in `G.deleteVerts X`. With a capacity `c v : ℕ` on every vertex, a *packing* is a
finite indexed family of `s`–`t` paths, repetitions allowed, in which every vertex `v` other than
`s` and `t` lies on at most `c v` members, and the weight of a vertex separator `X` is
`∑ v ∈ X, c v`.

This file proves the local vertex form of Menger's theorem for multigraphs with finitely many
actual vertices: the largest number of pairwise internally disjoint `s`–`t` paths equals the least
size of a vertex separator. More generally, the largest packing has as many members as the least
weight of a vertex separator. The edge set may be infinite: loops and parallel edges change
neither side, since the statements concern only the vertices that walks visit. Weak duality needs
no finiteness: each member of a packing visits a vertex of the separator other than `s` and `t`.
Without the hypothesis that no edge joins `s` and `t`, no vertex separator exists, and a single
edge from `s` to `t` could be repeated arbitrarily often in a packing.

## Main definitions

* `Graph.Walk.InternallyDisjoint`: two walks from `s` to `t` sharing no vertex other than `s` and
  `t`.

## Main results

* `Graph.card_le_sum_of_not_reachable_deleteVerts`: **weak duality** for vertex-capacitated
  packings.
* `Graph.exists_paths_vertexSeparator_sum_eq`: **vertex-capacitated Menger's theorem**, a packing
  and a vertex separator of equal size and weight.
* `Graph.card_le_encard_of_not_reachable_deleteVerts`: weak duality for families of pairwise
  internally disjoint walks.
* `Graph.exists_paths_vertexSeparator_card_eq`: **Menger's theorem** for internally
  vertex-disjoint paths in a multigraph, in witness form.
* `Graph.forall_reachable_deleteVerts_iff_exists_paths`: its predicate form: `s` and `t` stay
  reachable after deleting any fewer than `k` vertices other than `s` and `t` exactly when there
  are `k` pairwise internally disjoint `s`–`t` paths.

## Implementation notes

Attainment is transported from the corresponding theorems for directed walks of an arrow family
(`TauCeti.exists_paths_vertexSeparator_sum_eq` and `TauCeti.exists_paths_vertexSeparator_card_eq`)
applied to the bidirected arrow family `Graph.BidirectedHom G` on the actual vertices of `G`. Its
directed walks are the walks of `G` with the same vertex sequences
(`Graph.Walk.bidirectedEquiv`), it has no arrow from `s` to `t` exactly when no edge joins them, and
reachability avoiding a vertex set is reachability after deleting it
(`Graph.reachableAvoiding_bidirectedHom_iff`). The directed theorems allow infinite arrow types,
so no finiteness of the edge set is needed.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

open Finset TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : α}

/-! ### Internally disjoint walks -/

namespace Walk

variable {p q : G.Walk s t}

/-- Two walks from `s` to `t` are *internally disjoint* when they share no vertex other than `s`
and `t`. -/
def InternallyDisjoint (p q : G.Walk s t) : Prop :=
  ∀ v ∈ p.support, v ∈ q.support → v = s ∨ v = t

theorem internallyDisjoint_def :
    p.InternallyDisjoint q ↔ ∀ v ∈ p.support, v ∈ q.support → v = s ∨ v = t :=
  Iff.rfl

theorem InternallyDisjoint.symm (h : p.InternallyDisjoint q) : q.InternallyDisjoint p :=
  fun v hq hp ↦ h v hp hq

theorem internallyDisjoint_comm : p.InternallyDisjoint q ↔ q.InternallyDisjoint p :=
  ⟨.symm, .symm⟩

end Walk

end Graph

namespace TauCeti.ArrowWalk

open Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : V(G)}

@[simp]
theorem internallyDisjoint_toGraphWalk_iff {p q : ArrowWalk G.BidirectedHom s t} :
    p.toGraphWalk.InternallyDisjoint q.toGraphWalk ↔ p.InternallyDisjoint q := by
  rw [Walk.internallyDisjoint_def, internallyDisjoint_def]
  refine ⟨fun h v hp hq ↦ ?_, fun h v hp hq ↦ ?_⟩
  · exact (h v ((mem_support_toGraphWalk_iff _).2 ⟨v.2, hp⟩)
      ((mem_support_toGraphWalk_iff _).2 ⟨v.2, hq⟩)).imp Subtype.ext Subtype.ext
  · obtain ⟨hv, hp'⟩ := (mem_support_toGraphWalk_iff _).1 hp
    obtain ⟨_, hq'⟩ := (mem_support_toGraphWalk_iff _).1 hq
    exact (h ⟨v, hv⟩ hp' hq').imp (congrArg Subtype.val) (congrArg Subtype.val)

end TauCeti.ArrowWalk

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : α}

/-- Points reachable after deleting some vertices are actual vertices of `G`. -/
private theorem mem_vertexSet_of_reachable_deleteVerts {X : Set α}
    (h : (G.deleteVerts X).Reachable s t) : s ∈ V(G) ∧ t ∈ V(G) :=
  ⟨(h.mono deleteVerts_le).left_mem, (h.mono deleteVerts_le).right_mem⟩

/-- No arrow of the bidirected arrow family runs between vertices that no edge joins. -/
private theorem isEmpty_bidirectedHom (hadj : ¬G.Adj s t) (hs : s ∈ V(G)) (ht : t ∈ V(G)) :
    IsEmpty (G.BidirectedHom ⟨s, hs⟩ ⟨t, ht⟩) :=
  ⟨fun e ↦ hadj ⟨e.1, e.2⟩⟩

/-- A set of actual vertices that the bidirected arrow family cannot avoid on its way from `x` to
`y` separates `x` from `y` in `G`. -/
private theorem not_reachable_deleteVerts_map_subtype {X : Finset V(G)} {x y : V(G)}
    (h : ¬ReachableAvoiding G.BidirectedHom (X : Set V(G)) x y) :
    ¬(G.deleteVerts (X.map (Function.Embedding.subtype _) : Set α)).Reachable x y := by
  rwa [← reachableAvoiding_bidirectedHom_iff, coe_map, Function.Embedding.coe_subtype,
    Set.preimage_image_eq _ Subtype.val_injective]

/-! ### Weak duality -/

/-- **Weak duality for vertex-capacitated packings.** A family of `s`–`t` walks, from an actual
vertex `s`, in which every vertex `v` other than `s` and `t` lies on at most `c v` members has at
most `∑ v ∈ X, c v` members, for every set `X` of vertices avoiding `s` and `t` whose deletion
leaves `s` and `t` unreachable. -/
theorem card_le_sum_of_not_reachable_deleteVerts [DecidableEq α] {ι : Type*} [Fintype ι]
    {P : ι → G.Walk s t} {c : α → ℕ} (hP : ∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).support} ≤ c v)
    (hs : s ∈ V(G)) {X : Finset α} (hsX : s ∉ X) (htX : t ∉ X)
    (hX : ¬(G.deleteVerts X).Reachable s t) :
    Fintype.card ι ≤ ∑ v ∈ X, c v := by
  -- Each member visits a vertex of `X`, and the vertex `v` of `X` is visited by at most `c v`
  -- members.
  have h (i : ι) : ∃ v ∈ (P i).support, v ∈ X := by
    by_contra! h
    exact hX (reachable_deleteVerts_iff_exists_walk.2 ⟨P i, hs, h⟩)
  choose g hg hgX using h
  rw [← card_univ, card_eq_sum_card_fiberwise fun i _ ↦ hgX i]
  refine sum_le_sum fun v hv ↦ (card_le_card fun i hi ↦ ?_).trans
    (hP v (ne_of_mem_of_not_mem hv hsX) (ne_of_mem_of_not_mem hv htX))
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi ▸ hg i

/-- **Weak duality for internally vertex-disjoint walks.** A family of `s`–`t` walks, from an
actual vertex `s`, pairwise sharing no vertex other than `s` and `t` has at most as many members as
any set of vertices avoiding `s` and `t` whose deletion leaves `s` and `t` unreachable. -/
theorem card_le_encard_of_not_reachable_deleteVerts {ι : Type*} {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) (hs : s ∈ V(G)) {X : Set α}
    (hsX : s ∉ X) (htX : t ∉ X) (hX : ¬(G.deleteVerts X).Reachable s t) :
    ENat.card ι ≤ X.encard := by
  -- Each member visits a vertex of `X`, necessarily other than `s` and `t`, and different
  -- members visit different such vertices.
  have h (i : ι) : ∃ v ∈ (P i).support, v ∈ X := by
    by_contra! h
    exact hX (reachable_deleteVerts_iff_exists_walk.2 ⟨P i, hs, h⟩)
  choose g hg hgX using h
  have hinj : Function.Injective g := fun i j hij ↦ by
    by_contra hne
    rcases hP hne (g i) (hg i) (hij ▸ hg j) with h | h
    exacts [hsX (h ▸ hgX i), htX (h ▸ hgX i)]
  rw [← hinj.encard_range]
  exact Set.encard_le_encard (Set.range_subset_iff.2 hgX)

/-! ### Attainment -/

/-- **Vertex-capacitated Menger's theorem for multigraphs.** Let `s ≠ t` be points of a multigraph
with finitely many actual vertices, joined by no edge, and let `c v` be a capacity on every vertex.
Some family of `k` paths from `s` to `t`, in which every vertex `v` other than `s` and `t` lies on
at most `c v` members, and some set `X` of actual vertices avoiding `s` and `t`, whose deletion
leaves `s` and `t` unreachable, satisfy `∑ v ∈ X, c v = k`. By
`Graph.card_le_sum_of_not_reachable_deleteVerts`, the family is then largest and the separator of
least weight. -/
theorem exists_paths_vertexSeparator_sum_eq [Finite V(G)] [DecidableEq α] (c : α → ℕ)
    (hst : s ≠ t) (hadj : ¬G.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (X : Finset α), (∀ i, (P i).IsPath) ∧
      (∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).support} ≤ c v) ∧ (X : Set α) ⊆ V(G) ∧
      s ∉ X ∧ t ∉ X ∧ ¬(G.deleteVerts X).Reachable s t ∧ ∑ v ∈ X, c v = k := by
  -- Unless both points are actual vertices, they are not even reachable.
  by_cases hst' : s ∈ V(G) ∧ t ∈ V(G)
  swap
  · exact ⟨0, Fin.elim0, ∅, fun i ↦ i.elim0, by simp, by simp, by simp, by simp,
      fun h ↦ hst' (mem_vertexSet_of_reachable_deleteVerts h), by simp⟩
  obtain ⟨hs, ht⟩ := hst'
  obtain ⟨k, P, X, hP, hPv, hsX, htX, hX, hk⟩ :=
    TauCeti.exists_paths_vertexSeparator_sum_eq (Q := G.BidirectedHom) (s := ⟨s, hs⟩)
      (t := ⟨t, ht⟩) (fun v ↦ c v) (fun h ↦ hst (congrArg Subtype.val h))
      (isEmpty_bidirectedHom hadj hs ht)
  refine ⟨k, fun i ↦ (P i).toGraphWalk, X.map (Function.Embedding.subtype _),
    fun i ↦ (P i).isPath_toGraphWalk_iff.2 (hP i), fun v hvs hvt ↦ ?_, map_subtype_subset X,
    by simp [hsX], by simp [htX], not_reachable_deleteVerts_map_subtype hX, by rwa [sum_map]⟩
  · -- A point visited by some member is an actual vertex, where the directed count applies.
    by_cases hv : v ∈ V(G)
    · refine (card_le_card fun i hi ↦ ?_).trans
        (hPv ⟨v, hv⟩ (fun h ↦ hvs (congrArg Subtype.val h)) fun h ↦ hvt (congrArg Subtype.val h))
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact ((P i).mem_support_toGraphWalk_iff.1 hi).2
    · refine (card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ h ↦ ?_)).trans_le (Nat.zero_le _)
      exact hv ((P i).mem_support_toGraphWalk_iff.1 h).1

/-- **Menger's theorem for internally vertex-disjoint paths in a multigraph.** Let `s ≠ t` be
points of a multigraph with finitely many actual vertices, joined by no edge. Some family of `k`
distinct paths from `s` to `t`, pairwise sharing no vertex other than `s` and `t`, and some set of
`k` actual vertices avoiding `s` and `t`, whose deletion leaves `s` and `t` unreachable, exist. By
`Graph.card_le_encard_of_not_reachable_deleteVerts`, the family is then largest and the separator
smallest. -/
theorem exists_paths_vertexSeparator_card_eq [Finite V(G)] (hst : s ≠ t) (hadj : ¬G.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (X : Finset α), Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧ (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      (X : Set α) ⊆ V(G) ∧ s ∉ X ∧ t ∉ X ∧ ¬(G.deleteVerts X).Reachable s t ∧ #X = k := by
  -- Unless both points are actual vertices, they are not even reachable.
  by_cases hst' : s ∈ V(G) ∧ t ∈ V(G)
  swap
  · exact ⟨0, Fin.elim0, ∅, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, by simp, by simp,
      by simp, fun h ↦ hst' (mem_vertexSet_of_reachable_deleteVerts h), by simp⟩
  obtain ⟨hs, ht⟩ := hst'
  obtain ⟨k, P, X, hinj, hP, hdisj, hsX, htX, hX, hk⟩ :=
    TauCeti.exists_paths_vertexSeparator_card_eq (Q := G.BidirectedHom) (s := ⟨s, hs⟩)
      (t := ⟨t, ht⟩) (fun h ↦ hst (congrArg Subtype.val h)) (isEmpty_bidirectedHom hadj hs ht)
  exact ⟨k, fun i ↦ (P i).toGraphWalk, X.map (Function.Embedding.subtype _),
    ArrowWalk.toGraphWalk_injective.comp hinj, fun i ↦ (P i).isPath_toGraphWalk_iff.2 (hP i),
    fun _ _ hij ↦ by simpa using hdisj hij, map_subtype_subset X, by simp [hsX], by simp [htX],
    not_reachable_deleteVerts_map_subtype hX, by rwa [card_map]⟩

/-- **Menger's theorem for internally vertex-disjoint paths in a multigraph, predicate form.** Let
`s ≠ t` be points of a multigraph with finitely many actual vertices, joined by no edge. Then `s`
and `t` stay reachable after deleting any fewer than `k` vertices other than `s` and `t` exactly
when there are `k` paths from `s` to `t` pairwise sharing no vertex other than `s` and `t`. -/
theorem forall_reachable_deleteVerts_iff_exists_paths [Finite V(G)] (hst : s ≠ t)
    (hadj : ¬G.Adj s t) (k : ℕ) :
    (∀ X : Finset α, s ∉ X → t ∉ X → #X < k → (G.deleteVerts X).Reachable s t) ↔
      ∃ P : Fin k → G.Walk s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ X hsX htX hX ↦ ?_⟩
  · obtain ⟨m, P, X, -, hP, hdisj, -, hsX, htX, hX, hXm⟩ :=
      exists_paths_vertexSeparator_card_eq hst hadj
    have hkm : k ≤ m := hXm ▸ not_lt.1 fun hlt ↦ hX (h X hsX htX hlt)
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    -- Some member exists, and as `s ≠ t` it has positive length, so `s` is an actual vertex.
    have hs : s ∈ V(G) := (P ⟨0, by omega⟩).support_subset_vertexSet_of_pos
      (Nat.pos_of_ne_zero fun h ↦ hst (Walk.eq_of_length_eq_zero h)) s (Walk.start_mem_support _)
    have := card_le_encard_of_not_reachable_deleteVerts hP hs hsX htX h
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin, Set.encard_coe_eq_coe_finsetCard,
      Nat.cast_le] at this
    omega

end Graph
