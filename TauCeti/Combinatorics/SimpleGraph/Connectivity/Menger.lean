/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Menger.SetToSet
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.ArrowWalk

/-!
# Menger's theorem for vertex-disjoint paths in simple graphs

Let `G` be a simple graph on a finite vertex type `V`. This file proves the vertex forms of
Menger's theorem for `G`, with path witnesses in `SimpleGraph.Walk` and separators given by
deleting vertices.

* **Local form.** For distinct nonadjacent vertices `s` and `t`, the largest number of `s`–`t`
  paths pairwise sharing no vertex other than `s` and `t` equals the least number of vertices,
  other than `s` and `t`, whose deletion separates `s` from `t`. Deletion of a set `X` of vertices
  is expressed through the subgraph `G.induce (↑X)ᶜ` induced on the remaining vertices.
* **Adjacent vertices.** No set of vertices other than `s` and `t` separates adjacent vertices `s`
  and `t`, so the edge `s(s, t)` is deleted as well and counted separately: for some `k`, there are
  `k + 1` such paths, one of them the edge itself, and `k` vertices whose deletion together with
  that of the edge separates `s` from `t`.
* **Vertex-capacitated form.** With a capacity `c v : ℕ` on every vertex, a *packing* is a family of
  `s`–`t` paths, repetitions allowed, in which every vertex `v` other than `s` and `t` lies on at
  most `c v` members. The largest packing has as many members as the least weight
  `∑ v ∈ X, c v` of a separator `X`.
* **Set-to-set form.** For vertex sets `A` and `B`, possibly overlapping, an *`A`–`B` path* runs
  from a vertex of `A` to a vertex of `B` and has no other vertex in `A` or `B`. The largest number
  of pairwise vertex-disjoint `A`–`B` paths equals the least number of vertices meeting every walk
  from a vertex of `A` to a vertex of `B`; such a separator may meet `A` and `B`, and a vertex of
  `A ∩ B` is a path of length zero. The vertex-capacitated version counts every vertex, endpoints
  included, against its capacity.

Each form comes with weak duality, which needs no finiteness, and a witness form giving a path
family and a separator of equal size. The local form for nonadjacent vertices and the set-to-set
form also have predicate forms.

## Main definitions

* `SimpleGraph.Walk.InternallyDisjoint`: two walks from `s` to `t` sharing no vertex other than `s`
  and `t`.

## Main results

* `SimpleGraph.card_le_card_of_not_reachable_induce`: weak duality for internally disjoint walks.
* `SimpleGraph.exists_paths_vertexSeparator_card_eq`: **Menger's theorem** for internally
  vertex-disjoint paths, in witness form.
* `SimpleGraph.forall_reachable_induce_iff_exists_paths`: its predicate form: `t` stays reachable
  from `s` after deleting any fewer than `k` vertices other than `s` and `t` exactly when there are
  `k` internally vertex-disjoint `s`–`t` paths.
* `SimpleGraph.card_le_card_add_one_of_not_reachable_induce_deleteEdges` and
  `SimpleGraph.exists_paths_vertexSeparator_card_add_one_eq`: the form for adjacent vertices.
* `SimpleGraph.card_le_sum_of_not_reachable_induce` and
  `SimpleGraph.exists_paths_vertexSeparator_sum_eq`: the vertex-capacitated form.
* `SimpleGraph.card_le_card_of_forall_exists_mem_support`,
  `SimpleGraph.exists_paths_setSeparator_card_eq` and
  `SimpleGraph.forall_exists_walk_iff_exists_paths`: the set-to-set form.
* `SimpleGraph.card_le_sum_of_forall_exists_mem_support` and
  `SimpleGraph.exists_paths_setSeparator_sum_eq`: the vertex-capacitated set-to-set form.

## Implementation notes

Apart from the form for adjacent vertices, every statement is transported from the corresponding
theorem for directed walks of an arrow family (`TauCeti.exists_paths_vertexSeparator_card_eq` and
its companions) applied to the adjacency arrow family `SimpleGraph.AdjHom G`. Its directed walks
are the walks of `G` with the same vertex sequences (`SimpleGraph.Walk.arrowWalkEquiv`), and
reachability after deleting `X` is reachability avoiding `X`
(`SimpleGraph.reachable_induce_compl_iff`). The form for adjacent vertices applies the nonadjacent
form to the graph `G.deleteEdges {s(s, t)}`; a path from `s` to `t` traversing the edge `s(s, t)`
is that edge (`SimpleGraph.Walk.IsPath.eq_adj_toWalk_of_mem_edges`).

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 3.3.
-/

public section

open Finset TauCeti

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-! ### Internally disjoint walks -/

namespace Walk

variable {s t : V} {p q : G.Walk s t}

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

@[simp]
theorem internallyDisjoint_toArrowWalk_iff :
    p.toArrowWalk.InternallyDisjoint q.toArrowWalk ↔ p.InternallyDisjoint q := by
  simp [ArrowWalk.internallyDisjoint_def, internallyDisjoint_def]

end Walk

end SimpleGraph

namespace TauCeti.ArrowWalk

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {s t : V} {p q : ArrowWalk G.AdjHom s t}

@[simp]
theorem internallyDisjoint_toWalk_iff :
    p.toWalk.InternallyDisjoint q.toWalk ↔ p.InternallyDisjoint q := by
  simp [internallyDisjoint_def, Walk.internallyDisjoint_def]

end TauCeti.ArrowWalk

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-! ### Paths between two vertices -/

section Local

variable {s t : V}

/-- **Weak duality for vertex-capacitated packings.** A family of `s`–`t` walks in which every
vertex `v` other than `s` and `t` lies on at most `c v` members has at most `∑ v ∈ X, c v`
members, for every set `X` of vertices other than `s` and `t` whose deletion separates `s` from
`t`. -/
theorem card_le_sum_of_not_reachable_induce [DecidableEq V] {ι : Type*} [Fintype ι]
    {P : ι → G.Walk s t} {c : V → ℕ} (hP : ∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).support} ≤ c v)
    {X : Finset V} (hs : s ∉ X) (ht : t ∉ X)
    (hX : ¬(G.induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩) :
    Fintype.card ι ≤ ∑ v ∈ X, c v :=
  card_le_sum_of_not_reachableAvoiding (P := fun i ↦ (P i).toArrowWalk) (by simpa using hP) hs ht
    fun h ↦ hX (reachable_induce_compl_iff.2 h)

/-- **Vertex-capacitated Menger's theorem.** Let `s` and `t` be distinct nonadjacent vertices of a
simple graph on a finite vertex type, and let `c v` be a capacity on every vertex. Some family of
`k` paths from `s` to `t`, in which every vertex `v` other than `s` and `t` lies on at most `c v`
members, and some set `X` of vertices other than `s` and `t`, whose deletion separates `s` from
`t`, satisfy `∑ v ∈ X, c v = k`. By `SimpleGraph.card_le_sum_of_not_reachable_induce`, the family is
then largest and the separator of least weight. -/
theorem exists_paths_vertexSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ) (hst : s ≠ t)
    (hadj : ¬G.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (X : Finset V), (∀ i, (P i).IsPath) ∧
      (∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).support} ≤ c v) ∧
      ∃ (hs : s ∉ X) (ht : t ∉ X), ¬(G.induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩ ∧
        ∑ v ∈ X, c v = k := by
  obtain ⟨k, P, X, hP, hPv, hs, ht, hX, hk⟩ :=
    _root_.TauCeti.exists_paths_vertexSeparator_sum_eq (Q := G.AdjHom) c hst
      (isEmpty_plift.2 (isEmpty_Prop.2 hadj))
  exact ⟨k, fun i ↦ (P i).toWalk, X, fun i ↦ by simpa using hP i, by simpa using hPv, hs, ht,
    fun h ↦ hX (reachable_induce_compl_iff.1 h), hk⟩

/-- **Weak duality for internally vertex-disjoint walks.** A family of `s`–`t` walks pairwise
sharing no vertex other than `s` and `t` has at most `#X` members, for every set `X` of vertices
other than `s` and `t` whose deletion separates `s` from `t`. -/
theorem card_le_card_of_not_reachable_induce {ι : Type*} [Fintype ι] {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) {X : Finset V} (hs : s ∉ X)
    (ht : t ∉ X) (hX : ¬(G.induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩) :
    Fintype.card ι ≤ #X :=
  card_le_card_of_not_reachableAvoiding (P := fun i ↦ (P i).toArrowWalk)
    (fun _ _ hij ↦ by simpa using hP hij) hs ht fun h ↦ hX (reachable_induce_compl_iff.2 h)

/-- **Menger's theorem for internally vertex-disjoint paths.** Let `s` and `t` be distinct
nonadjacent vertices of a simple graph on a finite vertex type. Some family of `k` distinct paths
from `s` to `t`, pairwise sharing no vertex other than `s` and `t`, and some set of `k` vertices
other than `s` and `t`, whose deletion separates `s` from `t`, exist. By
`SimpleGraph.card_le_card_of_not_reachable_induce`, the family is then largest and the separator
smallest. -/
theorem exists_paths_vertexSeparator_card_eq [Finite V] (hst : s ≠ t) (hadj : ¬G.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (X : Finset V), Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧ (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      ∃ (hs : s ∉ X) (ht : t ∉ X), ¬(G.induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩ ∧
        #X = k := by
  obtain ⟨k, P, X, hinj, hP, hdisj, hs, ht, hX, hk⟩ :=
    _root_.TauCeti.exists_paths_vertexSeparator_card_eq (Q := G.AdjHom) hst
      (isEmpty_plift.2 (isEmpty_Prop.2 hadj))
  exact ⟨k, fun i ↦ (P i).toWalk, X, ArrowWalk.toWalk_injective.comp hinj,
    fun i ↦ by simpa using hP i, fun _ _ hij ↦ by simpa using hdisj hij, hs, ht,
    fun h ↦ hX (reachable_induce_compl_iff.1 h), hk⟩

/-- **Menger's theorem for internally vertex-disjoint paths, predicate form.** Let `s` and `t` be
distinct nonadjacent vertices of a simple graph on a finite vertex type. Then `t` stays reachable
from `s` after deleting any fewer than `k` vertices other than `s` and `t` exactly when there are
`k` paths from `s` to `t` pairwise sharing no vertex other than `s` and `t`. -/
theorem forall_reachable_induce_iff_exists_paths [Finite V] (hst : s ≠ t) (hadj : ¬G.Adj s t)
    (k : ℕ) :
    (∀ (X : Finset V) (hs : s ∉ X) (ht : t ∉ X), #X < k →
        (G.induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩) ↔
      ∃ P : Fin k → G.Walk s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ X hs ht hX ↦ ?_⟩
  · obtain ⟨P, hP, hdisj⟩ := (forall_reachableAvoiding_iff_exists_paths (Q := G.AdjHom) hst
      (isEmpty_plift.2 (isEmpty_Prop.2 hadj)) k).1 fun X hs ht hX ↦
        reachable_induce_compl_iff.1 (h X hs ht hX)
    exact ⟨fun i ↦ (P i).toWalk, fun i ↦ by simpa using hP i,
      fun _ _ hij ↦ by simpa using hdisj hij⟩
  · by_contra h
    exact hX.not_ge (by simpa using card_le_card_of_not_reachable_induce hP hs ht h)

/-- A walk between distinct nonadjacent vertices visits a vertex other than its endpoints. -/
theorem Walk.exists_mem_support_ne_ne (hst : s ≠ t) (hadj : ¬G.Adj s t) (p : G.Walk s t) :
    ∃ v ∈ p.support, v ≠ s ∧ v ≠ t := by
  cases p with
  | nil => exact absurd rfl hst
  | @cons _ x _ h p => exact ⟨x, by simp, h.ne.symm, fun hxt ↦ hadj (hxt ▸ h)⟩

/-! ### Paths between adjacent vertices -/

/-- **Weak duality for internally vertex-disjoint paths between possibly adjacent vertices.** Let
`X` be a set of vertices other than `s` and `t` whose deletion, together with that of the edge
`s(s, t)`, separates `s` from `t`. A family of distinct paths from `s` to `t`, pairwise sharing no
vertex other than `s` and `t`, has at most `#X + 1` members. -/
theorem card_le_card_add_one_of_not_reachable_induce_deleteEdges {ι : Type*} [Fintype ι]
    {P : ι → G.Walk s t} (hinj : Function.Injective P) (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) {X : Finset V} (hs : s ∉ X)
    (ht : t ∉ X)
    (hX : ¬((G.deleteEdges {s(s, t)}).induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩) :
    Fintype.card ι ≤ #X + 1 := by
  classical
  let q (i : ι) : Prop := s(s, t) ∉ (P i).edges
  -- The members avoiding the edge `s(s, t)` are walks after its deletion.
  have h₁ : Fintype.card {i // q i} ≤ #X :=
    card_le_card_of_not_reachable_induce (G := G.deleteEdges {s(s, t)})
      (P := fun i ↦ (P i.1).toDeleteEdges {s(s, t)} fun e he hes ↦ i.2 (by simp_all))
      (fun i j hij ↦ by
        simpa [Walk.internallyDisjoint_def] using hdisj (Subtype.coe_ne_coe.2 hij)) hs ht hX
  -- A member traversing the edge `s(s, t)` is the path consisting of that edge.
  have h₂ : Fintype.card {i // ¬q i} ≤ 1 :=
    Fintype.card_le_one_iff.2 fun i j ↦ Subtype.ext <| hinj <|
      ((hP i).eq_adj_toWalk_of_mem_edges (not_not.1 i.2)).trans
        ((hP j).eq_adj_toWalk_of_mem_edges (not_not.1 j.2)).symm
  rw [Fintype.card_congr (Equiv.sumCompl q).symm, Fintype.card_sum]
  omega

/-- **Menger's theorem for internally vertex-disjoint paths between adjacent vertices.** Let `s` and
`t` be adjacent vertices of a simple graph on a finite vertex type. For some `k`, there are a
family of `k + 1` distinct paths from `s` to `t`, pairwise sharing no vertex other than `s` and
`t`, whose last member is the path consisting of the edge `s(s, t)`, and a set of `k` vertices
other than `s` and `t` whose deletion, together with that of the edge `s(s, t)`, separates `s` from
`t`. By `SimpleGraph.card_le_card_add_one_of_not_reachable_induce_deleteEdges`, the family is then
largest and the separator smallest. -/
theorem exists_paths_vertexSeparator_card_add_one_eq [Finite V] (h : G.Adj s t) :
    ∃ (k : ℕ) (P : Fin (k + 1) → G.Walk s t) (X : Finset V), Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧ (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      P (Fin.last k) = h.toWalk ∧
      ∃ (hs : s ∉ X) (ht : t ∉ X),
        ¬((G.deleteEdges {s(s, t)}).induce (X : Set V)ᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩ ∧ #X = k := by
  have hadj : ¬(G.deleteEdges {s(s, t)}).Adj s t := by simp
  obtain ⟨k, P, X, -, hP, hdisj, hs, ht, hX, hk⟩ := exists_paths_vertexSeparator_card_eq h.ne hadj
  -- Append the edge `s(s, t)` to the family, after returning its members to `G`.
  let P' : Fin (k + 1) → G.Walk s t :=
    Fin.lastCases h.toWalk fun i ↦ (P i).mapLe (G.deleteEdges_le _)
  have hP'l : P' (Fin.last k) = h.toWalk := Fin.lastCases_last ..
  have hP'c (i : Fin k) : (P' i.castSucc).support = (P i).support := by
    simp [P']
  -- Every member other than the edge visits a vertex other than `s` and `t`.
  have hint {i : Fin (k + 1)} (hi : i ≠ Fin.last k) : ∃ v ∈ (P' i).support, v ≠ s ∧ v ≠ t := by
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    exact hP'c i ▸ (P i).exists_mem_support_ne_ne h.ne hadj
  have hdisj' : Pairwise fun i j ↦ (P' i).InternallyDisjoint (P' j) := by
    intro i j hij v hvi hvj
    induction i using Fin.lastCases with
    | last => simpa [hP'l] using hvi
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [hP'l] using hvj
      | cast j =>
        rw [hP'c] at hvi hvj
        exact hdisj (fun hij' ↦ hij (congrArg _ hij')) v hvi hvj
  refine ⟨k, P', X, fun i j hij ↦ ?_, fun i ↦ ?_, hdisj', hP'l, hs, ht, hX, hk⟩
  · by_contra hne
    obtain ⟨v, hv, hvs, hvt⟩ : ∃ v ∈ (P' i).support, v ≠ s ∧ v ≠ t := by
      by_cases hi : i = Fin.last k
      · exact hij ▸ hint (hi ▸ Ne.symm hne)
      · exact hint hi
    exact (hdisj' hne v hv (hij ▸ hv)).elim hvs hvt
  · induction i using Fin.lastCases with
    | last => exact hP'l ▸ h.isPath_toWalk
    | cast i => simpa [P'] using hP i

end Local

/-! ### Paths between two vertex sets -/

section SetToSet

/-- A set `X` of vertices meets every walk of `G` from `a` to `b` exactly when `b` is not reachable
from `a` along the adjacency arrow family avoiding `X`. -/
private theorem forall_exists_mem_support_iff {X : Set V} {a b : V} :
    (∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X) ↔ ¬ReachableAvoiding G.AdjHom X a b := by
  simp [reachableAvoiding_adjHom_iff]

/-- **Weak duality for vertex-capacitated set-to-set packings.** A family of walks, each from a
vertex of `A` to a vertex of `B`, in which every vertex `v` lies on at most `c v` members, has at
most `∑ v ∈ X, c v` members, for every set `X` of vertices meeting every walk from a vertex of `A`
to a vertex of `B`. -/
theorem card_le_sum_of_forall_exists_mem_support [DecidableEq V] {A B : Finset V} {ι : Type*}
    [Fintype ι] {a b : ι → V} {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A)
    (hb : ∀ i, b i ∈ B) {c : V → ℕ} (hP : ∀ v, #{i | v ∈ (P i).support} ≤ c v) {X : Finset V}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X) :
    Fintype.card ι ≤ ∑ v ∈ X, c v :=
  card_le_sum_of_forall_not_reachableAvoiding (P := fun i ↦ (P i).toArrowWalk) ha hb
    (by simpa using hP) fun a ha b hb ↦ forall_exists_mem_support_iff.1 (hX a ha b hb)

/-- **Vertex-capacitated Menger's theorem between vertex sets.** Let `A` and `B` be sets of vertices
of a simple graph on a finite vertex type, and let `c v` be a capacity on every vertex. Some family
of `k` paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with its other vertices in neither `A` nor
`B`, in which every vertex `v` lies on at most `c v` members, and some set `X` of vertices meeting
every walk from a vertex of `A` to a vertex of `B` satisfy `∑ v ∈ X, c v = k`. By
`SimpleGraph.card_le_sum_of_forall_exists_mem_support`, the family is then largest and the
separator of least weight. -/
theorem exists_paths_setSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ)
    (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, G.Walk (a i) (b i)) (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (∀ v, #{i | v ∈ (P i).support} ≤ c v) ∧
      (∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X) ∧ ∑ v ∈ X, c v = k := by
  obtain ⟨k, a, b, P, X, ha, hb, hP, hint, hPv, hX, hk⟩ :=
    _root_.TauCeti.exists_paths_setSeparator_sum_eq (Q := G.AdjHom) c A B
  exact ⟨k, a, b, fun i ↦ (P i).toWalk, X, ha, hb, fun i ↦ by simpa using hP i,
    by simpa using hint, by simpa using hPv,
    fun a ha b hb ↦ forall_exists_mem_support_iff.2 (hX a ha b hb), hk⟩

/-- **Weak duality for vertex-disjoint set-to-set walks.** A family of pairwise vertex-disjoint
walks, each from a vertex of `A` to a vertex of `B`, has at most `#X` members, for every set `X` of
vertices meeting every walk from a vertex of `A` to a vertex of `B`. -/
theorem card_le_card_of_forall_exists_mem_support {A B : Finset V} {ι : Type*} [Fintype ι]
    {a b : ι → V} {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hP : Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) {X : Finset V}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X) :
    Fintype.card ι ≤ #X :=
  card_le_card_of_forall_not_reachableAvoiding (P := fun i ↦ (P i).toArrowWalk) ha hb
    (fun _ _ hij ↦ by simpa using hP hij) fun a ha b hb ↦
      forall_exists_mem_support_iff.1 (hX a ha b hb)

/-- **Menger's theorem for vertex-disjoint paths between vertex sets.** Let `A` and `B` be sets of
vertices of a simple graph on a finite vertex type. Some family of `k` pairwise vertex-disjoint
paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with its other vertices in neither `A` nor `B`, and
some set of `k` vertices meeting every walk from a vertex of `A` to a vertex of `B` exist. By
`SimpleGraph.card_le_card_of_forall_exists_mem_support`, the family is then largest and the
separator smallest. -/
theorem exists_paths_setSeparator_card_eq [Finite V] (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, G.Walk (a i) (b i)) (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) ∧
      (∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X) ∧ #X = k := by
  obtain ⟨k, a, b, P, X, ha, hb, hP, hint, hdisj, hX, hk⟩ :=
    _root_.TauCeti.exists_paths_setSeparator_card_eq (Q := G.AdjHom) A B
  exact ⟨k, a, b, fun i ↦ (P i).toWalk, X, ha, hb, fun i ↦ by simpa using hP i,
    by simpa using hint, fun _ _ hij ↦ by simpa using hdisj hij,
    fun a ha b hb ↦ forall_exists_mem_support_iff.2 (hX a ha b hb), hk⟩

/-- **Menger's theorem for vertex-disjoint paths between vertex sets, predicate form.** Let `A` and
`B` be sets of vertices of a simple graph on a finite vertex type. For every set `X` of fewer than
`k` vertices, some walk from a vertex of `A` to a vertex of `B` avoids `X`, exactly when there are
`k` pairwise vertex-disjoint paths, each from a vertex of `A` to a vertex of `B` with its other
vertices in neither `A` nor `B`. -/
theorem forall_exists_walk_iff_exists_paths [Finite V] (A B : Finset V) (k : ℕ) :
    (∀ X : Finset V, #X < k → ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ X) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).support.Disjoint (P j).support := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, P, ha, hb, _, _, hP⟩ X hX ↦ ?_⟩
  · obtain ⟨a, b, P, ha, hb, hP, hint, hdisj⟩ :=
      (forall_exists_reachableAvoiding_iff_exists_paths (Q := G.AdjHom) A B k).1 fun X hX ↦
        let ⟨a, ha, b, hb, hab⟩ := h X hX
        ⟨a, ha, b, hb, reachableAvoiding_adjHom_iff.2 hab⟩
    exact ⟨a, b, fun i ↦ (P i).toWalk, ha, hb, fun i ↦ by simpa using hP i, by simpa using hint,
      fun _ _ hij ↦ by simpa using hdisj hij⟩
  · by_contra h
    push Not at h
    exact hX.not_ge (by simpa using card_le_card_of_forall_exists_mem_support ha hb hP h)

end SetToSet

end SimpleGraph
