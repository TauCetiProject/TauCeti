/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals
public import TauCeti.Combinatorics.Network.Menger.Vertex
import Mathlib.Basic.Finite.Sum

/-!
# Menger's theorem for vertex-disjoint directed paths between vertex sets

Let `Q` be an arrow family on a finite vertex type `V`, let `A` and `B` be sets of vertices, and
let `c v : ℕ` be a capacity on every vertex. An *`A`–`B` path* is a directed path from a vertex
`a ∈ A` to a vertex `b ∈ B` whose vertices other than `a` and `b` lie in neither `A` nor `B`. A
*packing* of `A`–`B` paths is a finite indexed family of them, repetitions allowed, in which every
vertex `v`, endpoints included, lies on at most `c v` members. A *separator* is a set `X` of
vertices meeting every walk from a vertex of `A` to a vertex of `B`; it may meet `A` and `B`, and
its weight is `∑ v ∈ X, c v`.

This file proves the vertex-capacitated set-to-set form of Menger's theorem: some packing has as
many members as some separator has weight, and every packing has at most as many members as every
separator has weight. A vertex of `A ∩ B` is a path of length zero, which may be repeated up to its
capacity, and it lies in every separator. The sets `A` and `B` may be empty or overlap, and the
arrow types need not be finite. For `c = 1` the members of a packing are pairwise vertex-disjoint,
which gives the set-to-set form of Menger's theorem for vertex-disjoint paths, also in predicate
form: after deleting any fewer than `k` vertices some vertex of `B` stays reachable from some vertex
of `A` exactly when there are `k` pairwise vertex-disjoint `A`–`B` paths.

## Main results

* `TauCeti.card_le_sum_of_forall_not_reachableAvoiding`: **weak duality**, a family of walks from
  vertices of `A` to vertices of `B` in which every vertex `v` lies on at most `c v` members has at
  most as many members as the weight of any separator.
* `TauCeti.exists_paths_setSeparator_sum_eq`: **vertex-capacitated set-to-set Menger**, a packing
  of `A`–`B` paths and a separator of equal size and weight.
* `TauCeti.card_le_card_of_forall_not_reachableAvoiding`: weak duality for families of pairwise
  vertex-disjoint walks.
* `TauCeti.exists_paths_setSeparator_card_eq`: **Menger's theorem** for vertex-disjoint directed
  paths between two vertex sets, in witness form.
* `TauCeti.forall_exists_reachableAvoiding_iff_exists_paths`: its predicate form.

## Implementation notes

Both directions reduce to the vertex-capacitated Menger theorem between two vertices
(`TauCeti.exists_paths_vertexSeparator_sum_eq` and `TauCeti.card_le_sum_of_not_reachableAvoiding`)
for the arrow family `TauCeti.AuxTerminalHom Q A B`, which adds a fresh source `σ` with an arrow to
every vertex of `A` and a fresh sink `τ` with an arrow from every vertex of `B`; the original
vertices keep their capacities. Walks from `A` to `B` lift to `σ`–`τ` walks through the same
original vertices, and every `σ`–`τ` walk projects to a walk from `A` to `B`
(`TauCeti.reachableAvoiding_auxTerminalHom_iff`). Each `σ`–`τ` path of a packing is then trimmed to
an `A`–`B` path (`TauCeti.ArrowWalk.exists_isPath_interior_notMem`), which visits no new vertex.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset Sum

universe u v

variable {V : Type u} {Q : V → V → Type v}

/-! ### Vertex-capacitated packings -/

/-- **Weak duality for vertex-capacitated set-to-set packings.** A family of walks, each from a
vertex of `A` to a vertex of `B`, in which every vertex `v` lies on at most `c v` members, has at
most `∑ v ∈ X, c v` members, for every set `X` of vertices meeting every walk from a vertex of `A`
to a vertex of `B`. -/
theorem card_le_sum_of_forall_not_reachableAvoiding [DecidableEq V] {A B : Finset V} {ι : Type*}
    [Fintype ι] {a b : ι → V} {P : ∀ i, ArrowWalk Q (a i) (b i)} (ha : ∀ i, a i ∈ A)
    (hb : ∀ i, b i ∈ B) {c : V → ℕ} (hP : ∀ v, #{i | v ∈ (P i).vertices} ≤ c v) {X : Finset V}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding Q (X : Set V) a b) :
    Fintype.card ι ≤ ∑ v ∈ X, c v := by
  -- Lift every member to a walk between the auxiliary terminals.
  choose P' hP' using fun i ↦ AuxTerminalHom.exists_arrowWalk_vertices_eq (ha i) (hb i) (P i)
  have hsep : ¬ReachableAvoiding (AuxTerminalHom Q A B)
      ((X.map .inl : Finset (V ⊕ Bool)) : Set (V ⊕ Bool)) (inr false) (inr true) := by
    rw [reachableAvoiding_auxTerminalHom_iff (by simp) (by simp)]
    rintro ⟨a, ha, b, hb, h⟩
    exact hX a ha b hb (by simpa [Set.preimage_image_eq _ inl_injective] using h)
  refine (card_le_sum_of_not_reachableAvoiding (P := P') (c := Sum.elim c 0)
    (fun x hxs hxt ↦ ?_) (by simp) (by simp) hsep).trans_eq (by simp)
  -- A lifted member visits `inl v` exactly when the original member visits `v`.
  rcases x with v | (_ | _)
  · simpa [hP'] using hP v
  · exact absurd rfl hxs
  · exact absurd rfl hxt

/-- **Vertex-capacitated Menger's theorem for directed paths between vertex sets.** Let `A` and `B`
be sets of vertices of an arrow family on a finite vertex type, and let `c v` be a capacity on every
vertex. Some family of `k` directed paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with its other
vertices in neither `A` nor `B`, in which every vertex `v` lies on at most `c v` members, and some
set `X` of vertices meeting every walk from a vertex of `A` to a vertex of `B` satisfy
`∑ v ∈ X, c v = k`. By `TauCeti.card_le_sum_of_forall_not_reachableAvoiding`, the family is then
largest and the separator of least weight. -/
theorem exists_paths_setSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ)
    (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)) (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (∀ v, #{i | v ∈ (P i).vertices} ≤ c v) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding Q (X : Set V) a b) ∧ ∑ v ∈ X, c v = k := by
  obtain ⟨k, P', X', -, hP', hσ, hτ, hX', hk⟩ :=
    exists_paths_vertexSeparator_sum_eq (Q := AuxTerminalHom Q A B) (Sum.elim c 0)
      (s := inr false) (t := inr true) (by simp) inferInstance
  -- Project every member to a walk from `A` to `B`, and trim it to an `A`–`B` path.
  have h (i : Fin k) : ∃ a ∈ A, ∃ b ∈ B, ∃ q : ArrowWalk Q a b, q.IsPath ∧
      q.vertices.map inl ⊆ (P' i).vertices ∧
      ∀ v ∈ q.vertices, v ≠ a → v ≠ b → v ∉ A ∧ v ∉ B := by
    obtain ⟨a, ha, b, hb, q, hq⟩ := AuxTerminalHom.exists_arrowWalk_map_vertices_subset (P' i)
    obtain ⟨a', ha', b', hb', r, hr, hrq, -, hint⟩ :=
      ArrowWalk.exists_isPath_interior_notMem (A := (A : Set V)) (B := (B : Set V)) q ha hb
    exact ⟨a', ha', b', hb', r, hr, List.Subset.trans (List.map_subset _ hrq) hq,
      by simpa using hint⟩
  choose a ha b hb P hP hsub hint using h
  have hpre : inl ⁻¹' (X' : Set (V ⊕ Bool)) = (X'.toLeft : Set V) := by
    ext
    simp
  refine ⟨k, a, b, P, X'.toLeft, ha, hb, hP, hint, fun v ↦ ?_, fun a ha b hb h ↦ hX' ?_, ?_⟩
  · -- A member through `v` comes from a member of the packing through `inl v`.
    refine (card_le_card fun i hi ↦ ?_).trans (hP' (inl v) inl_ne_inr inl_ne_inr)
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hsub i (List.mem_map_of_mem hi)
  · refine (reachableAvoiding_auxTerminalHom_iff (by simpa using hσ) (by simpa using hτ)).2
      ⟨a, ha, b, hb, ?_⟩
    rwa [hpre]
  · rw [sum_sum_eq_sum_toLeft_add_sum_toRight] at hk
    simpa using hk

/-! ### Vertex-disjoint paths -/

/-- **Weak duality for vertex-disjoint set-to-set walks.** A family of pairwise vertex-disjoint
walks, each from a vertex of `A` to a vertex of `B`, has at most `#X` members, for every set `X` of
vertices meeting every walk from a vertex of `A` to a vertex of `B`. -/
theorem card_le_card_of_forall_not_reachableAvoiding {A B : Finset V} {ι : Type*} [Fintype ι]
    {a b : ι → V} {P : ∀ i, ArrowWalk Q (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hP : Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices) {X : Finset V}
    (hX : ∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding Q (X : Set V) a b) :
    Fintype.card ι ≤ #X := by
  classical
  refine (card_le_sum_of_forall_not_reachableAvoiding (P := P) ha hb (c := 1) (fun v ↦ ?_)
    hX).trans_eq (by simp)
  refine card_le_one.2 fun i hi j hj ↦ ?_
  by_contra hij
  simp only [mem_filter, mem_univ, true_and] at hi hj
  exact hP hij hi hj

/-- **Menger's theorem for vertex-disjoint directed paths between vertex sets.** Let `A` and `B` be
sets of vertices of an arrow family on a finite vertex type. Some family of `k` pairwise
vertex-disjoint directed paths, the `i`-th from `a i ∈ A` to `b i ∈ B` with its other vertices in
neither `A` nor `B`, and some set of `k` vertices meeting every walk from a vertex of `A` to a
vertex of `B` exist. By `TauCeti.card_le_card_of_forall_not_reachableAvoiding`, the family is then
largest and the separator smallest. -/
theorem exists_paths_setSeparator_card_eq [Finite V] (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)) (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding Q (X : Set V) a b) ∧ #X = k := by
  classical
  obtain ⟨k, a, b, P, X, ha, hb, hP, hint, hPv, hX, hk⟩ :=
    exists_paths_setSeparator_sum_eq (Q := Q) 1 A B
  refine ⟨k, a, b, P, X, ha, hb, hP, hint, fun i j hij v hvi hvj ↦ ?_, hX, by simpa using hk⟩
  -- Two different members through `v` would exceed its capacity.
  have h2 : 1 < #{l | v ∈ (P l).vertices} :=
    one_lt_card.2 ⟨i, by simpa using hvi, j, by simpa using hvj, hij⟩
  exact (hPv v).not_gt h2

/-- **Menger's theorem for vertex-disjoint directed paths between vertex sets, predicate form.** Let
`A` and `B` be sets of vertices of an arrow family on a finite vertex type. After deleting any fewer
than `k` vertices, some vertex of `B` stays reachable from some vertex of `A` exactly when there
are `k` pairwise vertex-disjoint directed paths, each from a vertex of `A` to a vertex of `B` with
its other vertices in neither `A` nor `B`. -/
theorem forall_exists_reachableAvoiding_iff_exists_paths [Finite V] (A B : Finset V) (k : ℕ) :
    (∀ X : Finset V, #X < k → ∃ a ∈ A, ∃ b ∈ B, ReachableAvoiding Q (X : Set V) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk Q (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, P, ha, hb, _, _, hP⟩ X hX ↦ ?_⟩
  · obtain ⟨m, a, b, P, X, ha, hb, hP, hint, hdisj, hX, hXm⟩ :=
      exists_paths_setSeparator_card_eq (Q := Q) A B
    have hkm : k ≤ m := hXm ▸ not_lt.1 fun hlt ↦
      let ⟨a, ha, b, hb, hab⟩ := h X hlt
      hX a ha b hb hab
    exact ⟨fun i ↦ a (Fin.castLE hkm i), fun i ↦ b (Fin.castLE hkm i),
      fun i ↦ P (Fin.castLE hkm i), fun i ↦ ha _, fun i ↦ hb _, fun i ↦ hP _,
      fun i ↦ hint _, fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    push Not at h
    exact hX.not_ge (by simpa using card_le_card_of_forall_not_reachableAvoiding ha hb hP h)

end TauCeti
