/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.MixedCapacity
public import TauCeti.Combinatorics.Quiver.Prefunctor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Menger's theorem for vertex-disjoint directed paths

Let `Q` be an arrow family on a finite vertex type `V`, let `s ≠ t` be vertices with no arrow from
`s` to `t`, and let `c v : ℕ` be a capacity on every vertex. A *packing* of `s`–`t` paths is a
finite indexed family of directed `s`–`t` paths, repetitions allowed, in which every vertex `v`
other than `s` and `t` lies on at most `c v` members. A *vertex separator* is a set `X` of
vertices, avoiding `s` and `t`, whose deletion leaves `t` unreachable from `s`; its weight is
`∑ v ∈ X, c v`.

This file proves the vertex-capacitated form of Menger's theorem: some packing has as many members
as some vertex separator has weight, and every packing has at most as many members as every vertex
separator has weight. For `c = 1` the members of a packing are distinct and internally
vertex-disjoint, which gives the local vertex form of Menger's theorem, also in predicate form: `t`
stays reachable from `s` after deleting any fewer than `k` vertices other than `s` and `t` exactly
when there are `k` internally vertex-disjoint `s`–`t` paths. Without the hypothesis that no arrow
runs from `s` to `t`, no vertex separator exists, and with `c = 1` a direct arrow could be repeated
arbitrarily often in a packing.

The arrow types need not be finite, since the statements concern only the vertices visited by
walks.

## Main results

* `TauCeti.card_le_sum_of_not_reachableAvoiding`: **weak duality**, a family of `s`–`t` walks in
  which every vertex `v` other than `s` and `t` lies on at most `c v` members has at most as many
  members as the weight of any vertex separator.
* `TauCeti.exists_paths_vertexSeparator_sum_eq`: **vertex-capacitated Menger**, a packing and a
  vertex separator of equal size and weight.
* `TauCeti.card_le_card_of_not_reachableAvoiding`: weak duality for families of walks pairwise
  sharing no vertex other than `s` and `t`.
* `TauCeti.exists_paths_vertexSeparator_card_eq`: **Menger's theorem** for internally
  vertex-disjoint directed paths, in witness form.
* `TauCeti.forall_reachableAvoiding_iff_exists_paths`: its predicate form.

## Implementation notes

Weak duality is counting: each member of a packing visits a vertex of the separator, and the
separator vertex `v` is visited by at most `c v` members. Attainment is reduced to the
max-flow/min-cut theorem for mixed vertex and arrow capacities over `ℤ`
(`TauCeti.Flow.exists_respectsVertexCapacity_val_eq`), with capacity `M = ∑ v, c v + 1` on every
arrow. The vertices other than `s` and `t` form a separator of weight below `M`, so a minimum mixed
separator contains no arrows and is a vertex separator. A maximum flow carries a packing with as
many members as its value (`TauCeti.Flow.exists_paths_card_eq_val_card_filter_le`). For arrow types
that may be infinite, the arrow family is first replaced by the family with one arrow from `v` to
`w` whenever `Q v w` is inhabited, which has walks with the same vertex sequences.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v} {s t : V}

/-! ### Weak duality -/

/-- **Weak duality for vertex-capacitated packings.** A family of `s`–`t` walks in which every
vertex `v` other than `s` and `t` lies on at most `c v` members has at most `∑ v ∈ X, c v`
members, for every set `X` of vertices avoiding `s` and `t` whose deletion leaves `t` unreachable
from `s`. -/
theorem card_le_sum_of_not_reachableAvoiding [DecidableEq V] {ι : Type*} [Fintype ι]
    {P : ι → ArrowWalk Q s t} {c : V → ℕ}
    (hP : ∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).vertices} ≤ c v) {X : Finset V} (hs : s ∉ X)
    (ht : t ∉ X) (hX : ¬ReachableAvoiding Q (X : Set V) s t) :
    Fintype.card ι ≤ ∑ v ∈ X, c v := by
  have h (i : ι) : ∃ v ∈ (P i).vertices, v ∈ X := by
    by_contra! h
    exact hX (reachableAvoiding_def.2 ⟨P i, fun v hv hvX ↦ h v hv hvX⟩)
  choose g hg hgX using h
  rw [← card_univ, card_eq_sum_card_fiberwise fun i _ ↦ hgX i]
  refine sum_le_sum fun v hv ↦ (card_le_card fun i hi ↦ ?_).trans
    (hP v (ne_of_mem_of_not_mem hv hs) (ne_of_mem_of_not_mem hv ht))
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi ▸ hg i

/-! ### Vertex-capacitated Menger -/

/-- Vertex-capacitated Menger for finite arrow types. -/
private theorem exists_paths_vertexSeparator_sum_eq_of_finite [Finite V] [DecidableEq V]
    [∀ x y, Finite (Q x y)] (c : V → ℕ) (hst : s ≠ t) (hadj : IsEmpty (Q s t)) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk Q s t) (X : Finset V), (∀ i, (P i).IsPath) ∧
      (∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).vertices} ≤ c v) ∧
      s ∉ X ∧ t ∉ X ∧ ¬ReachableAvoiding Q (X : Set V) s t ∧ ∑ v ∈ X, c v = k := by
  have := Fintype.ofFinite V
  have (x y : V) : Fintype (Q x y) := Fintype.ofFinite _
  set M : ℤ := ∑ v, (c v : ℤ) + 1
  have hM : 0 ≤ M := by positivity
  obtain ⟨f, hf, X, F, hXF, hval⟩ := Flow.exists_respectsVertexCapacity_val_eq (Q := Q)
    (cap := fun _ _ _ ↦ M) (c := fun v ↦ (c v : ℤ)) hst (fun _ _ _ ↦ hM) fun _ _ _ ↦ by positivity
  -- The vertices other than `s` and `t` form a separator of weight below `M`.
  have hsep : IsMixedSeparator {v | v ≠ s ∧ v ≠ t} (∅ : Finset (Σ v w, Q v w)) s t := by
    refine isMixedSeparator_empty_iff.2 ⟨by simp, by simp, fun h ↦ ?_⟩
    obtain ⟨p, hp⟩ := reachableAvoiding_def.1 h
    obtain ⟨v, hv, hvs, hvt⟩ := p.exists_mem_vertices_ne_ne hst hadj
    exact hp v hv (by simp [hvs, hvt])
  have hlt : f.val < M := by
    refine (hf.val_le hsep).trans_lt ?_
    rw [sum_empty, add_zero, Int.lt_add_one_iff]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
  -- A mixed separator of weight below `M` contains no arrows.
  obtain rfl : F = ∅ := by
    by_contra hF
    obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 hF
    have hMF : M ≤ ∑ a ∈ F, M := single_le_sum (f := fun _ ↦ M) (fun _ _ ↦ hM) ha
    have hX : 0 ≤ ∑ v ∈ X, (c v : ℤ) := by positivity
    omega
  obtain ⟨hs, ht, hX⟩ := isMixedSeparator_empty_iff.1 hXF
  obtain ⟨k, P, hk, hP, hPv⟩ := f.exists_paths_card_eq_val_card_filter_le
  refine ⟨k, P, X, hP, fun v hvs hvt ↦ ?_, hs, ht, hX, ?_⟩
  · exact_mod_cast (hPv v hvs).trans (hf.le hvs hvt)
  · rw [hval, sum_empty, add_zero] at hk
    exact_mod_cast hk.symm

/-- **Vertex-capacitated Menger's theorem for directed paths.** Let `s ≠ t` be vertices of an arrow
family on a finite vertex type, with no arrow from `s` to `t`, and let `c v` be a capacity on every
vertex. Some family of `k` directed `s`–`t` paths, in which every vertex `v` other than `s` and `t`
lies on at most `c v` members, and some set `X` of vertices avoiding `s` and `t`, whose deletion
leaves `t` unreachable from `s`, satisfy `∑ v ∈ X, c v = k`. By
`TauCeti.card_le_sum_of_not_reachableAvoiding`, the family is then largest and the separator of
least weight. -/
theorem exists_paths_vertexSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ) (hst : s ≠ t)
    (hadj : IsEmpty (Q s t)) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk Q s t) (X : Finset V), (∀ i, (P i).IsPath) ∧
      (∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).vertices} ≤ c v) ∧
      s ∉ X ∧ t ∉ X ∧ ¬ReachableAvoiding Q (X : Set V) s t ∧ ∑ v ∈ X, c v = k := by
  -- Replace `Q` by the arrow family with one arrow from `v` to `w` whenever `Q v w` is inhabited,
  -- which has the same walks up to their vertex sequences.
  let R : V → V → Type := fun v w ↦ PLift (Nonempty (Q v w))
  let φ : @Prefunctor V ⟨Q⟩ V ⟨R⟩ := @Prefunctor.mk V ⟨Q⟩ V ⟨R⟩ id fun e ↦ ⟨⟨e⟩⟩
  let ψ : @Prefunctor V ⟨R⟩ V ⟨Q⟩ := @Prefunctor.mk V ⟨R⟩ V ⟨Q⟩ id fun e ↦ Classical.choice e.down
  obtain ⟨k, P, X, hP, hPv, hs, ht, hX, hk⟩ := exists_paths_vertexSeparator_sum_eq_of_finite
    (Q := R) c hst ⟨fun e ↦ hadj.false (Classical.choice e.down)⟩
  refine ⟨k, fun i ↦ @Prefunctor.mapPath V ⟨R⟩ V ⟨Q⟩ ψ s t (P i), X, fun i ↦ ?_,
    fun v hvs hvt ↦ ?_, hs, ht, fun h ↦ hX ?_, hk⟩
  · rw [ArrowWalk.isPath_def, ArrowWalk.vertices_mapPath_of_obj_eq_id ψ rfl]
    exact (ArrowWalk.isPath_def _).1 (hP i)
  · simpa only [ArrowWalk.vertices_mapPath_of_obj_eq_id ψ rfl] using hPv v hvs hvt
  · obtain ⟨p, hp⟩ := reachableAvoiding_def.1 h
    exact reachableAvoiding_def.2 ⟨@Prefunctor.mapPath V ⟨Q⟩ V ⟨R⟩ φ s t p,
      by rwa [ArrowWalk.vertices_mapPath_of_obj_eq_id φ rfl]⟩

/-! ### Internally vertex-disjoint paths -/

/-- In a family of `s`–`t` walks whose members pairwise share no vertex other than `s` and `t`,
every other vertex lies on at most one member. -/
private theorem card_filter_mem_vertices_le_one [DecidableEq V] {ι : Type*} [Fintype ι]
    {P : ι → ArrowWalk Q s t}
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) {v : V}
    (hvs : v ≠ s) (hvt : v ≠ t) : #{i | v ∈ (P i).vertices} ≤ 1 :=
  card_le_one.2 fun i hi j hj ↦ by
    by_contra hij
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact (ArrowWalk.internallyDisjoint_def.1 (hP hij) v hi hj).elim hvs hvt

/-- **Weak duality for internally vertex-disjoint walks.** A family of `s`–`t` walks whose members
pairwise share no vertex other than `s` and `t` has at most `#X` members, for every set `X` of
vertices avoiding `s` and `t` whose deletion leaves `t` unreachable from `s`. -/
theorem card_le_card_of_not_reachableAvoiding {ι : Type*} [Fintype ι] {P : ι → ArrowWalk Q s t}
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    {X : Finset V} (hs : s ∉ X) (ht : t ∉ X) (hX : ¬ReachableAvoiding Q (X : Set V) s t) :
    Fintype.card ι ≤ #X := by
  classical
  simpa using card_le_sum_of_not_reachableAvoiding (c := 1)
    (fun v hvs hvt ↦ card_filter_mem_vertices_le_one hP hvs hvt) hs ht hX

/-- **Menger's theorem for internally vertex-disjoint directed paths.** Let `s ≠ t` be vertices of
an arrow family on a finite vertex type, with no arrow from `s` to `t`. Some family of `k` distinct
directed `s`–`t` paths, pairwise sharing no vertex other than `s` and `t`, and some set of `k`
vertices avoiding `s` and `t`, whose deletion leaves `t` unreachable from `s`, exist. By
`TauCeti.card_le_card_of_not_reachableAvoiding`, the family is then largest and the separator
smallest. -/
theorem exists_paths_vertexSeparator_card_eq [Finite V] (hst : s ≠ t) (hadj : IsEmpty (Q s t)) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk Q s t) (X : Finset V), Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      s ∉ X ∧ t ∉ X ∧ ¬ReachableAvoiding Q (X : Set V) s t ∧ #X = k := by
  classical
  obtain ⟨k, P, X, hP, hPv, hs, ht, hX, hk⟩ := exists_paths_vertexSeparator_sum_eq (Q := Q) 1 hst
    hadj
  -- Two different members through a vertex other than `s` and `t` would exceed its capacity.
  have hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
    intro i j hij
    rw [ArrowWalk.internallyDisjoint_def]
    intro v hvi hvj
    by_contra! hv
    have h2 : 1 < #{l | v ∈ (P l).vertices} :=
      one_lt_card.2 ⟨i, by simpa using hvi, j, by simpa using hvj, hij⟩
    exact (hPv v hv.1 hv.2).not_gt h2
  exact ⟨k, P, X, injective_of_pairwise_internallyDisjoint hdisj
    fun i ↦ (P i).exists_mem_vertices_ne_ne hst hadj, hP, hdisj, hs, ht, hX, by simpa using hk⟩

/-- **Menger's theorem for internally vertex-disjoint directed paths, predicate form.** Let `s ≠ t`
be vertices of an arrow family on a finite vertex type, with no arrow from `s` to `t`. Then `t`
stays reachable from `s` after deleting any fewer than `k` vertices other than `s` and `t` exactly
when there are `k` directed `s`–`t` paths pairwise sharing no vertex other than `s` and `t`. -/
theorem forall_reachableAvoiding_iff_exists_paths [Finite V] (hst : s ≠ t)
    (hadj : IsEmpty (Q s t)) (k : ℕ) :
    (∀ X : Finset V, s ∉ X → t ∉ X → #X < k → ReachableAvoiding Q (X : Set V) s t) ↔
      ∃ P : Fin k → ArrowWalk Q s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ X hs ht hX ↦ ?_⟩
  · obtain ⟨m, P, X, -, hP, hdisj, hs, ht, hX, hXm⟩ :=
      exists_paths_vertexSeparator_card_eq (Q := Q) hst hadj
    have hkm : k ≤ m := hXm ▸ not_lt.1 fun hlt ↦ hX (h X hs ht hlt)
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    exact hX.not_ge (by simpa using card_le_card_of_not_reachableAvoiding hP hs ht h)

end TauCeti
