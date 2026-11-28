/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import TauCeti.Dynamics.ForwardOrbit

/-!
# Spanning arborescences and the arborescence sum

A spanning arborescence of a finite vertex type `V` converging to a root `r` is recorded by its
parent function `p : V → V`: the root is fixed, and every vertex reaches the root under
iteration of `p`. Each vertex `v ≠ r` then has exactly one arc `v → p v`, and following these
arcs from any vertex leads to `r`. For a weight function `w : V → V → R` on ordered pairs of
vertices, the weight of an arborescence is the product of the weights `w v (p v)` of its arcs,
and the arborescence sum at `r` is the sum of these weights over all arborescences converging to
`r`. With all weights `1` in `ℕ` it is the number of arborescences converging to `r`; an arc of
weight `0` makes its arborescence contribute nothing. This sum is the right-hand side of the
directed matrix-tree theorem.

## Main definitions

* `TauCeti.IsArborescence r p`: the parent function `p` is a spanning arborescence converging
  to `r`.
* `TauCeti.arborescenceSum w r`: the sum over the arborescences `p` converging to `r` of
  `∏ v ∈ univ.erase r, w v (p v)`.

## Main results

* `TauCeti.IsArborescence.apply_eq_self_iff`: the root is the only fixed point of an
  arborescence, so a loop is never one of its arcs.
* `TauCeti.IsArborescence.iterate_card_sub_one`: `Fintype.card V - 1` iterations of `p` take
  every vertex to the root.
* `TauCeti.isArborescence_iff_iterate_card_sub_one`: the converse, which makes
  `IsArborescence r` decidable.
* `TauCeti.map_arborescenceSum`: a ring homomorphism maps the arborescence sum of `w` to the
  arborescence sum of the image weights.
* `TauCeti.arborescenceSum_of_subsingleton`: on one vertex the arborescence sum is `1`.
* `TauCeti.arborescenceSum_of_univ_eq_pair`: on two vertices the arborescence sum at one vertex
  is the weight of the arc from the other vertex to it.
* `TauCeti.arborescenceSum_fin_two_zero`, `TauCeti.arborescenceSum_fin_two_one`: the two-vertex
  case on `Fin 2`.

## References

* R. P. Stanley, *Topics in Algebraic Combinatorics*, author's draft of 1 February 2013,
  Chapter 10, p. 191 (oriented subtrees with root `r`).
-/

public section

open Finset Function

namespace TauCeti

section IsArborescence

variable {V : Type*} {r : V} {p : V → V}

/-- The parent function `p : V → V` is a spanning arborescence converging to the root `r`: the
root is fixed, and every vertex reaches the root under iteration of `p`. -/
def IsArborescence (r : V) (p : V → V) : Prop :=
  p r = r ∧ ∀ v, ∃ k : ℕ, p^[k] v = r

/-- The definition of an arborescence. -/
theorem isArborescence_def :
    IsArborescence r p ↔ p r = r ∧ ∀ v, ∃ k : ℕ, p^[k] v = r :=
  Iff.rfl

/-- An arborescence fixes its root. -/
theorem IsArborescence.apply_root (h : IsArborescence r p) : p r = r :=
  h.1

/-- In an arborescence every vertex reaches the root under iteration of the parent function. -/
theorem IsArborescence.exists_iterate_eq (h : IsArborescence r p) (v : V) :
    ∃ k : ℕ, p^[k] v = r :=
  h.2 v

/-- The constant function with value `r` is an arborescence converging to `r`: the star with
centre `r`. -/
@[simp]
theorem isArborescence_const (r : V) : IsArborescence r fun _ ↦ r :=
  ⟨rfl, fun _ ↦ ⟨1, rfl⟩⟩

/-- The root is the only fixed point of an arborescence: `p v ≠ v` for every `v ≠ r`, so a
loop is never an arc of an arborescence. -/
theorem IsArborescence.apply_eq_self_iff (h : IsArborescence r p) {v : V} :
    p v = v ↔ v = r := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ hv ▸ h.apply_root⟩
  obtain ⟨k, hk⟩ := h.exists_iterate_eq v
  rwa [iterate_fixed hv] at hk

variable [Fintype V]

/-- In an arborescence on `n` vertices, `n - 1` iterations of the parent function take every
vertex to the root. -/
theorem IsArborescence.iterate_card_sub_one (h : IsArborescence r p) (v : V) :
    p^[Fintype.card V - 1] v = r := by
  obtain ⟨k, hk, hkr⟩ :=
    mem_forwardOrbit_iff_exists_lt_card.1 (mem_forwardOrbit.2 (h.exists_iterate_eq v))
  rw [Nat.card_eq_fintype_card] at hk
  rw [← Nat.sub_add_cancel (Nat.le_sub_one_of_lt hk), iterate_add_apply, hkr,
    iterate_fixed h.apply_root]

/-- A parent function is an arborescence converging to `r` exactly when it fixes `r` and
`Fintype.card V - 1` of its iterations take every vertex to `r`. -/
theorem isArborescence_iff_iterate_card_sub_one :
    IsArborescence r p ↔ p r = r ∧ ∀ v, p^[Fintype.card V - 1] v = r :=
  ⟨fun h ↦ ⟨h.apply_root, h.iterate_card_sub_one⟩, fun h ↦ ⟨h.1, fun v ↦ ⟨_, h.2 v⟩⟩⟩

/-- Being an arborescence is decidable, by `isArborescence_iff_iterate_card_sub_one`. -/
instance [DecidableEq V] (r : V) : DecidablePred (IsArborescence r) := fun _ ↦
  decidable_of_iff _ isArborescence_iff_iterate_card_sub_one.symm

end IsArborescence

section arborescenceSum

variable {V : Type*} [Fintype V] [DecidableEq V] {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The weighted arborescence sum at the root `r`: the sum, over all spanning arborescences `p`
converging to `r`, of the product of the weights `w v (p v)` of their arcs. -/
def arborescenceSum (w : V → V → R) (r : V) : R :=
  ∑ p ∈ univ.filter (IsArborescence r), ∏ v ∈ univ.erase r, w v (p v)

/-- The definition of the arborescence sum. -/
theorem arborescenceSum_def (w : V → V → R) (r : V) :
    arborescenceSum w r = ∑ p ∈ univ.filter (IsArborescence r), ∏ v ∈ univ.erase r, w v (p v) :=
  (rfl)

/-- A ring homomorphism `f` maps the arborescence sum of `w` at `r` to the arborescence sum of
the weights `f (w u v)` at `r`. -/
theorem map_arborescenceSum {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)
    (w : V → V → R) (r : V) :
    f (arborescenceSum w r) = arborescenceSum (fun u v ↦ f (w u v)) r := by
  simp [arborescenceSum, map_sum, map_prod]

/-- On a vertex type with at most one vertex, the identity is the only parent function, it is an
arborescence, and its weight is the empty product, so the arborescence sum is `1`. -/
@[simp]
theorem arborescenceSum_of_subsingleton [Subsingleton V] (w : V → V → R) (r : V) :
    arborescenceSum w r = 1 := by
  have hfilter : univ.filter (IsArborescence r) = {fun _ ↦ r} := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ ↦ Subsingleton.elim _ _, fun hp ↦ hp ▸ isArborescence_const r⟩
  have herase : univ.erase r = ∅ := by
    ext v
    simp [Subsingleton.elim v r]
  simp [arborescenceSum, hfilter, herase]

/-- On two vertices `r` and `v`, the only arborescence converging to `r` sends `v` to `r`, so the
arborescence sum at `r` is the weight of the arc from `v` to `r`. -/
theorem arborescenceSum_of_univ_eq_pair (w : V → V → R) {r v : V} (hvr : v ≠ r)
    (huniv : (univ : Finset V) = {r, v}) :
    arborescenceSum w r = w v r := by
  have hmem (u : V) : u = r ∨ u = v := by
    simpa [huniv] using mem_univ u
  have hfilter : univ.filter (IsArborescence r) = {fun _ ↦ r} := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    refine ⟨fun hp ↦ funext fun u ↦ ?_, fun hp ↦ hp ▸ isArborescence_const r⟩
    rcases hmem u with rfl | rfl
    · exact hp.apply_root
    · exact (hmem (p u)).resolve_right fun h ↦ hvr (hp.apply_eq_self_iff.1 h)
  have herase : univ.erase r = {v} := by
    rw [huniv, erase_insert_eq_erase, erase_eq_of_notMem (by simpa using hvr.symm)]
  simp [arborescenceSum, hfilter, herase]

/-- On `Fin 2` the arborescence sum at `0` is the weight of the arc from `1` to `0`. -/
theorem arborescenceSum_fin_two_zero (w : Fin 2 → Fin 2 → R) :
    arborescenceSum w 0 = w 1 0 :=
  arborescenceSum_of_univ_eq_pair w (by decide) (by decide)

/-- On `Fin 2` the arborescence sum at `1` is the weight of the arc from `0` to `1`. -/
theorem arborescenceSum_fin_two_one (w : Fin 2 → Fin 2 → R) :
    arborescenceSum w 1 = w 0 1 :=
  arborescenceSum_of_univ_eq_pair w (by decide) (by decide)

end arborescenceSum

end TauCeti
