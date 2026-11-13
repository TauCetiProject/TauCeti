/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Indexed

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Lattice.Bounded

/-!
# Indexed unions and intersections of sets

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

The union of the binary family `![U, V]` is `U ∪ V`.

For pairwise disjoint sets `C`, the union `⋃ j, C j` splits into the earlier sets, the `k`-th set
and the later sets, and these pieces are disjoint.

## Main results

* `Set.iUnion_vecCons_pair`: the union of a family of two sets.
* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
* `TauCeti.exists_notMem_succ_of_notMem_iInter`: a point outside the intersection of a decreasing
  sequence of sets lies outside `K (k + 1)` for some `k`.
* `TauCeti.exists_map_eq_of_notMem`: a map taking the eventual value of maps which stabilize outside
  a decreasing sequence of sets, with a prescribed value on the intersection.
* `TauCeti.iUnion_eq_union_of_pairwise_disjoint`: the decomposition of `⋃ j, C j` for pairwise
  disjoint `C` and the disjointness of its three pieces.
-/

public section

open Function Set

/-- The union of the binary family `![U, V]` is `U ∪ V`. -/
@[simp]
theorem Set.iUnion_vecCons_pair {X : Type*} (U V : Set X) : ⋃ i, ![U, V] i = U ∪ V := by
  simp only [Matrix.vecCons, Set.iUnion_cons, Set.iUnion_of_empty, Set.union_empty]

namespace TauCeti

/-- The set of points where a family of functions `g i` satisfies a condition `Φ` on its tuple of
values is the union, over the tuples `ε` satisfying `Φ`, of the sets where `g i = ε i` for all
`i`. -/
theorem setOf_apply_eq_biUnion_iInter {α β ι : Type*} (g : ι → α → β) (Φ : (ι → β) → Prop) :
    {x | Φ fun i => g i x} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  exact ⟨fun h => ⟨_, h, fun _ => rfl⟩, fun ⟨ε, hε, h⟩ => (funext h).symm ▸ hε⟩

/-- A point outside the intersection of a decreasing sequence of sets lies outside `K (k + 1)` for
some `k`. -/
theorem exists_notMem_succ_of_notMem_iInter {α : Type*} {K : ℕ → Set α}
    (hKsucc : ∀ i, K (i + 1) ⊆ K i) {x : α} (hx : x ∉ ⋂ i, K i) : ∃ k, x ∉ K (k + 1) := by
  obtain ⟨i, hi⟩ : ∃ i, x ∉ K i := by simpa using hx
  exact ⟨i, fun h ↦ hi (hKsucc i h)⟩

/-- Let `K₀ ⊇ K₁ ⊇ ⋯` be a decreasing sequence of sets, and `G k` maps such that `G m = G k` outside
`K (k + 1)` whenever `k ≤ m`. For every `q` there is a map `g` with value `q` on `⋂ i, K i` which
agrees with `G k` outside `K (k + 1)` for every `k`. -/
theorem exists_map_eq_of_notMem {α β : Type*} {K : ℕ → Set α} (hKsucc : ∀ i, K (i + 1) ⊆ K i)
    {G : ℕ → α → β} (hGstab : ∀ k m, k ≤ m → ∀ x ∉ K (k + 1), G m x = G k x) (q : β) :
    ∃ g : α → β, (∀ x ∈ ⋂ i, K i, g x = q) ∧ ∀ k x, x ∉ K (k + 1) → g x = G k x := by
  classical
  have hex (x : α) (hx : x ∉ ⋂ i, K i) := exists_notMem_succ_of_notMem_iInter hKsucc hx
  refine ⟨fun x ↦ if hx : x ∈ ⋂ i, K i then q else G (hex x hx).choose x,
    fun x hx ↦ dite_eq_left hx, fun k x hx ↦ ?_⟩
  have hxX : x ∉ ⋂ i, K i := fun h ↦ hx (mem_iInter.1 h _)
  have hj := (hex x hxX).choose_spec
  dsimp only
  rw [dite_eq_right hxX]
  rcases le_total (hex x hxX).choose k with hjk | hkj
  · exact (hGstab _ k hjk x hj).symm
  · exact hGstab k _ hkj x hx

/-- For pairwise disjoint sets `C`, the union `⋃ j, C j` splits into the earlier sets, the `k`-th
set and the later sets, and these three pieces are disjoint. -/
theorem iUnion_eq_union_of_pairwise_disjoint {α : Type*} {C : ℕ → Set α}
    (hC : Pairwise (Disjoint on C)) (k : ℕ) :
    ⋃ j, C j = (⋃ i ∈ Finset.range k, C i) ∪ (C k ∪ ⋃ i, ⋃ (_ : k < i), C i) ∧
    Disjoint (⋃ i ∈ Finset.range k, C i) (C k ∪ ⋃ i, ⋃ (_ : k < i), C i) ∧
    Disjoint (C k) (⋃ i, ⋃ (_ : k < i), C i) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.mem_range, not_lt, Set.biUnion_ge, Set.iSup_eq_iUnion]
      using iSup_split C (fun i ↦ i < k)
  · simp only [disjoint_union_right, disjoint_iUnion_left, disjoint_iUnion_right,
      Finset.mem_range]
    exact ⟨fun i hi ↦ hC (hi.ne), fun i hi i' hi' ↦ hC (by omega : i' ≠ i)⟩
  · simp only [disjoint_iUnion_right]
    exact fun i hi ↦ hC hi.ne

end TauCeti
