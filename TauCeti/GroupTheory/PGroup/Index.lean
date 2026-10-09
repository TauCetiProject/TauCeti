/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.GroupTheory.Index.Basic
import TauCeti.GroupTheory.QuotientGroup.Index
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Indices of subgroups in an extension of a cyclic group by a `p`-group

Let `V` be a normal `p`-subgroup of a group `G`. A subgroup `A` of index prime to `p` contains
`V`: the index `[A ⊔ V : A] = [V : A ⊓ V]` is a power of `p` dividing `[G : A]`.

If moreover `G ⧸ V` is cyclic, then the index of an intersection `A ⊓ B` is the
least common multiple of the indices of `A` and `B`, as soon as one of them, `A`, has index prime
to `p`. Indeed `A` contains `V`, so it is normal and
`[G : A ⊓ B] · [G : A ⊔ B] = [G : A] · [G : B]`; and in the cyclic group `G ⧸ V` the index of a
join is the gcd of the indices.

This is the group theory behind Abhyankar's lemma: the inertia group of a place in a Galois
extension with separable residue extension is of this shape, its first ramification group being
a normal `p`-subgroup with cyclic quotient, and ramification indices of intermediate fields are
indices in it.

## Main results

* `IsPGroup.le_of_not_dvd_index`: a normal `p`-subgroup lies in every subgroup of index prime
  to `p`.
* `IsPGroup.index_inf_eq_lcm`: if `G ⧸ V` is cyclic for a normal `p`-subgroup `V` and `p` does not
  divide `[G : A]`, then `[G : A ⊓ B] = lcm ([G : A], [G : B])`.
-/

public section

open Subgroup

namespace IsPGroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {V : Subgroup G} [V.Normal]

/-- **A normal `p`-subgroup lies in every subgroup of index prime to `p`**: the index
`[A ⊔ V : A] = [V : A ⊓ V]` is a power of `p` dividing `[G : A]`. -/
theorem le_of_not_dvd_index (hV : IsPGroup p V) {A : Subgroup G} (hA : ¬ p ∣ A.index) :
    V ≤ A := by
  have h : A.relIndex V ∣ A.index := by
    rw [← relIndex_sup_of_le_normalizer (le_normalizer_of_normal (H := V))]
    exact relIndex_dvd_index_of_le le_sup_left
  -- `A` has finite index, as `p` divides `0`, hence so has `A ⊓ V` in `V`.
  have : (A.subgroupOf V).FiniteIndex :=
    ⟨fun h0 ↦ hA (by rw [relIndex, h0, zero_dvd_iff] at h; rw [h]; exact dvd_zero p)⟩
  obtain ⟨n, hn⟩ := hV.index (A.subgroupOf V)
  rw [relIndex, hn] at h
  rcases n with _ | n
  · rwa [pow_zero, ← relIndex, relIndex_eq_one] at hn
  · exact absurd ((dvd_pow_self p n.succ_ne_zero).trans h) hA

/-- **The index of an intersection is the lcm of the indices** in a group `G` with a normal
`p`-subgroup `V` such that `G ⧸ V` is cyclic, provided one of the two subgroups has index prime to
`p`. No finiteness is assumed; a subgroup of infinite index has index `0` by convention. -/
theorem index_inf_eq_lcm (hV : IsPGroup p V) [IsCyclic (G ⧸ V)] {A : Subgroup G}
    (hA : ¬ p ∣ A.index) (B : Subgroup G) :
    (A ⊓ B).index = A.index.lcm B.index := by
  -- If `B` has infinite index, then so has `A ⊓ B`, and both sides vanish.
  rcases eq_or_ne B.index 0 with hB0 | hB0
  · rw [hB0, Nat.lcm_zero_right]
    exact Nat.eq_zero_of_zero_dvd (hB0 ▸ index_dvd_of_le inf_le_right)
  have : B.FiniteIndex := ⟨hB0⟩
  -- `A` has finite index, as `p` divides `0`.
  have hA0 : A.index ≠ 0 := fun h ↦ hA (h ▸ dvd_zero p)
  have hVA := hV.le_of_not_dvd_index hA
  have hπ : Function.Surjective (QuotientGroup.mk' V) := QuotientGroup.mk'_surjective V
  have hker {H : Subgroup G} (h : V ≤ H) : (QuotientGroup.mk' V).ker ≤ H := by
    rwa [QuotientGroup.ker_mk']
  -- `A` contains `V` and `G ⧸ V` is commutative, so `A` is normal.
  have hAn : A.Normal := by
    rw [← comap_map_eq_self (hker hVA)]
    exact Normal.comap inferInstance _
  -- `[G : B] = p ^ m * [G : B ⊔ V]`, since `[B ⊔ V : B] = [V : B ⊓ V]` is a power of `p`.
  obtain ⟨m, hm⟩ := hV.index (B.subgroupOf V)
  have hB : B.index = p ^ m * (B ⊔ V).index := by
    have hrel : B.relIndex (B ⊔ V) = p ^ m := by
      rw [relIndex_sup_of_le_normalizer (le_normalizer_of_normal (H := V)), relIndex, hm]
    rw [← relIndex_mul_index (le_sup_left : B ≤ B ⊔ V), hrel]
  -- In the cyclic group `G ⧸ V`, `[G : A ⊔ B] = gcd ([G : A], [G : B ⊔ V])`, which is
  -- `gcd ([G : A], [G : B])` as `p` does not divide `[G : A]`.
  have hcop : (p ^ m).Coprime A.index :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hA)
  have hsup : (A ⊔ B).index = A.index.gcd B.index :=
    calc (A ⊔ B).index = ((A ⊔ B).map (QuotientGroup.mk' V)).index :=
          (index_map_eq _ hπ (hker (hVA.trans le_sup_left))).symm
      _ = (A.map (QuotientGroup.mk' V)).index.gcd (B.map (QuotientGroup.mk' V)).index := by
          rw [Subgroup.map_sup, IsCyclic.index_sup]
      _ = A.index.gcd (B ⊔ V).index := by
          rw [index_map_eq _ hπ (hker hVA), index_map_mk'_eq_index_sup]
      _ = A.index.gcd B.index := by
          rw [hB, Nat.Coprime.gcd_mul_left_cancel_right _ hcop]
  -- `[G : A ⊓ B] * [G : A ⊔ B] = [G : A] * [G : B]`: as `A` is normal,
  -- `[A : A ⊓ B] = [A ⊔ B : B]`, and `[A ⊔ B : B] * [G : A ⊔ B] = [G : B]`.
  have hmul : (A ⊓ B).index * (A ⊔ B).index = A.index * B.index :=
    calc (A ⊓ B).index * (A ⊔ B).index = A.index * (B.relIndex A * (A ⊔ B).index) := by
          rw [inf_comm, index_inf]
          ring
      _ = A.index * (B.relIndex (A ⊔ B) * (A ⊔ B).index) := by
          rw [sup_comm, relIndex_sup_of_le_normalizer (le_normalizer_of_normal (H := A))]
      _ = A.index * B.index := by
          rw [relIndex_mul_index (le_sup_right : B ≤ A ⊔ B)]
  rw [hsup, ← Nat.gcd_mul_lcm A.index B.index, mul_comm (Nat.gcd _ _)] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hA0)) hmul

end IsPGroup
