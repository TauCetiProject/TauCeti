/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Tactic.Linarith
import TauCeti.Data.Finset.PairwiseDisjoint

/-!
# Sunflowers and the sunflower lemma

A sunflower is a family of finite sets any two distinct members of which meet in the same set,
the kernel of the sunflower. The sunflower lemma of Erdős and Rado says that a family of more
than `k! (p - 1) ^ k` sets with at most `k` elements each contains a sunflower with `p` members.

The proof is by induction on `k`. A subfamily of pairwise disjoint members is a sunflower with
empty kernel, so one may assume that every such subfamily has fewer than `p` members. The union
of a maximal one is then small and meets every nonempty member of the family, so one of its
elements lies in many members; removing that element from them gives a family of smaller sets,
and adding it back to a sunflower found there gives a sunflower in the original family.

## Main definitions

* `Finset.IsSunflower`: any two distinct members of the family have the same intersection.

## Main statements

* `Finset.exists_isSunflower_of_lt_card`: the sunflower lemma.

## References

* Ryan Alweiss, Shachar Lovett, Kewen Wu and Jiapeng Zhang, *Improved bounds for the sunflower
  lemma*, arXiv:1908.08483, Lemma 1.2, where the lemma is attributed to Erdős and Rado.
-/

public section

open Finset
open scoped Nat

namespace Finset

variable {β : Type*} [DecidableEq β] {S T : Finset (Finset β)}

/-- A family `S` of finite sets is a sunflower if there is a set `Y`, its kernel, such that any
two distinct members of `S` have intersection `Y`. The kernel may be empty, and a family with at
most one member is a sunflower. -/
def IsSunflower (S : Finset (Finset β)) : Prop :=
  ∃ Y : Finset β, (S : Set (Finset β)).Pairwise fun A B ↦ A ∩ B = Y

theorem isSunflower_iff :
    S.IsSunflower ↔ ∃ Y : Finset β, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y :=
  Iff.rfl

/-- A subfamily of a sunflower is a sunflower. -/
theorem IsSunflower.subset (hS : S.IsSunflower) (hTS : T ⊆ S) : T.IsSunflower :=
  hS.imp fun _ hY ↦ hY.mono (coe_subset.mpr hTS)

/-- A family of pairwise disjoint sets is a sunflower, with empty kernel. -/
theorem isSunflower_of_pairwiseDisjoint (hS : (S : Set (Finset β)).PairwiseDisjoint id) :
    S.IsSunflower :=
  ⟨∅, fun _ hA _ hB hAB ↦ disjoint_iff_inter_eq_empty.mp (hS hA hB hAB)⟩

/-- A family with at most one member is a sunflower. -/
theorem isSunflower_of_card_le_one (hS : #S ≤ 1) : S.IsSunflower :=
  ⟨∅, Set.Subsingleton.pairwise (fun _ hA _ hB ↦ card_le_one.mp hS _ hA _ hB) _⟩

@[simp]
theorem isSunflower_empty : (∅ : Finset (Finset β)).IsSunflower :=
  isSunflower_of_card_le_one (by simp)

@[simp]
theorem isSunflower_singleton (A : Finset β) : ({A} : Finset (Finset β)).IsSunflower :=
  isSunflower_of_card_le_one (by simp)

/-- Any two sets form a sunflower, whose kernel is their intersection. -/
theorem isSunflower_pair (A B : Finset β) : ({A, B} : Finset (Finset β)).IsSunflower :=
  ⟨A ∩ B, by simp [Set.pairwise_pair, inter_comm]⟩

/-- Adding one element to every member of a sunflower gives a sunflower, whose kernel is the
old one with that element added. -/
theorem IsSunflower.image_insert (hS : S.IsSunflower) (x : β) :
    (S.image (insert x)).IsSunflower := by
  obtain ⟨Y, hY⟩ := hS
  refine ⟨insert x Y, fun A hA B hB hAB ↦ ?_⟩
  obtain ⟨A, hA', rfl⟩ := mem_image.mp hA
  obtain ⟨B, hB', rfl⟩ := mem_image.mp hB
  rw [← insert_inter_distrib, hY hA' hB' fun h ↦ hAB (congrArg _ h)]

/-- The counting step of the sunflower lemma: in a family of more than `(k + 1)! (p - 1) ^ (k + 1)`
sets with at most `k + 1` elements each, in which every subfamily of pairwise disjoint members has
fewer than `p` members, some element lies in more than `k! (p - 1) ^ k` members. -/
private theorem exists_lt_card_filter_mem {k p : ℕ} (F : Finset (Finset β))
    (hsize : ∀ A ∈ F, #A ≤ k + 1) (hcard : (k + 1)! * (p - 1) ^ (k + 1) < #F)
    (hF : ∀ S ⊆ F, (S : Set (Finset β)).PairwiseDisjoint id → #S < p) :
    ∃ x, k ! * (p - 1) ^ k < #{A ∈ F | x ∈ A} := by
  obtain ⟨D, hDF, hD, hmax⟩ := F.exists_subset_pairwiseDisjoint_forall_disjoint_biUnion_mem
  have hDp := hF D hDF hD
  set U := D.biUnion id with hU
  set M := k ! * (p - 1) ^ k
  have hcard' : (k + 1) * ((p - 1) * M) < #F := by
    rwa [Nat.factorial_succ, pow_succ', mul_mul_mul_comm, mul_assoc] at hcard
  -- The empty set contributes nothing to the union `U`.
  have hUle : #U ≤ #(D.erase ∅) * (k + 1) := by
    have hUeq : U = (D.erase ∅).biUnion id := by
      ext x
      simp only [hU, mem_biUnion, mem_erase, id]
      exact ⟨fun ⟨A, hA, hx⟩ ↦ ⟨A, ⟨ne_empty_of_mem hx, hA⟩, hx⟩, fun ⟨A, hA, hx⟩ ↦ ⟨A, hA.2, hx⟩⟩
    rw [hUeq]
    exact card_biUnion_le_card_mul _ _ _ fun A hA ↦ hsize A (hDF (mem_of_mem_erase hA))
  -- By maximality of `D`, every nonempty member of `F` contains an element of `U`.
  have hFU : F.erase ∅ ⊆ U.biUnion fun x ↦ {A ∈ F | x ∈ A} := by
    intro A hA
    obtain ⟨hA0, hA⟩ := mem_erase.mp hA
    have hAU : ¬ Disjoint A U := fun hAU ↦
      hA0 (disjoint_self.mp (hAU.mono_right (subset_biUnion_of_mem id (hmax A hA hAU))))
    obtain ⟨x, hxA, hxU⟩ := not_disjoint_iff.mp hAU
    exact mem_biUnion.mpr ⟨x, hxU, mem_filter.mpr ⟨hA, hxA⟩⟩
  have hlt : ∑ _x ∈ U, M < ∑ x ∈ U, #{A ∈ F | x ∈ A} := by
    refine lt_of_lt_of_le ?_ ((card_le_card hFU).trans card_biUnion_le)
    rw [sum_const, smul_eq_mul]
    by_cases h0 : ∅ ∈ F
    · -- If the empty set is a member, it lies in `D`, so `D` has at most `p - 2` other members.
      have h0D : ∅ ∈ D := hmax ∅ h0 (disjoint_empty_left _)
      have h1 := card_erase_add_one h0D
      have h2 := card_erase_add_one h0
      have hM1 : 1 ≤ M := Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega) k)
      have h3 : (#(D.erase ∅) + 1) * ((k + 1) * M) ≤ (p - 1) * ((k + 1) * M) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith [Nat.mul_le_mul_right M hUle, Nat.zero_le (k * M)]
    · rw [erase_eq_of_notMem h0]
      have h1 : #(D.erase ∅) ≤ p - 1 := (card_le_card (erase_subset _ _)).trans (by omega)
      nlinarith [Nat.mul_le_mul_right M hUle, Nat.mul_le_mul_right ((k + 1) * M) h1]
  obtain ⟨x, -, hx⟩ := exists_lt_of_sum_lt hlt
  exact ⟨x, hx⟩

/-- **The sunflower lemma** of Erdős and Rado. A family of more than `k! (p - 1) ^ k` finite
sets, each with at most `k` elements, contains a sunflower with exactly `p` members. -/
theorem exists_isSunflower_of_lt_card {k p : ℕ} (F : Finset (Finset β))
    (hsize : ∀ A ∈ F, #A ≤ k) (hcard : k ! * (p - 1) ^ k < #F) :
    ∃ S ⊆ F, #S = p ∧ S.IsSunflower := by
  induction k generalizing F with
  | zero =>
    -- The only set with no elements is the empty one, so the family has at most one member.
    have hF : #F ≤ 1 := card_le_one.mpr fun A hA B hB ↦ by
      rw [card_eq_zero.mp (Nat.le_zero.mp (hsize A hA)),
        card_eq_zero.mp (Nat.le_zero.mp (hsize B hB))]
    simp at hcard
    omega
  | succ k ih =>
    by_cases hF : ∀ S ⊆ F, (S : Set (Finset β)).PairwiseDisjoint id → #S < p
    swap
    · -- Some `p` pairwise disjoint members form a sunflower with empty kernel.
      push Not at hF
      obtain ⟨D, hDF, hD, hpD⟩ := hF
      obtain ⟨S, hSD, hS⟩ := exists_subset_card_eq hpD
      exact ⟨S, hSD.trans hDF, hS,
        isSunflower_of_pairwiseDisjoint (hD.subset (coe_subset.mpr hSD))⟩
    -- Otherwise some `x` lies in many members; remove it from them and apply the induction.
    obtain ⟨x, hx⟩ := F.exists_lt_card_filter_mem hsize hcard hF
    have hinj : Set.InjOn (fun A : Finset β ↦ A.erase x) ({A ∈ F | x ∈ A} : Finset (Finset β)) :=
      (erase_injOn' x).mono fun A hA ↦ (mem_filter.mp hA).2
    obtain ⟨S, hSF, hSp, hS⟩ := ih (F.memberSubfamily x)
      (fun B hB ↦ by
        obtain ⟨hB, hxB⟩ := mem_memberSubfamily.mp hB
        have := hsize _ hB
        rw [card_insert_of_notMem hxB] at this
        omega)
      (by rwa [memberSubfamily, card_image_of_injOn hinj])
    have hxS : ∀ B ∈ S, x ∉ B := fun B hB ↦ (mem_memberSubfamily.mp (hSF hB)).2
    refine ⟨S.image (insert x), fun B hB ↦ ?_, ?_, hS.image_insert x⟩
    · obtain ⟨C, hC, rfl⟩ := mem_image.mp hB
      exact (mem_memberSubfamily.mp (hSF hC)).1
    · rw [card_image_of_injOn fun B hB C hC ↦ insert_injOn_notMem x (hxS B hB) (hxS C hC), hSp]

end Finset
