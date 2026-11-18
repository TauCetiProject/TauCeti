/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Rel.Cover
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# Constant-weight packings

For two equal-sized subsets s and a of a finite ground set, the cardinality of a \ s
counts the number of replacements turning one into the other. Counting the removed and
added elements gives the sphere sizes for this distance. A maximal separated family covers
the ground family by balls and yields the constant-weight Gilbert bound. We also bound
ball sizes by counting subsets that contain a common part of the centre.

The sphere count and maximal-packing argument follow Giraud, *Introduction to
High-Dimensional Statistics*, 2nd ed., Lemma 3.7 and §3.6.2.
-/

public section

open scoped BigOperators

namespace Finset

variable {α : Type*} [DecidableEq α] {s t : Finset α} {k m : ℕ}

/-- The sphere of k-element subsets obtained by making exactly m replacements
from a k-element centre. The two factors count the removed and inserted elements. -/
theorem card_filter_powersetCard_card_sdiff_eq (hst : s ⊆ t) (hs : s.card = k) (m : ℕ) :
    ((t.powersetCard k).filter fun a ↦ (a \ s).card = m).card =
      k.choose m * (t.card - k).choose m := by
  let removedAdded := (s.powersetCard m) ×ˢ ((t \ s).powersetCard m)
  calc
    _ = removedAdded.card := by
      refine card_nbij' (fun a ↦ (s \ a, a \ s)) (fun uv ↦ (s \ uv.1) ∪ uv.2) ?_ ?_ ?_ ?_
      · intro a ha
        rcases mem_filter.mp ha with ⟨ha, hm⟩
        rcases mem_powersetCard.mp ha with ⟨hat, hak⟩
        have hsa := (card_sdiff_eq_card_sdiff_iff.mpr (hs.trans hak.symm)).trans hm
        exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset, hsa⟩,
          mem_powersetCard.mpr ⟨sdiff_subset_sdiff hat Subset.rfl, hm⟩⟩
      · intro ⟨u, v⟩ huv
        rcases mem_product.mp huv with ⟨hu, hv⟩
        rcases mem_powersetCard.mp hu with ⟨hus, hum⟩
        rcases mem_powersetCard.mp hv with ⟨hvt, hvm⟩
        have hd : Disjoint (s \ u) v :=
          disjoint_of_subset_left sdiff_subset
            (disjoint_of_subset_right hvt disjoint_sdiff_self_right)
        have hcard := card_sdiff_add_card_eq_card hus
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
        · exact union_subset (sdiff_subset.trans hst) (hvt.trans sdiff_subset)
        · rw [card_union_of_disjoint hd, hvm, ← hum, hcard, hs]
        · rwa [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr sdiff_subset, empty_union,
            sdiff_eq_self_iff_disjoint.mpr (disjoint_of_subset_left hvt disjoint_sdiff_self_left)]
      · intro a _
        ext i
        simp only [mem_union, mem_sdiff]
        grind
      · intro ⟨u, v⟩ huv
        rcases mem_product.mp huv with ⟨hu, hv⟩
        have hus := (mem_powersetCard.mp hu).1
        have hvs := (mem_powersetCard.mp hv).1
        ext : 1
        · ext i
          have hi := @hus i
          have hj := @hvs i
          simp only [mem_sdiff, mem_union] at *
          grind
        · ext i
          have hj := @hvs i
          simp only [mem_sdiff, mem_union] at *
          grind
    _ = _ := by
      simp [removedAdded, card_product, card_powersetCard, card_sdiff_of_subset hst, hs]

/-- The ball of radius r in the constant-weight family, measured in replacements. -/
theorem card_filter_powersetCard_card_sdiff_le (hst : s ⊆ t) (hs : s.card = k) (r : ℕ) :
    ((t.powersetCard k).filter fun a ↦ (a \ s).card ≤ r).card =
      ∑ j ∈ range (r + 1), k.choose j * (t.card - k).choose j := by
  have hmap : Set.MapsTo (fun a : Finset α ↦ (a \ s).card)
      (↑((t.powersetCard k).filter fun a ↦ (a \ s).card ≤ r) : Set (Finset α))
      (↑(range (r + 1)) : Set ℕ) := by
    intro a ha
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp ha).2)
  rw [card_eq_sum_card_fiberwise hmap]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [filter_filter]
  have hj' : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
  have heq (a : Finset α) : ((a \ s).card ≤ r ∧ (a \ s).card = j) ↔ (a \ s).card = j :=
    and_iff_right_of_imp fun h ↦ h ▸ hj'
  simpa only [heq] using card_filter_powersetCard_card_sdiff_eq hst hs j

/-- Any k-subset at most k - m replacements from s contains an m-subset of s.
Counting all extensions of those m-subsets gives this upper bound for the ball. -/
theorem card_filter_powersetCard_card_sdiff_le_mul_choose (hs : s.card = k) (hm : m ≤ k) :
    ((t.powersetCard k).filter fun a ↦ (a \ s).card ≤ k - m).card ≤
      k.choose m * (t.card - m).choose (k - m) := by
  let extensions := fun u : Finset α ↦ (t.powersetCard k).filter (u ⊆ ·)
  have hsub : ((t.powersetCard k).filter fun a ↦ (a \ s).card ≤ k - m) ⊆
      ((s ∩ t).powersetCard m).biUnion extensions := by
    intro a ha
    rcases mem_filter.mp ha with ⟨ha, hdist⟩
    rcases mem_powersetCard.mp ha with ⟨hat, hak⟩
    have hsum := card_sdiff_add_card_inter a s
    obtain ⟨u, hu, hum⟩ := exists_subset_card_eq (s := a ∩ s) (n := m) (by omega)
    have hua := hu.trans inter_subset_left
    have hust := subset_inter (hu.trans inter_subset_right) (hua.trans hat)
    exact mem_biUnion.mpr ⟨u, mem_powersetCard.mpr ⟨hust, hum⟩, mem_filter.mpr ⟨ha, hua⟩⟩
  refine (card_le_card hsub).trans
    ((card_biUnion_le_card_mul _ _ ((t.card - m).choose (k - m)) fun u hu ↦ ?_).trans ?_)
  · rcases mem_powersetCard.mp hu with ⟨hus, hum⟩
    rw [card_filter_powersetCard_subset _ _ _ (hus.trans inter_subset_right) (hum ▸ hm), hum]
  · rw [card_powersetCard, ← hs]
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (card_le_card inter_subset_left))

/-- A constant-weight packing covering the whole family of k-subsets with balls of
radius r in the replacement distance. This remains valid for an empty family. -/
theorem exists_powersetCard_pairwise_lt_card_sdiff_cover (t : Finset α) (k r : ℕ) :
    ∃ C ⊆ t.powersetCard k,
      (C : Set (Finset α)).Pairwise (fun a b ↦ r < (a \ b).card) ∧
        ∀ a ∈ t.powersetCard k, ∃ b ∈ C, (a \ b).card ≤ r := by
  let R : SetRel (Finset α) (Finset α) := {p | max (p.1 \ p.2).card (p.2 \ p.1).card ≤ r}
  have : R.IsRefl := ⟨fun a ↦ by simp [R]⟩
  have : R.IsSymm := ⟨fun a b h ↦ by simpa [R, and_comm] using h⟩
  let A : Set (Finset α) := ↑(t.powersetCard k)
  obtain ⟨C, hC⟩ := (finite_toSet (t.powersetCard k)).finite_subsets
    |>.subset (t := {C : Set (Finset α) | C ⊆ A ∧ R.IsSeparated C}) (fun _ h ↦ h.1)
    |>.exists_maximal ⟨∅, Set.empty_subset _, SetRel.IsSeparated.empty⟩
  let T := ((finite_toSet (t.powersetCard k)).subset hC.1.1).toFinset
  have hT : (T : Set (Finset α)) = C := Set.Finite.coe_toFinset _
  have hsub : T ⊆ t.powersetCard k := by simpa [← coe_subset, hT] using hC.1.1
  refine ⟨T, hsub, ?_, ?_⟩
  · rw [hT]
    intro a ha b hb hab
    have ha' := (mem_powersetCard.mp (hC.1.1 ha)).2
    have hb' := (mem_powersetCard.mp (hC.1.1 hb)).2
    have h := hC.1.2 ha hb hab
    exact lt_of_not_ge (by simpa [R, card_sdiff_comm (hb'.trans ha'.symm)] using h)
  · intro a ha
    obtain ⟨b, hb, hab⟩ := SetRel.IsCover.of_maximal_isSeparated hC ha
    have hb' : b ∈ T := by simpa [← hT] using hb
    exact ⟨b, hb', (le_max_left _ _).trans hab⟩

/-- A cover by constant-weight balls bounds the number of subsets by the number of
centres times a uniform bound on the sizes of their balls. -/
theorem choose_le_card_mul_of_powersetCard_cover {C : Finset (Finset α)} {r B : ℕ}
    (hcover : ∀ a ∈ t.powersetCard k, ∃ b ∈ C, (a \ b).card ≤ r)
    (hB : ∀ b ∈ C, ((t.powersetCard k).filter fun a ↦ (a \ b).card ≤ r).card ≤ B) :
    t.card.choose k ≤ C.card * B := by
  let ball := fun b : Finset α ↦ (t.powersetCard k).filter fun a ↦ (a \ b).card ≤ r
  rw [← card_powersetCard k t]
  calc
    _ ≤ (C.biUnion ball).card :=
      card_le_card fun a ha ↦ by
        obtain ⟨b, hb, hab⟩ := hcover a ha
        exact mem_biUnion.mpr ⟨b, hb, mem_filter.mpr ⟨ha, hab⟩⟩
    _ ≤ _ := card_biUnion_le_card_mul _ _ _ hB

/-- The constant-weight Gilbert bound. Separation is strict in the replacement
radius, which is half the Hamming distance between the incidence vectors. -/
theorem exists_powersetCard_pairwise_lt_card_sdiff (t : Finset α) (k r : ℕ) :
    ∃ C ⊆ t.powersetCard k,
      (C : Set (Finset α)).Pairwise (fun a b ↦ r < (a \ b).card) ∧
      t.card.choose k ≤ C.card * ∑ j ∈ range (r + 1), k.choose j * (t.card - k).choose j := by
  obtain ⟨C, hC, hsep, hcover⟩ := t.exists_powersetCard_pairwise_lt_card_sdiff_cover k r
  refine ⟨C, hC, hsep, choose_le_card_mul_of_powersetCard_cover hcover fun b hb ↦ ?_⟩
  obtain ⟨hbt, hbk⟩ := mem_powersetCard.mp (hC hb)
  exact (card_filter_powersetCard_card_sdiff_le hbt hbk r).le

/-- A packing separated by more than k - m replacements has a lower cardinality bound
obtained by counting extensions of m-subsets of each centre. -/
theorem exists_powersetCard_pairwise_lt_card_sdiff_choose_le (t : Finset α) {k m : ℕ}
    (hm : m ≤ k) (hk : k ≤ t.card) :
    ∃ C ⊆ t.powersetCard k,
      (C : Set (Finset α)).Pairwise (fun a b ↦ k - m < (a \ b).card) ∧
      t.card.choose m ≤ C.card * (k.choose m) ^ 2 := by
  obtain ⟨C, hC, hsep, hcover⟩ := t.exists_powersetCard_pairwise_lt_card_sdiff_cover k (k - m)
  refine ⟨C, hC, hsep, ?_⟩
  have hcount : t.card.choose k ≤ C.card * (k.choose m * (t.card - m).choose (k - m)) :=
    choose_le_card_mul_of_powersetCard_cover hcover fun b hb ↦ by
      exact card_filter_powersetCard_card_sdiff_le_mul_choose (mem_powersetCard.mp (hC hb)).2 hm
  apply Nat.le_of_mul_le_mul_right (c := t.card.choose k) _ (Nat.choose_pos hk)
  calc
    t.card.choose m * t.card.choose k ≤
        t.card.choose m * (C.card * (k.choose m * (t.card - m).choose (k - m))) :=
      Nat.mul_le_mul_left _ hcount
    _ = (t.card.choose m * (t.card - m).choose (k - m)) * (C.card * k.choose m) := by
      ac_rfl
    _ = (C.card * (k.choose m) ^ 2) * t.card.choose k := by
      rw [← Nat.choose_mul hm, pow_two]
      ac_rfl

end Finset
