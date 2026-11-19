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
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Order.Preorder.Finite
import TauCeti.Data.Finset.Powerset

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
theorem card_filter_powersetCard_card_sdiff_eq_choose_mul_choose
    (hst : s ⊆ t) (hs : s.card = k) (m : ℕ) :
    ((t.powersetCard k).filter fun a ↦ (a \ s).card = m).card =
      k.choose m * (t.card - k).choose m := by
  by_cases hm : m ≤ k
  · have hfilter : (t.powersetCard k).filter (fun a ↦ (a \ s).card = m) =
        (t.powersetCard k).filter (fun a ↦ (a ∩ s).card = k - m) := by
      refine filter_congr fun a ha ↦ ?_
      have hcard := (mem_powersetCard.mp ha).2
      have hsum := card_sdiff_add_card_inter a s
      omega
    rw [hfilter, card_filter_powersetCard_card_inter t s (Nat.sub_le k m),
      inter_eq_right.mpr hst, card_sdiff_of_subset hst, hs, Nat.choose_symm hm, Nat.sub_sub_self hm]
  · have hlt := Nat.lt_of_not_ge hm
    have hfilter : (t.powersetCard k).filter (fun a ↦ (a \ s).card = m) = ∅ := by
      refine filter_eq_empty_iff.mpr fun a ha hdist ↦ ?_
      have hcard := (mem_powersetCard.mp ha).2
      have hle := card_le_card (sdiff_subset (s := a) (t := s))
      omega
    simp [hfilter, Nat.choose_eq_zero_of_lt hlt]

/-- The ball of radius r in the constant-weight family, measured in replacements. -/
theorem card_filter_powersetCard_card_sdiff_le_eq_sum
    (hst : s ⊆ t) (hs : s.card = k) (r : ℕ) :
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
  simpa only [heq] using card_filter_powersetCard_card_sdiff_eq_choose_mul_choose hst hs j

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
  exact (card_filter_powersetCard_card_sdiff_le_eq_sum hbt hbk r).le

/-- There is a family `C` of `k`-subsets of `t` pairwise separated by more than `k - m`
replacements and satisfying `t.card.choose m ≤ C.card * (k.choose m) ^ 2`.
The bound comes from counting extensions of `m`-subsets of each centre. -/
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
