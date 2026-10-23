/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Ring
import TauCeti.Order.Partition.Finpartition

/-!
# Maps into the parts of a finite partition

Let `P` be a finite partition of a finset `s` and let `ι` be a finite index type. A map
`g : ι → α` with values in `s` has a *cell assignment* `i ↦ P.part (g i)`, and the maps whose cell
assignment is a given `φ : ι → P.parts` form the box `Fintype.piFinset fun i ↦ φ i`. These boxes
partition the maps `ι → s`, so sums over such maps split along cell assignments.

Counting lemmas for regular partitions treat the maps whose coordinates lie in distinct parts
separately from the rest: a map with an injective cell assignment is itself injective, while the
maps putting two coordinates in a common part are few when all parts are small. This file
supplies both facts.

## Main results

* `Finpartition.sum_sum_piFinset_parts`: a sum over maps `ι → s` splits along cell assignments.
* `Finpartition.sum_piFinset_apply_part`: a sum over maps `ι → s` of a function of their cell
  assignments weights each cell assignment by the size of its box.
* `Finpartition.injective_of_mem_piFinset_parts`: a map in the box of an injective cell assignment
  is injective.
* `Finpartition.card_filter_not_injective_part_le`: at most
  `(card ι).choose 2 * #s ^ (card ι - 2) * ∑ A ∈ P.parts, #A ^ 2` maps `ι → s` have a
  non-injective cell assignment.
* `Finpartition.sum_prod_card_of_not_injective_le`: the same bound for the total size of the boxes
  of non-injective cell assignments.
* `Finpartition.sum_prod_card_of_not_injective_le_of_card_le`: when all parts have size at most
  `m`, these boxes have total size at most `(card ι).choose 2 * m * #s ^ (card ι - 1)`.
-/

public section

open Finset Function

namespace Finpartition

variable {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι] {s : Finset α}
  (P : Finpartition s)

/-- The boxes of distinct cell assignments are disjoint. -/
theorem pairwiseDisjoint_piFinset_parts :
    ((univ : Finset (ι → P.parts)) : Set (ι → P.parts)).PairwiseDisjoint
      fun φ ↦ Fintype.piFinset fun i ↦ (φ i : Finset α) := by
  intro φ _ ψ _ hφψ
  obtain ⟨i, hi⟩ := ne_iff.1 hφψ
  exact Fintype.piFinset_disjoint_of_disjoint _ _
    (P.disjoint (φ i).2 (ψ i).2 (Subtype.coe_ne_coe.2 hi))

/-- The boxes of all cell assignments cover the maps `ι → s`. -/
theorem biUnion_piFinset_parts :
    (univ : Finset (ι → P.parts)).biUnion (fun φ ↦ Fintype.piFinset fun i ↦ (φ i : Finset α)) =
      Fintype.piFinset fun _ : ι ↦ s := by
  ext g
  simp only [mem_biUnion, mem_univ, true_and, Fintype.mem_piFinset]
  exact ⟨fun ⟨φ, hφ⟩ i ↦ P.le (φ i).2 (hφ i),
    fun hg ↦ ⟨fun i ↦ ⟨P.part (g i), P.part_mem.2 (hg i)⟩, fun i ↦ P.mem_part (hg i)⟩⟩

/-- A sum over the maps `ι → s` splits along cell assignments. -/
theorem sum_sum_piFinset_parts {M : Type*} [AddCommMonoid M] (f : (ι → α) → M) :
    ∑ φ : ι → P.parts, ∑ g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset α)), f g =
      ∑ g ∈ Fintype.piFinset (fun _ : ι ↦ s), f g := by
  rw [← P.biUnion_piFinset_parts, sum_biUnion P.pairwiseDisjoint_piFinset_parts]

/-- The maps `ι → s` with a given property are counted along cell assignments. -/
theorem sum_card_filter_piFinset_parts (p : (ι → α) → Prop) [DecidablePred p] :
    ∑ φ : ι → P.parts, #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset α)) | p g} =
      #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) | p g} := by
  simpa only [card_filter] using P.sum_sum_piFinset_parts fun g ↦ if p g then 1 else 0

/-- A map in the box of an injective cell assignment is injective. -/
theorem injective_of_mem_piFinset_parts {φ : ι → P.parts} (hφ : Injective φ) {g : ι → α}
    (hg : g ∈ Fintype.piFinset fun i ↦ (φ i : Finset α)) : Injective g := by
  intro i j hij
  rw [Fintype.mem_piFinset] at hg
  exact hφ <| Subtype.ext <| P.eq_of_mem_parts (φ i).2 (φ j).2 (hg i) (hij ▸ hg j)

/-- On the box of a cell assignment `φ`, the cell assignment of each map is `φ`. -/
theorem part_eq_of_mem_piFinset_parts {φ : ι → P.parts} {g : ι → α}
    (hg : g ∈ Fintype.piFinset fun i ↦ (φ i : Finset α)) (i : ι) : P.part (g i) = φ i :=
  P.part_eq_of_mem (φ i).2 (Fintype.mem_piFinset.1 hg i)

/-- A sum over the maps `ι → s` of a function of their cell assignments counts each cell
assignment `φ` with the size `∏ i, #(φ i)` of its box. -/
theorem sum_piFinset_apply_part {M : Type*} [AddCommMonoid M] (f : (ι → Finset α) → M) :
    ∑ g ∈ Fintype.piFinset (fun _ : ι ↦ s), f (fun i ↦ P.part (g i)) =
      ∑ φ : ι → P.parts, (∏ i, #(φ i : Finset α)) • f (fun i ↦ φ i) := by
  rw [← P.sum_sum_piFinset_parts]
  refine sum_congr rfl fun φ _ ↦ ?_
  rw [sum_congr rfl fun g hg ↦ by rw [funext (P.part_eq_of_mem_piFinset_parts hg)], sum_const,
    Fintype.card_piFinset]

/-- At most `#s ^ (card ι - 2) * ∑ A ∈ P.parts, #A ^ 2` maps `ι → s` send two given distinct
coordinates to a common part. -/
theorem card_filter_part_eq_part_le {i j : ι} (hij : i ≠ j) :
    #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) | P.part (g i) = P.part (g j)} ≤
      #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by
  -- Such a map lies in the box with the part `A` of `g i` at `i` and `j`, and `s` elsewhere.
  set box : Finset α → Finset (ι → α) :=
    fun A ↦ Fintype.piFinset fun l ↦ if l = i ∨ l = j then A else s
  have hpair : #({l | l = i ∨ l = j} : Finset ι) = 2 := by
    rw [← card_pair hij]
    congr 1
    ext l
    simp
  have hrest := card_filter_add_card_filter_not (s := (univ : Finset ι)) fun l ↦ l = i ∨ l = j
  rw [hpair, card_univ] at hrest
  calc #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) | P.part (g i) = P.part (g j)}
      ≤ #(P.parts.biUnion box) := by
        refine card_le_card fun g hg ↦ ?_
        rw [mem_filter, Fintype.mem_piFinset] at hg
        refine mem_biUnion.2 ⟨P.part (g i), P.part_mem.2 (hg.1 i), Fintype.mem_piFinset.2 ?_⟩
        intro l
        split_ifs with hl
        · rcases hl with rfl | rfl
          · exact P.mem_part (hg.1 l)
          · exact hg.2 ▸ P.mem_part (hg.1 l)
        · exact hg.1 l
    _ ≤ ∑ A ∈ P.parts, #(box A) := card_biUnion_le
    _ = ∑ A ∈ P.parts, #A ^ 2 * #s ^ (Fintype.card ι - 2) := by
        refine sum_congr rfl fun A _ ↦ ?_
        simp only [box, Fintype.card_piFinset, apply_ite card, prod_ite, prod_const, hpair]
        congr 2
        omega
    _ = #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by rw [← sum_mul, mul_comm]

/-- At most `(card ι).choose 2 * #s ^ (card ι - 2) * ∑ A ∈ P.parts, #A ^ 2` maps `ι → s` send two
distinct coordinates to a common part. -/
theorem card_filter_not_injective_part_le :
    #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) | ¬Injective fun i ↦ P.part (g i)} ≤
      (Fintype.card ι).choose 2 * #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by
  -- Union bound over the pairs of coordinates sent to a common part.
  calc #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) | ¬Injective fun i ↦ P.part (g i)}
      ≤ ∑ t ∈ (univ : Finset ι).powersetCard 2,
          #{g ∈ Fintype.piFinset (fun _ : ι ↦ s) |
            ∀ i ∈ t, ∀ j ∈ t, P.part (g i) = P.part (g j)} := by
        refine (card_le_card fun g hg ↦ ?_).trans card_biUnion_le
        rw [mem_filter] at hg
        obtain ⟨i, j, hgij, hij⟩ := not_injective_iff.1 hg.2
        refine mem_biUnion.2 ⟨{i, j}, mem_powersetCard.2 ⟨subset_univ _, card_pair hij⟩,
          mem_filter.2 ⟨hg.1, ?_⟩⟩
        simp only [mem_insert, mem_singleton]
        rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hgij]
    _ ≤ ∑ _t ∈ (univ : Finset ι).powersetCard 2,
          #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by
        refine sum_le_sum fun t ht ↦ ?_
        obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 (mem_powersetCard.1 ht).2
        refine le_trans (card_le_card fun g hg ↦ ?_) (P.card_filter_part_eq_part_le hij)
        rw [mem_filter] at hg ⊢
        exact ⟨hg.1, hg.2 i (by simp) j (by simp)⟩
    _ = (Fintype.card ι).choose 2 * #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by
        rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul, Nat.cast_id, mul_assoc]

/-- The boxes of the non-injective cell assignments have total size at most
`(card ι).choose 2 * #s ^ (card ι - 2) * ∑ A ∈ P.parts, #A ^ 2`. -/
theorem sum_prod_card_of_not_injective_le :
    ∑ φ : ι → P.parts with ¬Injective φ, ∏ i, #(φ i : Finset α) ≤
      (Fintype.card ι).choose 2 * #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2 := by
  refine le_trans (le_of_eq ?_) P.card_filter_not_injective_part_le
  rw [← P.sum_card_filter_piFinset_parts, sum_filter]
  refine sum_congr rfl fun φ _ ↦ ?_
  have hinj : Injective φ ↔ Injective fun i ↦ (φ i : Finset α) :=
    (Subtype.val_injective.of_comp_iff φ).symm
  have hpart {g} (hg : g ∈ Fintype.piFinset fun i ↦ (φ i : Finset α)) :
      (fun i ↦ P.part (g i)) = fun i ↦ (φ i : Finset α) :=
    funext (P.part_eq_of_mem_piFinset_parts hg)
  split_ifs with hφ
  · rw [filter_false_of_mem fun g hg ↦ by rwa [hpart hg, ← hinj, not_not], card_empty]
  · rw [filter_true_of_mem fun g hg ↦ by rwa [hpart hg, ← hinj], Fintype.card_piFinset]

/-- If every part of `P` has at most `m` elements, the boxes of the non-injective cell assignments
have total size at most `(card ι).choose 2 * m * #s ^ (card ι - 1)`. -/
theorem sum_prod_card_of_not_injective_le_of_card_le {m : ℕ} (hm : ∀ A ∈ P.parts, #A ≤ m) :
    ∑ φ : ι → P.parts with ¬Injective φ, ∏ i, #(φ i : Finset α) ≤
      (Fintype.card ι).choose 2 * m * #s ^ (Fintype.card ι - 1) := by
  refine P.sum_prod_card_of_not_injective_le.trans ?_
  rcases lt_or_ge (Fintype.card ι) 2 with hι | hι
  · simp [Nat.choose_eq_zero_of_lt hι]
  · calc (Fintype.card ι).choose 2 * #s ^ (Fintype.card ι - 2) * ∑ A ∈ P.parts, #A ^ 2
        ≤ (Fintype.card ι).choose 2 * #s ^ (Fintype.card ι - 2) * (m * #s) := by
          grw [P.sum_sq_card_parts_le hm]
      _ = (Fintype.card ι).choose 2 * m * #s ^ (Fintype.card ι - 1) := by
          rw [show Fintype.card ι - 1 = Fintype.card ι - 2 + 1 by omega, pow_succ]
          ring

end Finpartition
