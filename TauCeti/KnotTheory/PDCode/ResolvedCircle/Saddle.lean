/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Adjacent

/-!
# Fibres of the resolution saddle correspondence

When one target circle passes through a changed crossing, the saddle correspondence collapses
all source circles through that crossing and is a bijection elsewhere. This file characterizes
its fibres and extends it to all resolved circles, retaining every crossing-free circle label.
The only possible collision is between the source circles in slots `0` and `2`. When these
circles are distinct, the correspondence is exactly a merge of two circles, and the total
circle count decreases by one. These facts identify the factors multiplied by a resolution
saddle on indexed circle tensors.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
-/

public section

namespace TauCeti.PDCode

open Finset

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (ht : #(D.circlesAt t c) = 1)

/-- A source circle meets the changed crossing exactly when its image does. -/
@[simp]
theorem saddleCircleMap_mem_circlesAt_iff (C : D.CrossingCircle s) :
    D.saddleCircleMap hst ht C ∈ D.circlesAt t c ↔ C ∈ D.circlesAt s c := by
  constructor
  · intro h
    by_contra hC
    rw [D.saddleCircleMap_of_notMem hst ht hC] at h
    exact (D.unchangedCircleEquiv hst ⟨C, hC⟩).2 h
  · intro hC
    rw [← D.image_saddleCircleMap_circlesAt hst ht]
    exact mem_image_of_mem _ hC

/-- Two source circles have the same saddle image exactly when they coincide or both meet the
changed crossing. -/
theorem saddleCircleMap_eq_iff (C C' : D.CrossingCircle s) :
    D.saddleCircleMap hst ht C = D.saddleCircleMap hst ht C' ↔
      C = C' ∨ C ∈ D.circlesAt s c ∧ C' ∈ D.circlesAt s c := by
  constructor
  · intro h
    by_cases hC : C ∈ D.circlesAt s c
    · exact Or.inr ⟨hC, (D.saddleCircleMap_mem_circlesAt_iff hst ht C').mp
        (h ▸ (D.saddleCircleMap_mem_circlesAt_iff hst ht C).mpr hC)⟩
    · have hC' : C' ∉ D.circlesAt s c := by
        intro hC'
        exact hC ((D.saddleCircleMap_mem_circlesAt_iff hst ht C).mp
          (h ▸ (D.saddleCircleMap_mem_circlesAt_iff hst ht C').mpr hC'))
      rw [D.saddleCircleMap_of_notMem hst ht hC,
        D.saddleCircleMap_of_notMem hst ht hC'] at h
      exact Or.inl (congrArg Subtype.val ((D.unchangedCircleEquiv hst).injective
        (Subtype.ext h)))
  · rintro (rfl | ⟨hC, hC'⟩)
    · rfl
    · exact card_le_one.mp (by omega : #(D.circlesAt t c) ≤ 1) _
        ((D.saddleCircleMap_mem_circlesAt_iff hst ht C).mpr hC) _
        ((D.saddleCircleMap_mem_circlesAt_iff hst ht C').mpr hC')

/-- The saddle correspondence on all resolved circles. It preserves each crossing-free label. -/
def saddleResolvedCircleMap : D.ResolvedCircle s → D.ResolvedCircle t :=
  Sum.map (D.saddleCircleMap hst ht) id

/-- On a crossing-bearing circle, the full saddle map is the half-edge quotient map. -/
@[simp]
theorem saddleResolvedCircleMap_inl (C : D.CrossingCircle s) :
    D.saddleResolvedCircleMap hst ht (.inl C) = .inl (D.saddleCircleMap hst ht C) :=
  (rfl)

/-- Crossing-free circles retain their labels under the saddle. -/
@[simp]
theorem saddleResolvedCircleMap_inr (i : Fin D.crossinglessComponentCount) :
    D.saddleResolvedCircleMap hst ht (.inr i) = .inr i := (rfl)

/-- Every target resolved circle is hit by the saddle. -/
theorem saddleResolvedCircleMap_surjective :
    Function.Surjective (D.saddleResolvedCircleMap hst ht) :=
  Sum.map_surjective.mpr ⟨D.saddleCircleMap_surjective hst ht, Function.surjective_id⟩

/-- The only possible distinct circles identified by the full saddle map are the two circles
through the changed crossing, represented by slots `0` and `2`. -/
theorem saddleResolvedCircleMap_eq_iff (C C' : D.ResolvedCircle s) :
    D.saddleResolvedCircleMap hst ht C = D.saddleResolvedCircleMap hst ht C' ↔
      C = C' ∨
        (C = .inl ⟦D.crossing c 0⟧ ∨ C = .inl ⟦D.crossing c 2⟧) ∧
        (C' = .inl ⟦D.crossing c 0⟧ ∨ C' = .inl ⟦D.crossing c 2⟧) := by
  cases C <;> cases C' <;>
    simp [D.saddleCircleMap_eq_iff hst ht, D.circlesAt_eq_pair, eq_comm]

/-- The fibre over the target circle through the crossing consists of the source circles
through slots `0` and `2`. -/
theorem saddleResolvedCircleMap_eq_crossing_iff (C : D.ResolvedCircle s) :
    D.saddleResolvedCircleMap hst ht C = .inl ⟦D.crossing c 0⟧ ↔
      C = .inl ⟦D.crossing c 0⟧ ∨ C = .inl ⟦D.crossing c 2⟧ := by
  have hmap : D.saddleResolvedCircleMap hst ht (.inl ⟦D.crossing c 0⟧) =
      .inl ⟦D.crossing c 0⟧ := by simp
  rw [← hmap, D.saddleResolvedCircleMap_eq_iff hst ht]
  tauto

/-- As a finite set, the fibre through the crossing is the pair of source circles in opposite
slots; repeated entries are counted only once. -/
theorem filter_saddleResolvedCircleMap_eq_crossing :
    (univ.filter fun C ↦ D.saddleResolvedCircleMap hst ht C = .inl ⟦D.crossing c 0⟧) =
      ({.inl ⟦D.crossing c 0⟧, .inl ⟦D.crossing c 2⟧} : Finset (D.ResolvedCircle s)) := by
  apply Finset.ext
  intro C
  simpa only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] using
    D.saddleResolvedCircleMap_eq_crossing_iff hst ht C

/-- The product over the changed fibre is the product of the two merged factors. -/
theorem prod_filter_saddleResolvedCircleMap_eq_crossing {M : Type*} [CommMonoid M]
    (hs : #(D.circlesAt s c) = 2) (x : D.ResolvedCircle s → M) :
    (∏ C' with D.saddleResolvedCircleMap hst ht C' = .inl ⟦D.crossing c 0⟧, x C') =
      x (.inl ⟦D.crossing c 0⟧) * x (.inl ⟦D.crossing c 2⟧) := by
  rw [D.filter_saddleResolvedCircleMap_eq_crossing]
  exact prod_pair (fun h ↦ (D.card_circlesAt_eq_two_iff s c).mp hs (Sum.inl.inj h))

/-- The product over an unchanged fibre is its sole source factor. This includes every
crossing-free circle. -/
theorem prod_filter_saddleResolvedCircleMap_eq_of_ne {M : Type*} [CommMonoid M]
    (C : D.ResolvedCircle s) (hC₀ : C ≠ .inl ⟦D.crossing c 0⟧)
    (hC₂ : C ≠ .inl ⟦D.crossing c 2⟧) (x : D.ResolvedCircle s → M) :
    (∏ C' with D.saddleResolvedCircleMap hst ht C' =
      D.saddleResolvedCircleMap hst ht C, x C') = x C := by
  have hf : (univ.filter fun C' ↦ D.saddleResolvedCircleMap hst ht C' =
      D.saddleResolvedCircleMap hst ht C) = {C} := by
    ext C'
    simp only [mem_filter, mem_univ, true_and, D.saddleResolvedCircleMap_eq_iff hst ht,
      hC₀, hC₂, or_self, and_false, or_false, mem_singleton]
  rw [hf, prod_singleton]

/-- The target label at the changed circle is the Boolean disjunction of the two source labels.
This describes label transport even when the two source circles coincide. -/
@[simp↓]
theorem decide_exists_saddleResolvedCircleMap_eq_crossing (l : D.ResolvedCircle s → Bool) :
    decide (∃ C', D.saddleResolvedCircleMap hst ht C' = .inl ⟦D.crossing c 0⟧ ∧
      l C' = true) = (l (.inl ⟦D.crossing c 0⟧) || l (.inl ⟦D.crossing c 2⟧)) := by
  simp only [D.saddleResolvedCircleMap_eq_crossing_iff hst ht, or_and_right, exists_or,
    exists_eq_left]
  simp

/-- A crossing-bearing circle avoiding the changed crossing retains its Boolean label. -/
@[simp↓]
theorem decide_exists_saddleResolvedCircleMap_eq_of_notMem (l : D.ResolvedCircle s → Bool)
    (C : D.CrossingCircle s) (hC : C ∉ D.circlesAt s c) :
    decide (∃ C', D.saddleResolvedCircleMap hst ht C' =
      D.saddleResolvedCircleMap hst ht (.inl C) ∧ l C' = true) = l (.inl C) := by
  have hC₀ : (Sum.inl C : D.ResolvedCircle s) ≠ .inl ⟦D.crossing c 0⟧ :=
    fun h ↦ hC (Sum.inl.inj h ▸ D.mk_crossing_mem_circlesAt s c 0)
  have hC₂ : (Sum.inl C : D.ResolvedCircle s) ≠ .inl ⟦D.crossing c 2⟧ :=
    fun h ↦ hC (Sum.inl.inj h ▸ D.mk_crossing_mem_circlesAt s c 2)
  simp only [D.saddleResolvedCircleMap_eq_iff hst ht, hC₀, hC₂, or_self, and_false, or_false]
  simp

/-- Away from the merged target circle every fibre is a singleton. -/
theorem existsUnique_saddleResolvedCircleMap_eq (C : D.ResolvedCircle t)
    (hC : C ≠ .inl ⟦D.crossing c 0⟧) :
    ∃! C', D.saddleResolvedCircleMap hst ht C' = C := by
  obtain ⟨C', rfl⟩ := D.saddleResolvedCircleMap_surjective hst ht C
  refine ⟨C', rfl, fun C'' h ↦ ?_⟩
  rcases (D.saddleResolvedCircleMap_eq_iff hst ht C'' C').mp h with h | ⟨_, h'⟩
  · exact h
  · exact False.elim (hC ((D.saddleResolvedCircleMap_eq_crossing_iff hst ht C').mpr h'))

include hst ht in
/-- A two-to-one saddle reduces the total number of circles by one, including isolated circles. -/
theorem card_resolvedCircle_source_eq_target_add_one (hs : #(D.circlesAt s c) = 2) :
    Fintype.card (D.ResolvedCircle s) = Fintype.card (D.ResolvedCircle t) + 1 := by
  have h := D.stateLoopCount_add_card_circlesAt hst
  rw [card_resolvedCircle, card_resolvedCircle]
  omega

end TauCeti.PDCode
