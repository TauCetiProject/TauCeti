/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.OrderIso

/-!
# Finite supports, order-isomorphism transport, and translation of nonempty intervals

`NonemptyInterval α` in `Mathlib.Order.Interval.Basic` packages a pair of endpoints `s.fst ≤ s.snd`
ordered by set inclusion `(s : Set α) ⊆ (t : Set α)`. When `α` is a `LocallyFiniteOrder`, the points
of `s` form the nonempty `Finset` `Finset.Icc s.fst s.snd`; this file exposes that finite support as
`NonemptyInterval.toFinset` together with its inclusion, injectivity, and cardinality API. Notice
that `#s.toFinset` counts the points in `s` (for `α = ℤ`, `(s.snd + 1 - s.fst).toNat`), whereas
`NonemptyInterval.length` in `Mathlib.Algebra.Order.Interval.Basic` is the endpoint difference
`s.snd - s.fst`.

This file also upgrades `NonemptyInterval.map` along an `OrderIso` `e : α ≃o β` to an order
isomorphism `NonemptyInterval.orderIsoCongr e : NonemptyInterval α ≃o NonemptyInterval β` preserving
finite-support cardinalities, and defines right additive translation `NonemptyInterval.shift s c`
sending `[a, b]` to `[a + c, b + c]`.

## Main definitions

* `NonemptyInterval.toFinset`: the finite closed interval `Finset.Icc s.fst s.snd` of points in `s`.
* `NonemptyInterval.orderIsoCongr`: transport of nonempty intervals along an order isomorphism as an
  `OrderIso`.
* `NonemptyInterval.shift`: right translation `[a, b] ↦ [a + c, b + c]` of a nonempty interval.
-/

public section

open Finset Function

namespace NonemptyInterval

/-- Membership in a nonempty interval `[a, b]` is decidable whenever `≤` is decidable. -/
instance instDecidableMem {α : Type*} [Preorder α] [DecidableLE α] (x : α)
    (s : NonemptyInterval α) : Decidable (x ∈ s) :=
  decidable_of_iff' (s.fst ≤ x ∧ x ≤ s.snd) mem_def

theorem eq_pure_iff_fst_eq_snd {α : Type*} [Preorder α] {s : NonemptyInterval α} {a : α} :
    s = pure a ↔ s.fst = a ∧ s.snd = a := by
  rw [NonemptyInterval.ext_iff, Prod.ext_iff, pure_fst, pure_snd]

section LocallyFiniteOrder

variable {α : Type*}

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {s t : NonemptyInterval α} {x : α}

/-- The finite set `Finset.Icc s.fst s.snd` of points belonging to a nonempty interval `s` in a
locally finite order. -/
def toFinset (s : NonemptyInterval α) : Finset α :=
  Icc s.fst s.snd

theorem toFinset_def (s : NonemptyInterval α) : s.toFinset = Icc s.fst s.snd :=
  (rfl)

@[simp]
theorem mem_toFinset : x ∈ s.toFinset ↔ x ∈ s := by
  rw [toFinset_def, Finset.mem_Icc, mem_def]

theorem fst_mem_toFinset (s : NonemptyInterval α) : s.fst ∈ s.toFinset :=
  mem_toFinset.mpr ⟨le_rfl, s.fst_le_snd⟩

theorem snd_mem_toFinset (s : NonemptyInterval α) : s.snd ∈ s.toFinset :=
  mem_toFinset.mpr ⟨s.fst_le_snd, le_rfl⟩

@[simp]
theorem toFinset_nonempty (s : NonemptyInterval α) : s.toFinset.Nonempty :=
  ⟨s.fst, s.fst_mem_toFinset⟩

theorem card_toFinset_pos (s : NonemptyInterval α) : 0 < #s.toFinset :=
  s.toFinset_nonempty.card_pos

@[simp]
theorem toFinset_subset_toFinset : s.toFinset ⊆ t.toFinset ↔ s ≤ t := by
  rw [toFinset_def, toFinset_def, Finset.Icc_subset_Icc_iff s.fst_le_snd, le_def]

theorem toFinset_mono : Monotone (toFinset : NonemptyInterval α → Finset α) :=
  fun _ _ h => toFinset_subset_toFinset.mpr h

theorem card_toFinset_mono (h : s ≤ t) : #s.toFinset ≤ #t.toFinset :=
  Finset.card_le_card (toFinset_subset_toFinset.mpr h)

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {s t : NonemptyInterval α}

@[simp]
theorem coe_toFinset (s : NonemptyInterval α) : (s.toFinset : Set α) = (s : Set α) := by
  rw [toFinset_def, coe_Icc, coe_def]

@[simp]
theorem toFinset_pure (a : α) : (pure a).toFinset = {a} := by
  rw [toFinset_def, pure_fst, pure_snd, Icc_self]

@[simp]
theorem toFinset_ssubset_toFinset : s.toFinset ⊂ t.toFinset ↔ s < t := by
  rw [← Finset.coe_ssubset, coe_toFinset, coe_toFinset, coe_ssubset_coe]

theorem toFinset_strictMono : StrictMono (toFinset : NonemptyInterval α → Finset α) :=
  fun _ _ h => toFinset_ssubset_toFinset.mpr h

theorem toFinset_injective : Injective (toFinset : NonemptyInterval α → Finset α) := by
  intro s t h
  exact SetLike.coe_injective (by rw [← coe_toFinset, ← coe_toFinset, h])

@[simp]
theorem toFinset_inj : s.toFinset = t.toFinset ↔ s = t :=
  toFinset_injective.eq_iff

theorem card_toFinset_strictMono (h : s < t) : #s.toFinset < #t.toFinset :=
  Finset.card_lt_card (toFinset_ssubset_toFinset.mpr h)

/-- A nonempty interval in a locally finite partial order has a single point if and only if its two
endpoints coincide. -/
theorem card_toFinset_eq_one_iff : #s.toFinset = 1 ↔ s.fst = s.snd := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Finset.card_le_one.mp h.le s.fst s.fst_mem_toFinset s.snd s.snd_mem_toFinset
  · have hs : s = pure s.fst := eq_pure_iff_fst_eq_snd.mpr ⟨rfl, h.symm⟩
    rw [hs, toFinset_pure, card_singleton]

/-- A nonempty interval in a locally finite partial order has more than one point if and only if its
left endpoint is strictly less than its right endpoint. -/
theorem one_lt_card_toFinset_iff : 1 < #s.toFinset ↔ s.fst < s.snd := by
  have hpos := s.card_toFinset_pos
  rw [s.fst_le_snd.lt_iff_ne, ← not_iff_not, not_ne_iff, ← card_toFinset_eq_one_iff]
  omega

end PartialOrder

end LocallyFiniteOrder

section OrderIso

variable {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]

/-- Transport nonempty intervals along an order isomorphism `e : α ≃o β` as an order isomorphism
with respect to inclusion. -/
def orderIsoCongr (e : α ≃o β) : NonemptyInterval α ≃o NonemptyInterval β where
  toFun s := s.map (e : α →o β)
  invFun s := s.map (e.symm : β →o α)
  left_inv s := by
    ext <;> simp
  right_inv s := by
    ext <;> simp
  map_rel_iff' := by
    intro s t
    simp [le_def]

@[simp]
theorem orderIsoCongr_apply (e : α ≃o β) (s : NonemptyInterval α) :
    orderIsoCongr e s = s.map (e : α →o β) :=
  (rfl)

@[simp]
theorem orderIsoCongr_symm (e : α ≃o β) :
    (orderIsoCongr e).symm = orderIsoCongr e.symm :=
  (rfl)

@[simp]
theorem orderIsoCongr_refl :
    orderIsoCongr (OrderIso.refl α) = OrderIso.refl (NonemptyInterval α) := by
  ext : 1
  ext <;> rfl

theorem orderIsoCongr_trans (e : α ≃o β) (e' : β ≃o γ) :
    orderIsoCongr (e.trans e') = (orderIsoCongr e).trans (orderIsoCongr e') := by
  ext : 1
  ext <;> rfl

theorem mem_map_orderIso (e : α ≃o β) {s : NonemptyInterval α} {b : β} :
    b ∈ s.map (e : α →o β) ↔ e.symm b ∈ s := by
  simp [mem_def, e.le_symm_apply, e.symm_apply_le]

@[simp]
theorem apply_mem_map_orderIso (e : α ≃o β) {s : NonemptyInterval α} {a : α} :
    e a ∈ s.map (e : α →o β) ↔ a ∈ s := by
  rw [mem_map_orderIso, e.symm_apply_apply]

@[simp]
theorem map_orderIso_le_map_orderIso (e : α ≃o β) {s t : NonemptyInterval α} :
    s.map (e : α →o β) ≤ t.map (e : α →o β) ↔ s ≤ t :=
  (orderIsoCongr e).le_iff_le

theorem map_orderIso_injective (e : α ≃o β) :
    Injective (map (e : α →o β) : NonemptyInterval α → NonemptyInterval β) :=
  (orderIsoCongr e).injective

@[simp]
theorem coe_map_orderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) (s : NonemptyInterval α) :
    ((s.map (e : α →o β) : NonemptyInterval β) : Set β) = e '' (s : Set α) :=
  (e.image_Icc s.fst s.snd).symm

theorem toFinset_map_orderIso [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    (e : α ≃o β) (s : NonemptyInterval α) :
    (s.map (e : α →o β)).toFinset = s.toFinset.map e.toEquiv.toEmbedding := by
  ext b
  rw [mem_toFinset, mem_map_equiv, mem_toFinset]
  exact mem_map_orderIso e

@[simp]
theorem card_toFinset_map_orderIso [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    (e : α ≃o β) (s : NonemptyInterval α) :
    #(s.map (e : α →o β)).toFinset = #s.toFinset := by
  rw [toFinset_map_orderIso, Finset.card_map]

end OrderIso

section Shift

variable {α : Type*}

section Add

variable [Preorder α] [Add α] [AddRightMono α]

/-- Translate a nonempty interval on the right by `c`, sending `[a, b]` to `[a + c, b + c]`. -/
def shift (s : NonemptyInterval α) (c : α) : NonemptyInterval α :=
  s.map ⟨(· + c), fun _ _ h => add_le_add_left h c⟩

theorem shift_def (s : NonemptyInterval α) (c : α) :
    s.shift c = s.map ⟨(· + c), fun _ _ h => add_le_add_left h c⟩ :=
  (rfl)

@[simp]
theorem fst_shift (s : NonemptyInterval α) (c : α) : (s.shift c).fst = s.fst + c :=
  (rfl)

@[simp]
theorem snd_shift (s : NonemptyInterval α) (c : α) : (s.shift c).snd = s.snd + c :=
  (rfl)

@[simp]
theorem pure_shift (a c : α) : (pure a).shift c = pure (a + c) :=
  (rfl)

theorem shift_mono {s t : NonemptyInterval α} (c : α) (h : s ≤ t) : s.shift c ≤ t.shift c :=
  ⟨add_le_add_left h.1 c, add_le_add_left h.2 c⟩

end Add

@[simp]
theorem shift_zero [AddZeroClass α] [Preorder α] [AddRightMono α] (s : NonemptyInterval α) :
    s.shift 0 = s := by
  ext <;> simp

theorem shift_shift [AddSemigroup α] [Preorder α] [AddRightMono α]
    (s : NonemptyInterval α) (c d : α) :
    (s.shift c).shift d = s.shift (c + d) := by
  ext <;> simp [add_assoc]

section AddGroup

variable [AddGroup α] [Preorder α] [AddRightMono α]

/-- In an ordered additive group, `NonemptyInterval.shift` agrees with transport along
`OrderIso.addRight c`. -/
theorem shift_eq_map_orderIso (s : NonemptyInterval α) (c : α) :
    s.shift c = s.map (OrderIso.addRight c : α →o α) :=
  (rfl)

@[simp]
theorem shift_neg_cancel_right (s : NonemptyInterval α) (c : α) :
    (s.shift c).shift (-c) = s := by
  rw [shift_shift, add_neg_cancel, shift_zero]

@[simp]
theorem neg_shift_cancel_right (s : NonemptyInterval α) (c : α) :
    (s.shift (-c)).shift c = s := by
  rw [shift_shift, neg_add_cancel, shift_zero]

theorem mem_shift_iff {s : NonemptyInterval α} {a c : α} :
    a ∈ s.shift c ↔ a - c ∈ s := by
  rw [shift_eq_map_orderIso, mem_map_orderIso]
  simp [sub_eq_add_neg]

@[simp]
theorem add_mem_shift_iff {s : NonemptyInterval α} {a c : α} :
    a + c ∈ s.shift c ↔ a ∈ s := by
  rw [shift_eq_map_orderIso]
  exact apply_mem_map_orderIso (OrderIso.addRight c)

@[simp]
theorem shift_le_shift_iff {s t : NonemptyInterval α} {c : α} :
    s.shift c ≤ t.shift c ↔ s ≤ t := by
  rw [shift_eq_map_orderIso, shift_eq_map_orderIso, map_orderIso_le_map_orderIso]

theorem shift_injective (c : α) : Injective (fun s : NonemptyInterval α => s.shift c) :=
  map_orderIso_injective (OrderIso.addRight c)

@[simp]
theorem shift_inj {s t : NonemptyInterval α} {c : α} :
    s.shift c = t.shift c ↔ s = t :=
  (shift_injective c).eq_iff

theorem toFinset_shift [LocallyFiniteOrder α] (s : NonemptyInterval α) (c : α) :
    (s.shift c).toFinset = s.toFinset.map (addRightEmbedding c) := by
  rw [shift_eq_map_orderIso, toFinset_map_orderIso]
  congr 1

@[simp]
theorem card_toFinset_shift [LocallyFiniteOrder α] (s : NonemptyInterval α) (c : α) :
    #(s.shift c).toFinset = #s.toFinset := by
  rw [shift_eq_map_orderIso, card_toFinset_map_orderIso]

end AddGroup

end Shift

section Int

/-- The number of integer points in a nonempty integer interval `[a, b]` is `(b + 1 - a).toNat`. -/
theorem card_toFinset_int (s : NonemptyInterval ℤ) :
    #s.toFinset = (s.snd + 1 - s.fst).toNat :=
  Int.card_Icc s.fst s.snd

/-- As an integer, the number of points in `[a, b]` is `b - a + 1`. -/
theorem natCast_card_toFinset_int (s : NonemptyInterval ℤ) :
    (#s.toFinset : ℤ) = s.snd - s.fst + 1 := by
  have h := s.fst_le_snd
  rw [card_toFinset_int]
  omega

end Int

end NonemptyInterval
