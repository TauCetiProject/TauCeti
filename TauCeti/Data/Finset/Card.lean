/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-!
# Downward induction on the subsets of a finset

* `Finset.card_sdiff_insert_add_one`: adding an element `a ∈ T \ S` to `S` lowers the number of
  elements of `T` outside `S` by one.
* `Finset.subset_induction`: downward induction on `S ⊆ T`, from `T` itself and steps from
  `S ∪ {a}` to `S`. Mathlib's `Finset.induction_on'` is the upward analogue.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- Adding an element `a ∈ T \ S` to `S` lowers the number of elements of `T` outside `S` by
one. -/
theorem card_sdiff_insert_add_one {S T : Finset ι} {a : ι} (ha : a ∈ T \ S) :
    #(T \ insert a S) + 1 = #(T \ S) := by
  rw [sdiff_insert, card_erase_add_one ha]

/-- Downward induction on `S ⊆ T`: a property holding at `T`, and passing from `S ∪ {a}` to `S`,
holds for every `S ⊆ T`. -/
theorem subset_induction {T : Finset ι} {P : ∀ S, S ⊆ T → Prop}
    (self : P T Subset.rfl)
    (step : ∀ S a, a ∉ S → ∀ h : insert a S ⊆ T,
      P (insert a S) h → P S ((S.subset_insert a).trans h)) (S : Finset ι) (h : S ⊆ T) :
    P S h := by
  induction hk : #(T \ S) generalizing S with
  | zero =>
    obtain rfl := Subset.antisymm h (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))
    exact self
  | succ k ih =>
    obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #(T \ S))
    have h' : insert a S ⊆ T := insert_subset (mem_sdiff.1 ha).1 h
    exact step S a (mem_sdiff.1 ha).2 h'
      (ih _ h' (by have := card_sdiff_insert_add_one ha; omega))

end Finset
