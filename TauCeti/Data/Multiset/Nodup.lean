/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.MapFold

/-!
# Equality of duplicate-free multisets from list enumerations

If a duplicate-free multiset `s` has the same elements as the image of a duplicate-free list `l`
under a map `f` that is injective on the elements of `l`, then `s` equals
`(Multiset.ofList l).map f`.
-/

public section

namespace Multiset

/-- A duplicate-free multiset whose elements are exactly the values `f a` for `a ∈ l`, where `l`
has no duplicates and `f` is injective on `l`, equals `(Multiset.ofList l).map f`. -/
theorem eq_map_of_mem_iff_of_nodup {α β : Type*} {s : Multiset β} {l : List α} {f : α → β}
    (hs : s.Nodup) (hl : l.Nodup) (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (hmem : ∀ b, b ∈ s ↔ ∃ a ∈ l, f a = b) : s = (Multiset.ofList l).map f := by
  refine (Nodup.ext hs (Nodup.map_on (fun x hx y hy ↦ hf x hx y hy) (coe_nodup.mpr hl))).mpr
    fun b ↦ ?_
  simp [hmem]

end Multiset
