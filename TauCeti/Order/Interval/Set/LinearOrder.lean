/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Set difference of intervals in a linear order

Removing a nested open interval `(c, d)` from `[a, b]` leaves the union `[a, c] ∪ [d, b]`
(`Set.Icc_sdiff_Ioo`).

## Main results

* `Set.Icc_sdiff_Ioo`: for `a ≤ c ≤ d ≤ b`, `Icc a b \ Ioo c d = Icc a c ∪ Icc d b`.
-/

public section

namespace Set

/-- Removing the open subinterval `(c, d)` from `[a, b]` when `a ≤ c ≤ d ≤ b` leaves
`[a, c] ∪ [d, b]`. -/
theorem Icc_sdiff_Ioo {α : Type*} [LinearOrder α] {a b c d : α}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    Icc a b \ Ioo c d = Icc a c ∪ Icc d b := by
  ext x
  simp only [mem_sdiff, mem_Icc, mem_Ioo, mem_union, not_and, not_lt]
  refine ⟨fun ⟨⟨hax, hxb⟩, hnot⟩ => ?_, ?_⟩
  · by_cases hxc : x ≤ c
    · exact Or.inl ⟨hax, hxc⟩
    · exact Or.inr ⟨hnot (not_le.mp hxc), hxb⟩
  · rintro (⟨hax, hxc⟩ | ⟨hdx, hxb⟩)
    · exact ⟨⟨hax, hxc.trans (hcd.trans hdb)⟩, fun hcx => absurd hcx (not_lt.mpr hxc)⟩
    · exact ⟨⟨hac.trans (hcd.trans hdx), hxb⟩, fun _ => hdx⟩

end Set
