/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Functions pasted at a point of an order

For `b` in an order, `t ↦ if t ≤ b then f t else g t` follows `f` up to `b` and `g` after it:
on `Iic b` it is `f` by `ite_eq_left`, as Mathlib's `Set.piecewise_eqOn` says for
`(Iic b).piecewise f g`. It agrees with `g` on `Ici b` when `f` and `g` agree at `b`
(`Set.eqOn_ite_le_Ici`), and in a linear order it maps `Icc a c` into a set into which `f` maps
`Icc a b` and `g` maps `Icc b c` (`Set.MapsTo.ite_le_Icc`).
-/

public section

namespace Set

variable {α β : Type*}

/-- The function following `f` up to `b` and `g` after it agrees with `g` on `Ici b` when `f` and
`g` agree at `b`. -/
theorem eqOn_ite_le_Ici [PartialOrder α] [DecidableLE α] {f g : α → β} {b : α} (h : f b = g b) :
    EqOn (fun t ↦ if t ≤ b then f t else g t) g (Ici b) := fun t ht ↦ by
  rcases (mem_Ici.1 ht).eq_or_lt with rfl | hlt
  · simp [h]
  · exact ite_eq_right hlt.not_ge

/-- The function following `f` up to `b` and `g` after it maps `Icc a c` into `s` when `f` maps
`Icc a b` and `g` maps `Icc b c` into `s`. -/
theorem MapsTo.ite_le_Icc [LinearOrder α] {f g : α → β} {a b c : α} {s : Set β}
    (hf : MapsTo f (Icc a b) s) (hg : MapsTo g (Icc b c) s) :
    MapsTo (fun t ↦ if t ≤ b then f t else g t) (Icc a c) s :=
  fun t ht ↦ by
    by_cases htb : t ≤ b
    · simpa [htb] using hf ⟨ht.1, htb⟩
    · simpa [htb] using hg ⟨(not_le.1 htb).le, ht.2⟩

end Set
