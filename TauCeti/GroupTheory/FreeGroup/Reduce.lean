/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Reduced words in free groups

Elementary facts about reduced words complementing `Mathlib.GroupTheory.FreeGroup.Reduce`:
the formal inverse of a one-letter word, uniqueness of reduced representatives, and
reducedness of formal inverses.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- The inverse of a one-letter word is the inverse letter. -/
theorem inv_mk_singleton (w : α × Bool) : (mk [w])⁻¹ = mk [(w.1, !w.2)] := by
  simp [inv_mk, invRev]

/-- Reduced words representing the same element of a free group are equal. -/
theorem IsReduced.eq_of_mk_eq {u v : List (α × Bool)} (hu : IsReduced u) (hv : IsReduced v)
    (h : mk u = mk v) : u = v := by
  classical
  rw [← hu.reduce_eq, ← hv.reduce_eq, reduce.sound h]

/-- The formal inverse of a reduced word is reduced. -/
theorem IsReduced.invRev {w : List (α × Bool)} (hw : IsReduced w) :
    IsReduced (invRev w) := by
  classical
  have h := isReduced_toWord (x := mk (FreeGroup.invRev w))
  rwa [toWord_mk, reduce_invRev, hw.reduce_eq] at h

end FreeGroup
