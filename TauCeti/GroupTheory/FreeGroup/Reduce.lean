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
the formal inverse of a one-letter word, uniqueness of reduced representatives, reducedness of
formal inverses, and reducedness of words `w u w⁻¹` in which no letter cancels at either join.
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

/-- A formal inverse is reduced exactly when the original word is. -/
@[simp]
theorem isReduced_invRev {w : List (α × Bool)} : IsReduced (invRev w) ↔ IsReduced w :=
  ⟨fun h => by simpa using IsReduced.invRev h, IsReduced.invRev⟩

/-- If `w` and the nonempty word `u` are reduced, the last letter of `w` does not cancel against
the first letter of `u`, and the last letter of `u` does not cancel against the first letter of
`invRev w`, then `w ++ u ++ invRev w` is reduced. -/
theorem IsReduced.append_append_invRev {w u : List (α × Bool)} (hw : IsReduced w)
    (hu : IsReduced u) (hu₀ : u ≠ [])
    (hhead : ∀ a ∈ w.getLast?, (a.1, !a.2) ∉ u.head?)
    (hlast : ∀ a ∈ w.getLast?, a ∉ u.getLast?) :
    IsReduced (w ++ u ++ FreeGroup.invRev w) := by
  refine List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨hw, hu, ?_⟩, hw.invRev, ?_⟩
  · intro x hx y hy hxy
    have := hhead x hx
    rw [Option.mem_def.mp hy] at this
    cases x; cases y
    simp_all
  · intro x hx y hy hxy
    rw [List.getLast?_append_of_ne_nil _ hu₀] at hx
    simp only [FreeGroup.invRev, List.head?_reverse, List.getLast?_map, Option.mem_def,
      Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := hlast z hz
    rw [Option.mem_def.mp hx] at this
    cases x; cases z
    simp_all [Bool.eq_not]

end FreeGroup
