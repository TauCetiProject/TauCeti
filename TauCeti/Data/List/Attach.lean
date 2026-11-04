/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Nodup

/-!
# Lists of subtype elements

This file records how forgetting subtype membership proofs from a list interacts with membership
and duplicate-freeness.
-/

public section

namespace List

variable {α : Type*} {p : α → Prop}

/-- An element of a subtype occurs in a list exactly when its value occurs in the list with
membership proofs forgotten. -/
theorem val_mem_unattach_iff (a : Subtype p) (l : List (Subtype p)) :
    (a : α) ∈ l.unattach ↔ a ∈ l := by
  rw [List.mem_unattach]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · intro h
    exact ⟨a.2, h⟩

/-- Forgetting membership proofs preserves and reflects duplicate-freeness. -/
@[simp]
theorem nodup_unattach_iff (l : List (Subtype p)) : l.unattach.Nodup ↔ l.Nodup := by
  rw [List.unattach, List.nodup_map_iff Subtype.val_injective]

end List
