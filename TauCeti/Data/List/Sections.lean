/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sections

/-!
# Sections of a constant list of lists

The sections of `n` copies of a list `l` are the lists of length `n` with entries in `l`. This
enumerates the tuples of a given length over a finite list of choices.
-/

public section

namespace List

variable {α : Type*}

/-- The sections of `n` copies of `l` are the lists of length `n` all of whose entries lie
in `l`. -/
theorem mem_sections_replicate {l f : List α} {n : ℕ} :
    f ∈ (replicate n l).sections ↔ f.length = n ∧ ∀ a ∈ f, a ∈ l := by
  rw [mem_sections]
  induction n generalizing f with
  | zero => cases f <;> simp
  | succ n ih => cases f <;> simp [replicate_succ, ih, and_left_comm]

end List
