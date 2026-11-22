/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Basic

/-!
# Membership in nonempty closed intervals

Membership in a `NonemptyInterval α` is given by `s.fst ≤ a ∧ a ≤ s.snd`, that is, by
membership in `Set.Icc s.fst s.snd`. When those endpoint comparisons are decidable, membership is
decidable as well.
-/

public section

namespace NonemptyInterval

/-- Membership in a nonempty closed interval is membership in the closed set interval between its
endpoints. -/
theorem mem_iff_mem_Icc {α : Type*} [Preorder α] {a : α} {s : NonemptyInterval α} :
    a ∈ s ↔ a ∈ Set.Icc s.fst s.snd :=
  mem_def.trans Set.mem_Icc.symm

/-- Membership in a nonempty closed interval is decidable when the endpoint comparisons are. -/
instance decidableMem {α : Type*} [Preorder α] {a : α} {s : NonemptyInterval α}
    [Decidable (s.fst ≤ a)] [Decidable (a ≤ s.snd)] : Decidable (a ∈ s) :=
  decidable_of_iff' (s.fst ≤ a ∧ a ≤ s.snd) mem_def

end NonemptyInterval
