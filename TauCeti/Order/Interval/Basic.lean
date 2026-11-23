/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Basic

/-!
# Decidable membership for nonempty closed intervals

Membership in a `NonemptyInterval α` is given by `s.fst ≤ a ∧ a ≤ s.snd`. When those endpoint
comparisons are decidable, membership is decidable as well.
-/

public section

namespace NonemptyInterval

/-- Membership in a nonempty closed interval is decidable when the endpoint comparisons are. -/
instance decidableMem {α : Type*} [Preorder α] {a : α} {s : NonemptyInterval α}
    [Decidable (s.fst ≤ a)] [Decidable (a ≤ s.snd)] : Decidable (a ∈ s) :=
  decidable_of_iff' (s.fst ≤ a ∧ a ≤ s.snd) mem_def

end NonemptyInterval
