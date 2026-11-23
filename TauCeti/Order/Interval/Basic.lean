/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Basic

/-!
# Membership in nonempty closed intervals

Membership in a `NonemptyInterval α` is given by `s.fst ≤ a ∧ a ≤ s.snd`. When those endpoint
comparisons are decidable, membership is decidable as well. A strictly monotone map `f` sends `a`
into the closed interval `[f s.fst, f s.snd]` exactly when `a ∈ s`
(`NonemptyInterval.apply_mem_Icc_iff`); for instance, a rational number lies in the real interval
spanned by the endpoints of a rational interval exactly when it lies in the rational interval.
-/

public section

namespace NonemptyInterval

/-- Membership in a nonempty closed interval is decidable when the endpoint comparisons are. -/
instance decidableMem {α : Type*} [Preorder α] {a : α} {s : NonemptyInterval α}
    [Decidable (s.fst ≤ a)] [Decidable (a ≤ s.snd)] : Decidable (a ∈ s) :=
  decidable_of_iff' (s.fst ≤ a ∧ a ≤ s.snd) mem_def

/-- A strictly monotone map `f` sends `a` into `[f s.fst, f s.snd]` exactly when `a ∈ s`. -/
theorem apply_mem_Icc_iff {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    (hf : StrictMono f) {s : NonemptyInterval α} {a : α} :
    f a ∈ Set.Icc (f s.fst) (f s.snd) ↔ a ∈ s := by
  rw [Set.mem_Icc, hf.le_iff_le, hf.le_iff_le, mem_def]

end NonemptyInterval
