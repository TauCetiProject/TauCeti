/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Partrec

/-!
# Least-success search on optional values

`Nat.mem_rfindOpt_iff` characterizes the result of an optional search by its first success.
-/

public section

namespace Nat

/-- Least-option search returns `y` exactly when the first present observation is `some y`. -/
theorem mem_rfindOpt_iff {α : Type*} {A : ℕ → Option α} {y : α} :
    y ∈ rfindOpt A ↔ ∃ s, A s = some y ∧ ∀ t < s, A t = none := by
  simp only [rfindOpt, Part.mem_bind_iff, Part.mem_coe, Option.mem_def]
  refine exists_congr fun s => ?_
  constructor
  · rintro ⟨hfind, hs⟩
    obtain ⟨-, hbefore⟩ := mem_rfind.1 hfind
    exact ⟨hs, fun _ ht => Option.isNone_iff_eq_none.1
      (Option.isSome_eq_false_iff.1 (Part.mem_some_iff.1 (hbefore ht)).symm)⟩
  · rintro ⟨hs, hbefore⟩
    exact ⟨mem_rfind.2 ⟨by simp [hs], fun {t} ht => by simp [hbefore t ht]⟩, hs⟩

end Nat
