/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Logic.Basic

/-!
# Universal statements split at two points

A statement holds everywhere exactly when it holds at two given points and at every point
different from both. This is the form in which agreement of two functions is checked when two
distinguished coordinates are treated separately from the rest.

## Main results

* `TauCeti.forall_iff_forall_ne_ne_and`: `∀ i, P i` iff `P` holds away from `p` and `q`, at `p`,
  and at `q`.
-/

public section

namespace TauCeti

/-- A statement holds everywhere exactly when it holds at two given points and away from them. -/
theorem forall_iff_forall_ne_ne_and {α : Sort*} {P : α → Prop} (p q : α) :
    (∀ i, P i) ↔ (∀ i, i ≠ p → i ≠ q → P i) ∧ P p ∧ P q := by
  refine ⟨fun h ↦ ⟨fun i _ _ ↦ h i, h p, h q⟩, fun ⟨h, hp, hq⟩ i ↦ ?_⟩
  by_cases hip : i = p
  · exact hip ▸ hp
  by_cases hiq : i = q
  · exact hiq ▸ hq
  exact h i hip hiq

end TauCeti
