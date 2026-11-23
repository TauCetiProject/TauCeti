/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Basic

/-!
# Upper sets and minimal elements

In a preorder with well-founded `<`, every element of an upper set `D` lies above some minimal
element of `D`, so `D` is the union of the upper cones `Set.Ici a` over its minimal elements.

## Main results

* `IsUpperSet.biUnion_Ici_minimal`: an upper set in a preorder with `WellFoundedLT` equals
  `⋃ a ∈ {a | Minimal (· ∈ D) a}, Set.Ici a`.
-/

public section

namespace IsUpperSet

/-- An upward-closed set `D` in a preorder with well-founded `<` is the union of the cones
`Set.Ici a` over its minimal elements `{a | Minimal (· ∈ D) a}`. -/
theorem biUnion_Ici_minimal {α : Type*} [Preorder α] [WellFoundedLT α]
    {D : Set α} (hD : IsUpperSet D) : ⋃ a ∈ {a | Minimal (· ∈ D) a}, Set.Ici a = D := by
  ext c
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_Ici, exists_prop]
  exact ⟨fun ⟨_, hmin, hle⟩ ↦ hD hle hmin.prop,
    fun hc ↦ let ⟨a, hle, hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D) c hc; ⟨a, hmin, hle⟩⟩

end IsUpperSet
