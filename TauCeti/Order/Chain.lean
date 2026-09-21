/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite

/-!
# Greatest elements of finite chains

A chain need not have a greatest element, and a finite set need not have one either, but a finite
chain always does: comparability upgrades a maximal element to a greatest one.

The order is an arbitrary reflexive transitive `≤` rather than a `Preorder`, matching the level of
`Set.Finite.exists_maximal`, so the result also applies to a relation carrying no `Preorder`
instance. Every preorder supplies both instances.

## Main results

* `IsChain.exists_isGreatest`: a nonempty finite chain has a greatest element.
-/

public section

namespace IsChain

/-- A nonempty finite chain has a greatest element. -/
theorem exists_isGreatest {α : Type*} [LE α] [IsTrans α (· ≤ ·)] [Std.Refl (· ≤ · : α → α → Prop)]
    {s : Set α} (hchain : IsChain (· ≤ ·) s) (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a, IsGreatest s a := by
  obtain ⟨a, hmax⟩ := hfin.exists_maximal hne
  refine ⟨a, hmax.prop, fun b hb => ?_⟩
  rcases hchain.total hb hmax.prop with hba | hab
  · exact hba
  · exact hmax.le_of_ge hb hab

end IsChain
