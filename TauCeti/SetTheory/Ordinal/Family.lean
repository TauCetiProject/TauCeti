/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-!
# Lifting suprema of ordinals

`Ordinal.lift` commutes with the supremum of a family of ordinals bounded above, as
`Cardinal.lift_iSup` does for cardinals.

## Main results

* `TauCeti.Ordinal.lift_iSup`: the lift of a bounded supremum is the supremum of the lifts.
-/

public section

universe u v w

namespace TauCeti

namespace Ordinal

/-- **`Ordinal.lift` commutes with a bounded supremum**: the lift of the supremum of a family of
ordinals bounded above is the supremum of the lifts. -/
theorem lift_iSup {β : Type w} {f : β → _root_.Ordinal.{u}} (hf : BddAbove (Set.range f)) :
    _root_.Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, _root_.Ordinal.lift.{v} (f i) := by
  -- Normality of the lift gives this over a nonempty index type; over an empty one both sides
  -- are `0`.
  rcases isEmpty_or_nonempty β with _ | _
  · simp
  · exact _root_.Ordinal.liftInitialSeg.isNormal.map_iSup hf

end Ordinal

end TauCeti
