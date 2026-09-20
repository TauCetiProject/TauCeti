/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Index

/-!
# The algebraic closure for the Tits construction

This file records that the algebraic closure attached to the validated Tits index has
characteristic two. That is the form in which the characteristic reaches the explicit type-`F₄`
carrier and its exceptional isogeny.

## Main result

* `TauCeti.TitsLieIndex.charP_closure_two`: the algebraic closure attached to the Tits index has
  characteristic two.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section

namespace TauCeti.TitsLieIndex

/-- The algebraic closure attached to the Tits index has characteristic two. -/
instance charP_closure_two (d : TitsLieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

end TauCeti.TitsLieIndex
