/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Index

/-!
# The algebraic closure for the Ree family of type `F₄`

This file records that the algebraic closure attached to a validated Ree index of type `F₄` has
characteristic two. That is the form in which the characteristic reaches a construction on the
family's carrier, whose defining equations and exceptional isogeny live in characteristic two.

## Main result

* `TauCeti.ReeF4LieIndex.charP_closure_two`: the algebraic closure attached to a Ree index of
  type `F₄` has characteristic two.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section

namespace TauCeti.ReeF4LieIndex

/-- The algebraic closure attached to a Ree index of type `F₄` has characteristic two. -/
instance charP_closure_two (d : ReeF4LieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

end TauCeti.ReeF4LieIndex
