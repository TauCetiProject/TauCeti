/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index

/-!
# The algebraic closure for the Ree family of type `G₂`

This file records that the algebraic closure attached to a validated Ree index of type `G₂` has
characteristic three.

## Main result

* `TauCeti.ReeG2LieIndex.charP_closure_three`: the algebraic closure attached to a Ree index of
  type `G₂` has characteristic three.
-/

public section

namespace TauCeti.ReeG2LieIndex

/-- The algebraic closure attached to a Ree index of type `G₂` has characteristic three. -/
instance charP_closure_three (d : ReeG2LieIndex) : CharP d.1.Closure 3 := by
  rw [← d.characteristic_eq_three]
  infer_instance

end TauCeti.ReeG2LieIndex
