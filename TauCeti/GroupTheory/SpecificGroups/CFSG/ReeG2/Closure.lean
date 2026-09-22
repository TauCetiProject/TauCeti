/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index

/-!
# The algebraic closure for the Ree family of type `G₂`

This file records that the algebraic closure attached to a validated Ree index of type `G₂` has
characteristic three, and equips it with the resulting structure of an algebra over the field of
three elements. This is the base ring over which the family's short-root carrier is defined.

## Main results

* `TauCeti.ReeG2LieIndex.charP_closure_three`: the algebraic closure attached to a Ree index of
  type `G₂` has characteristic three.
* `TauCeti.ReeG2LieIndex.algebraZModThree`: the resulting `ZMod 3`-algebra structure on it.
-/

public section

namespace TauCeti.ReeG2LieIndex

/-- The algebraic closure attached to a Ree index of type `G₂` has characteristic three. -/
instance charP_closure_three (d : ReeG2LieIndex) : CharP d.1.Closure 3 := by
  rw [← d.characteristic_eq_three]
  infer_instance

/-- The algebraic closure attached to a Ree index of type `G₂` is an algebra over the field of
three elements, the base ring of the family's carrier. Characteristic three determines this
structure uniquely. -/
noncomputable instance algebraZModThree (d : ReeG2LieIndex) : Algebra (ZMod 3) d.1.Closure :=
  ZMod.algebra d.1.Closure 3

end TauCeti.ReeG2LieIndex
