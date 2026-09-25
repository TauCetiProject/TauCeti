/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Index

/-!
# The algebraic closure for the Tits construction

This file records that the algebraic closure attached to the validated Tits index has
characteristic two, and equips it with the resulting structure of an algebra over the field of two
elements. These are the structures through which the index reaches the explicit type-`F₄` carrier
and its exceptional isogeny.

## Main results

* `TauCeti.TitsLieIndex.charP_closure_two`: the algebraic closure attached to the Tits index has
  characteristic two.
* `TauCeti.TitsLieIndex.algebraZModTwo`: the resulting `ZMod 2`-algebra structure.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section

namespace TauCeti.TitsLieIndex

/-- The algebraic closure attached to the Tits index has characteristic two. -/
instance charP_closure_two (d : TitsLieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

/-- The algebraic closure attached to the Tits index is an algebra over the field of two elements,
the base ring over which its short-root carrier is defined. -/
noncomputable instance algebraZModTwo (d : TitsLieIndex) : Algebra (ZMod 2) d.1.Closure :=
  ZMod.algebra d.1.Closure 2

end TauCeti.TitsLieIndex
