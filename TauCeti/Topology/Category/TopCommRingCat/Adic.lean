/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCommRingCat
public import TauCeti.RingTheory.AdicRing.Basic

/-!
# The category of complete separated adic rings of finite ideal type

We define the object property `TauCeti.TopCommRingCat.isAdicRing` cutting out complete separated
adic rings of finite ideal type inside `TopCommRingCat`, together with its defining equivalence
`TauCeti.TopCommRingCat.isAdicRing_iff` and the `TauCeti.IsAdicRing` instance on objects of the
full subcategory `isAdicRing.FullSubcategory`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti.TopCommRingCat

/-- The property of a `TopCommRingCat` being a complete separated adic ring of finite ideal type. -/
def isAdicRing : ObjectProperty TopCommRingCat.{u} := fun R ↦ IsAdicRing R

/-- A `TopCommRingCat` satisfies `isAdicRing` iff it carries an `IsAdicRing` instance. -/
@[simp]
theorem isAdicRing_iff (R : TopCommRingCat.{u}) : isAdicRing R ↔ IsAdicRing R := Iff.rfl

instance (R : isAdicRing.{u}.FullSubcategory) : IsAdicRing R.obj := R.property

end TauCeti.TopCommRingCat
