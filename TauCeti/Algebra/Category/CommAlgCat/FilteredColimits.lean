/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Filtered colimits in commutative algebras

The forgetful functor from commutative algebras over a base ring to types preserves small
filtered colimits. This is deduced from the corresponding fact for commutative rings, using the
equivalence between commutative algebras and commutative rings under the base.
-/

public section

open CategoryTheory Limits

universe u

namespace CommAlgCat

variable {Base : Type u} [CommRing Base]

/-- The forgetful functor from commutative algebras to types is the composite of the equivalence
with commutative rings under the base, the forgetful functor to commutative rings, and the
forgetful functor to types. -/
@[expose, simps!]
def forgetIsoUnderForget : forget (CommAlgCat.{u} Base) ≅
    (commAlgCatEquivUnder (CommRingCat.of Base)).functor ⋙
      Under.forget (CommRingCat.of Base) ⋙ forget CommRingCat.{u} :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The forgetful functor from commutative algebras to types preserves small filtered colimits. -/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (CommAlgCat.{u} Base)) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_of_natIso (forgetIsoUnderForget (Base := Base)).symm⟩

end CommAlgCat
