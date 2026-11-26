/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Cover

/-!
# Checks for descending central sections along a cover

* On the empty sieve, whose category of arrows is empty, every family is compatible and gives the
  identity automorphism of the descent datum, whatever its values; no conclusion about descent of
  objects is drawn.
* If `Aut x` is trivial, every compatible family on a covering sieve descends to the identity of
  `x`.
* If the fibre over `U` is empty, the descended centre unit is the identity, for every compatible
  family on every covering sieve (the sieve itself need not be empty).
-/

public section

namespace TauCeti.Examples.BandCenterCover

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {U : C}

/-- On the empty sieve every family is compatible and gives the identity descent automorphism. -/
example (z : ∀ i : (⊥ : Sieve U).arrows.category, IntrinsicBandSections F i.obj.left)
    (x : F.obj (.mk (op U))) :
    coverIso (isCompatible_bot z) x = Iso.refl _ := by
  ext i
  exact i.property.elim

/-- If `Aut x` is trivial, every compatible family descends to the identity of `x`. -/
example {J : GrothendieckTopology C} [F.IsPrestack J] {R : Sieve U} (hR : R ∈ J U)
    {z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left} (hz : IsCompatible z)
    (x : F.obj (.mk (op U))) [Subsingleton (Aut x)] :
    coverAut hR hz x = 1 :=
  Subsingleton.elim _ _

/-- If the fibre over `U` is empty, the descended centre unit is the identity. -/
example {J : GrothendieckTopology C} [F.IsPrestack J] {R : Sieve U} (hR : R ∈ J U)
    {z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left} (hz : IsCompatible z)
    [IsEmpty (F.obj (.mk (op U)))] :
    coverCenter hR hz = 1 :=
  Units.ext (CatCenter.ext _ _ fun x ↦ isEmptyElim x)

end TauCeti.Examples.BandCenterCover
