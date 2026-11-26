/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.SingleObj

/-!
# One-object categories of opposite monoids

For a monoid `M`, the one-object category `SingleObj M` has the elements of `M` as endomorphisms
of its object `∗`, composed by `f ≫ g = g * f`. Reversing the multiplication is the same as
reversing the composition: `SingleObj Mᵐᵒᵖ` is isomorphic to the opposite category
`(SingleObj M)ᵒᵖ`, a morphism `op a` going to `a.op`. The category `SingleObj M` is also
essentially small as soon as `M` is small, since it has one object.

## Main definitions

* `CategoryTheory.SingleObj.mulOppositeEquiv M : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`, with the
  computation lemmas `mulOppositeEquiv_functor_obj`, `mulOppositeEquiv_functor_map`,
  `mulOppositeEquiv_inverse_obj` and `mulOppositeEquiv_inverse_map`.

## Main results

* The instance `EssentiallySmall.{w} (SingleObj M)` for a `w`-small monoid `M`.
-/

public section

universe w

open Opposite

namespace CategoryTheory.SingleObj

variable (M : Type*) [Monoid M]

/-- The isomorphism of categories `SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`: a morphism `op a` goes to
`a.op`. -/
def mulOppositeEquiv : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ where
  functor :=
    { obj _ := op (SingleObj.star M)
      map f := Quiver.Hom.op (X := SingleObj.star M) (Y := SingleObj.star M) (MulOpposite.unop f)
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj _ := SingleObj.star Mᵐᵒᵖ
      map f := (MulOpposite.op f.unop : Mᵐᵒᵖ)
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {M}

/-- The functor of `mulOppositeEquiv M` sends the object to `op ∗`. -/
@[simp]
theorem mulOppositeEquiv_functor_obj (X : SingleObj Mᵐᵒᵖ) :
    (mulOppositeEquiv M).functor.obj X = op (SingleObj.star M) :=
  (rfl)

/-- The functor of `mulOppositeEquiv M` sends `op a` to `a.op`. -/
@[simp]
theorem mulOppositeEquiv_functor_map {X Y : SingleObj Mᵐᵒᵖ} (f : X ⟶ Y) :
    (mulOppositeEquiv M).functor.map f =
      Quiver.Hom.op (X := SingleObj.star M) (Y := SingleObj.star M) (MulOpposite.unop f) :=
  (rfl)

/-- The inverse of `mulOppositeEquiv M` sends the object to `∗`. -/
@[simp]
theorem mulOppositeEquiv_inverse_obj (X : (SingleObj M)ᵒᵖ) :
    (mulOppositeEquiv M).inverse.obj X = SingleObj.star Mᵐᵒᵖ :=
  (rfl)

/-- The inverse of `mulOppositeEquiv M` sends `a.op` to `op a`. -/
@[simp]
theorem mulOppositeEquiv_inverse_map {X Y : (SingleObj M)ᵒᵖ} (f : X ⟶ Y) :
    (mulOppositeEquiv M).inverse.map f = (MulOpposite.op f.unop : Mᵐᵒᵖ) :=
  (rfl)

/-- A one-object category is essentially small as soon as its endomorphism monoid is small. -/
instance [Small.{w} M] : EssentiallySmall.{w} (SingleObj M) :=
  have : Small.{w} (SingleObj M) := inferInstanceAs (Small.{w} Unit)
  have : LocallySmall.{w} (SingleObj M) := ⟨fun _ _ ↦ inferInstanceAs (Small.{w} M)⟩
  essentiallySmall_of_small_of_locallySmall _

end CategoryTheory.SingleObj
