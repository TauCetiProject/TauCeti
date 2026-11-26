/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Inverse images of pseudofunctor object properties

A strong transformation of `Cat`-valued pseudofunctors pulls back object properties fibrewise.
This construction respects identity transformations and composition, independently of any
Grothendieck topology or descent condition. It uses Mathlib's `ObjectProperty.inverseImage`
on each component functor.
-/

public section

open CategoryTheory Bicategory Opposite

namespace CategoryTheory.Pseudofunctor.ObjectProperty

universe v v' u u'

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- The inverse image of an object property along a strong transformation, computed in each
fibre category. -/
def inverseImage (Q : G.ObjectProperty) (η : StrongTrans F G) : F.ObjectProperty where
  prop U := (Q.prop U).inverseImage (η.app U).toFunctor

@[simp]
lemma inverseImage_prop (Q : G.ObjectProperty) (η : StrongTrans F G)
    (U : LocallyDiscrete Cᵒᵖ) (M : F.obj U) :
    (Q.inverseImage η).prop U M ↔ Q.prop U ((η.app U).toFunctor.obj M) :=
  Iff.rfl

@[simp]
lemma inverseImage_id (P : F.ObjectProperty) : P.inverseImage (StrongTrans.id F) = P :=
  (rfl)

@[simp]
lemma inverseImage_comp {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    (Q : H.ObjectProperty) (η : StrongTrans F G) (θ : StrongTrans G H) :
    Q.inverseImage (StrongTrans.vcomp η θ) = (Q.inverseImage θ).inverseImage η :=
  (rfl)

end CategoryTheory.Pseudofunctor.ObjectProperty
