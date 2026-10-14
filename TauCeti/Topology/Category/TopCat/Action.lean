/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Continuous actions as functors to `TopCat`

A monoid `G` acting on a space `X` by continuous maps `g • ·` is the same as a functor
`SingleObj G ⥤ TopCat` sending the unique object to `X`. This file defines that functor,
`TopCat.actionFunctor X G`, and records how it acts on objects and morphisms.
-/

public section

open CategoryTheory

universe w

namespace TopCat

variable (X : TopCat.{w}) (G : Type*) [Monoid G] [MulAction G X] [ContinuousConstSMul G X]

/-- A continuous action of a monoid `G` on a space `X`, as the functor `SingleObj G ⥤ TopCat`
sending the unique object to `X` and `g` to the continuous map `g • ·`. -/
@[expose]
def actionFunctor : SingleObj G ⥤ TopCat.{w} :=
  SingleObj.functor
    { toFun g := ofHom ⟨(g • · : X → X), continuous_const_smul g⟩
      map_one' := ConcreteCategory.hom_ext _ _ fun x ↦ one_smul G x
      map_mul' g h := ConcreteCategory.hom_ext _ _ fun x ↦ mul_smul g h x }

@[simp]
lemma actionFunctor_obj (Y : SingleObj G) : (X.actionFunctor G).obj Y = X :=
  (rfl)

lemma actionFunctor_map (g : G) :
    (X.actionFunctor G).map (X := SingleObj.star G) (Y := SingleObj.star G) g =
      ofHom ⟨(g • · : X → X), continuous_const_smul g⟩ :=
  (rfl)

@[simp]
lemma actionFunctor_map_apply (g : G) (x : X) :
    (X.actionFunctor G).map (X := SingleObj.star G) (Y := SingleObj.star G) g x = g • x :=
  (rfl)

end TopCat
