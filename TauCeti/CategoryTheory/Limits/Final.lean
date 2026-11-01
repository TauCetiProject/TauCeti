/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Final

/-!
# Cones with a fixed apex along an initial functor

For an initial functor `F : C ⥤ D`, Mathlib's `CategoryTheory.Functor.Initial.conesEquiv`
identifies the category of cones over `G : D ⥤ E` with the category of cones over `F ⋙ G`, and
both of its unit and counit are the identity on cone points. This file records the resulting
bijection between natural transformations `const X ⟶ G` and `const X ⟶ F ⋙ G` for a fixed apex
`X`, given by whiskering along `F`. It is the form in which initiality is used to compare
constant presheaves on two sites.
-/

public section

namespace CategoryTheory.Functor.Initial

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (F : C ⥤ D) [F.Initial] (G : D ⥤ E) (X : E)

/-- For an initial functor `F : C ⥤ D`, whiskering along `F` identifies cones with apex `X` over
`G : D ⥤ E` with cones with apex `X` over `F ⋙ G`; the inverse is `Initial.extendCone`. -/
noncomputable def constHomEquiv :
    ((Functor.const D).obj X ⟶ G) ≃ ((Functor.const C).obj X ⟶ F ⋙ G) where
  toFun π := Functor.whiskerLeft F π
  invFun π := (extendCone.obj (Cone.mk X π)).π
  left_inv π := by
    ext Y
    exact (π.naturality (homToLift F Y)).symm.trans (Category.id_comp _)
  right_inv π := by
    ext Y
    exact limit_cone_comp_aux (Cone.mk X π) Y

@[simp]
lemma constHomEquiv_apply (π : (Functor.const D).obj X ⟶ G) :
    constHomEquiv F G X π = Functor.whiskerLeft F π := (rfl)

end CategoryTheory.Functor.Initial
