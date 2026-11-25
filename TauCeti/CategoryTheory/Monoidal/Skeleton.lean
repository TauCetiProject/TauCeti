/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton

/-!
# The monoid homomorphism of skeleta induced by a monoidal functor

A strong monoidal functor `F : C ⥤ D` induces the monoid homomorphism
`CategoryTheory.Skeleton.monoidHom F : Skeleton C →* Skeleton D` on monoids of isomorphism
classes. This file records its value on the class of an object.
-/

public section

namespace CategoryTheory.Skeleton

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- The monoid homomorphism induced by a monoidal functor sends the isomorphism class of `X` to
the isomorphism class of `F.obj X`. -/
@[simp]
lemma monoidHom_toSkeleton (F : C ⥤ D) [F.Monoidal] (X : C) :
    monoidHom F (toSkeleton X) = toSkeleton (F.obj X) :=
  F.mapSkeleton_obj_toSkeleton X

end CategoryTheory.Skeleton
