/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Order.Bounds.Basic

/-!
# Joins of families of subobjects

Without requiring `WellPowered C`, the least upper bound of a `J`-indexed family of subobjects of
`X` is the image subobject of the map from the coproduct of the domains of the family into `X`
(`CategoryTheory.Subobject.isLUB_range_imageSubobject_sigmaDesc`), whenever that coproduct and
image exist.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- In a category with images, the image subobject of the map from the coproduct of a `J`-indexed
family of subobjects of `X` is the least upper bound of the family, whenever the coproduct and
image exist. -/
lemma isLUB_range_imageSubobject_sigmaDesc {J : Type*} {X : C} (S : J → Subobject X)
    [HasCoproduct fun j ↦ (S j : C)] [HasImage (Sigma.desc fun j ↦ (S j).arrow)] :
    IsLUB (Set.range S) (imageSubobject (Sigma.desc fun j ↦ (S j).arrow)) := by
  refine ⟨?_, fun T hT ↦ ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact le_of_comm (Sigma.ι (fun j ↦ (S j : C)) j ≫ factorThruImageSubobject _) (by simp)
  · refine imageSubobject_le _ (Sigma.desc fun j ↦ ofLE (S j) T (hT ⟨j, rfl⟩)) ?_
    ext j
    simp

end CategoryTheory.Subobject
