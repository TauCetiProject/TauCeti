/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Essentially small object properties

This file supplements Mathlib's `Mathlib.CategoryTheory.ObjectProperty.Small`.

## Main declarations

* `CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`: every object property in an
  essentially small category is essentially small, so its full subcategory is essentially small.
-/

public section

universe w

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/-- Every object property in an essentially small category is essentially small. This supplies
the smallness instance for its full subcategory through Mathlib's object-property API. -/
instance essentiallySmall_of_ambient [CategoryTheory.EssentiallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le.{w} (Q := (⊤ : ObjectProperty C)) le_top

end CategoryTheory.ObjectProperty
