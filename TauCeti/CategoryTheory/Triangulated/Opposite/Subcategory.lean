/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Triangle-closure conditions on opposite subcategories

Third-object closure of an object property in a pretriangulated category gives first-object
closure of the opposite property. This instance allows arguments using first-object closure
to be applied to the opposite category.
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Third-object closure of a property becomes first-object closure on the opposite category. -/
instance (P : ObjectProperty C) [P.IsTriangulatedClosed₃] : P.op.IsTriangulatedClosed₁ where
  ext₁' T hT h₂ h₃ := by
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _
      ((mem_distTriang_op_iff T).1 hT) h₃ h₂
    exact ⟨Opposite.op X, hX, ⟨e.symm.op⟩⟩

end CategoryTheory.ObjectProperty
