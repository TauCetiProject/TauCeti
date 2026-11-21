/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Truncation bounds for `TStructure.triangleLEGE`

Mathlib provides `TStructure.IsLE` and `TStructure.IsGE` instances on `(t.truncLE a).obj X` and
`(t.truncGE b).obj X`, as well as the canonical truncation triangle `t.triangleLEGE a b h`.
Because `t.triangleLEGE` is not marked `@[reducible]`, typeclass synthesis does not automatically
transport those instances through `((t.triangleLEGE a b h).obj X).obj₁` and `.obj₃`.

This file supplies the corresponding `t.IsLE` and `t.IsGE` instances for the first and third
vertices of `(t.triangleLEGE a b h).obj X`, removing boilerplate rewrites during t-structure
truncation inductions (such as in `TauCeti.Algebra.Homology.DerivedCategory.TStructure` and
`TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`).
-/

public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The first vertex of `(t.triangleLEGE a b h).obj X` lies in `≤ a`. -/
instance (X : C) (a b : ℤ) (h : a + 1 = b) : t.IsLE (((t.triangleLEGE a b h).obj X).obj₁) a := by
  rw [triangleLEGE_obj_obj₁]
  infer_instance

/-- If `X` lies in `≤ c`, then so does the first vertex of `(t.triangleLEGE a b h).obj X`. -/
instance (X : C) (a b c : ℤ) (h : a + 1 = b) [t.IsLE X c] :
    t.IsLE (((t.triangleLEGE a b h).obj X).obj₁) c := by
  rw [triangleLEGE_obj_obj₁]
  infer_instance

/-- The third vertex of `(t.triangleLEGE a b h).obj X` lies in `≥ b`. -/
instance (X : C) (a b : ℤ) (h : a + 1 = b) : t.IsGE (((t.triangleLEGE a b h).obj X).obj₃) b := by
  rw [triangleLEGE_obj_obj₃]
  infer_instance

/-- If `X` lies in `≥ c`, then so does the third vertex of `(t.triangleLEGE a b h).obj X`. -/
instance (X : C) (a b c : ℤ) (h : a + 1 = b) [t.IsGE X c] :
    t.IsGE (((t.triangleLEGE a b h).obj X).obj₃) c := by
  rw [triangleLEGE_obj_obj₃]
  infer_instance

section IsTriangulated

variable [IsTriangulated C]

/-- In a triangulated category, if `X` lies in `≥ c`, then so does the first vertex of
`(t.triangleLEGE a b h).obj X`. -/
instance (X : C) (a b c : ℤ) (h : a + 1 = b) [t.IsGE X c] :
    t.IsGE (((t.triangleLEGE a b h).obj X).obj₁) c := by
  rw [triangleLEGE_obj_obj₁]
  infer_instance

/-- In a triangulated category, if `X` lies in `≤ c`, then so does the third vertex of
`(t.triangleLEGE a b h).obj X`. -/
instance (X : C) (a b c : ℤ) (h : a + 1 = b) [t.IsLE X c] :
    t.IsLE (((t.triangleLEGE a b h).obj X).obj₃) c := by
  rw [triangleLEGE_obj_obj₃]
  infer_instance

end IsTriangulated

end CategoryTheory.Triangulated.TStructure
