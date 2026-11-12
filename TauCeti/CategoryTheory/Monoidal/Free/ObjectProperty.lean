/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Monoidal object properties on tensor words

A monoidal property of objects holds on the interpretation of every formal tensor word as soon
as it holds on the generating objects. This lets interpretations of a monoidal presentation be
restricted to properties needed only on their image, rather than imposed on the whole target
category. The interpretation is Mathlib's `FreeMonoidalCategory.projectObj`; no new tensor-word
carrier or evaluation function is introduced.
-/

public section

namespace CategoryTheory.ObjectProperty

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A monoidal property holding on the generators holds on every interpreted tensor word,
including the empty word and every parenthesization. -/
theorem prop_projectObj (P : ObjectProperty C) [P.IsMonoidal] {A : Type w} {f : A → C}
    (h : ∀ a, P (f a)) (W : FreeMonoidalCategory A) :
    P (FreeMonoidalCategory.projectObj f W) := by
  induction W with
  | of a => exact h a
  | unit => exact P.prop_unit
  | tensor X Y hX hY => exact prop_tensor hX hY

end CategoryTheory.ObjectProperty
