/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Additive change of sheaf coefficients

Postcomposition with an additive coefficient functor is additive on sheaf categories,
provided the functor preserves the sheaf condition. This allows additive constructions on
sheaves to be compared under coefficient change without requiring a coefficient equivalence.
-/

public section

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- Postcomposition with an additive coefficient functor is additive on sheaves. -/
instance additive_sheafCompose {C : Type u} [Category.{v} C]
    {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    (J : GrothendieckTopology C) (F : A ⥤ B) [J.HasSheafCompose F] [F.Additive] :
    (sheafCompose J F).Additive where
  map_add := by
    intro P Q f g
    ext U
    exact F.map_add

end CategoryTheory
