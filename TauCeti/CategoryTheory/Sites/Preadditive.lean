/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Additive change of sheaf coefficients and sites

Postcomposition with an additive coefficient functor is additive on sheaf categories,
provided the functor preserves the sheaf condition. This allows additive constructions on
sheaves to be compared under coefficient change without requiring a coefficient equivalence.

Transport of sheaves along an equivalence of sites, Mathlib's `Equivalence.sheafCongr`, is
likewise additive (`CategoryTheory.Equivalence.sheafCongr_additive`), since it adds morphisms
sectionwise, and so is the functor of the inverse equivalence
(`CategoryTheory.Equivalence.sheafCongr_symm_functor_additive`).
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

namespace CategoryTheory.Equivalence

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type*) [Category* A] [Preadditive A] [e.inverse.IsDenseSubsite K J]

/-- A site equivalence preserves the sectionwise addition of sheaf morphisms. -/
instance sheafCongr_additive : (e.sheafCongr J K A).functor.Additive := by
  -- `ObjectProperty.lift` inherits additivity from the composite of sheafToPresheaf
  -- and precomposition, using the generic additive whiskeringLeft instance.
  unfold sheafCongr sheafCongr.functor
  infer_instance

/-- Inverse site transport, as the functor of the inverse equivalence, is additive. -/
instance sheafCongr_symm_functor_additive : (e.sheafCongr J K A).symm.functor.Additive := by
  -- The functor of the inverse equivalence is its inverse functor.
  exact (Equivalence.inverse_additive _ : (e.sheafCongr J K A).inverse.Additive)

end CategoryTheory.Equivalence
