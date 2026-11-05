/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero morphisms: induced maps on quotients and faithful functors

In a category with zero morphisms, a composite of two maps induced on quotients vanishes as soon as
the final quotient map kills the morphism inducing the first one.  This is the complex condition
for sequences of quotients such as `coker f ⟶ coker (f ≫ g) ⟶ coker g`.

A faithful functor out of a category with zero morphisms reflects zero objects
(`CategoryTheory.Functor.isZero_of_isZero_obj`): if `F.obj X` is a zero object then `F` sends
`𝟙 X` and `0` to the same morphism, so `𝟙 X = 0`. This complements Mathlib's
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero`, which asks for fullness instead of
zero morphisms in the source.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {Y Z Q₁ Q₂ Q₃ : C} {g : Y ⟶ Z}
  {π₁ : Y ⟶ Q₁} {π₂ : Z ⟶ Q₂} {π₃ : Z ⟶ Q₃} {u : Q₁ ⟶ Q₂} {v : Q₂ ⟶ Q₃}

/-- Let `u` and `v` be the maps induced by `g` and by the identity on the targets of `π₁`, `π₂` and
`π₃`, in the sense that `π₁ ≫ u = g ≫ π₂` and `π₂ ≫ v = π₃`. If `π₁` is an epimorphism and
`g ≫ π₃ = 0`, then `u ≫ v = 0`. -/
theorem comp_eq_zero_of_epi (hπ₁ : Epi π₁) (w₃ : g ≫ π₃ = 0) (hu : π₁ ≫ u = g ≫ π₂)
    (hv : π₂ ≫ v = π₃) : u ≫ v = 0 :=
  hπ₁.left_cancellation _ _ (by simp [reassoc_of% hu, hv, w₃])

end TauCeti

namespace CategoryTheory.Functor

universe v' u'

/-- A faithful functor out of a category with zero morphisms reflects zero objects. -/
theorem isZero_of_isZero_obj {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful] {X : C} (hX : IsZero (F.obj X)) :
    IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (F.map_injective (hX.eq_of_src _ _))

end CategoryTheory.Functor
