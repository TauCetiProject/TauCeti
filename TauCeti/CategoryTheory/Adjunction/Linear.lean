/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The hom equivalence of an adjunction with a linear right adjoint

For an adjunction `F ⊣ G` between `R`-linear categories whose right adjoint `G` is `R`-linear, the
hom set bijection `(F X ⟶ Y) ≃ (X ⟶ G Y)` is `R`-linear, because it is postcomposition of `G.map`
with the unit. This is the linear form of Mathlib's `CategoryTheory.Adjunction.homAddEquiv`; it is
what transports a dimension of a morphism space along an adjunction, for instance to compute the
morphisms out of a left adjoint of an evaluation functor.

## Main definitions

* `CategoryTheory.Adjunction.homLinearEquiv`: the hom equivalence of `adj : F ⊣ G` as an `R`-linear
  equivalence, when `G` is `R`-linear.
-/

public section

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂ t

variable (R : Type t) [Semiring R] {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
  [Category.{v₂} D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] [G.Linear R]

/-- **The hom equivalence of an adjunction is `R`-linear** when the right adjoint is `R`-linear:
`(F X ⟶ Y) ≃ₗ[R] (X ⟶ G Y)`. -/
def homLinearEquiv (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  toEquiv := adj.homEquiv X Y
  map_add' _ _ := by simp [homEquiv_unit]
  map_smul' _ _ := by simp [homEquiv_unit]

@[simp]
theorem homLinearEquiv_apply {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv R X Y f = adj.homEquiv X Y f :=
  (rfl)

@[simp]
theorem homLinearEquiv_symm_apply {X : C} {Y : D} (g : X ⟶ G.obj Y) :
    (adj.homLinearEquiv R X Y).symm g = (adj.homEquiv X Y).symm g :=
  (rfl)

end CategoryTheory.Adjunction
