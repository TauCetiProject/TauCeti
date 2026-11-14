/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Adjunctions between linear functors

Let `adj : F ⊣ G` be an adjunction between functors on `R`-linear preadditive categories.

* If one of the adjoint functors is `R`-linear, then so is the other
  (`CategoryTheory.Adjunction.right_adjoint_linear`,
  `CategoryTheory.Adjunction.left_adjoint_linear`).
* When `F` is additive and `R`-linear, the Hom-set bijection `adj.homEquiv X Y` upgrades to an
  `R`-linear isomorphism `CategoryTheory.Adjunction.homLinearEquiv`.

## Main declarations

* `CategoryTheory.Adjunction.right_adjoint_linear` and
  `CategoryTheory.Adjunction.left_adjoint_linear`: `R`-linearity transfers across an adjunction;
* `CategoryTheory.Adjunction.homLinearEquiv`: the `R`-linear isomorphism
  `(F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y)` upgrading `adj.homEquiv X Y`.
-/

public section

namespace CategoryTheory.Adjunction

universe t u₁ u₂ v₁ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (R : Type t) [Semiring R] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj in
/-- If the left adjoint in an adjunction `F ⊣ G` is `R`-linear, then so is the right adjoint. -/
theorem right_adjoint_linear [F.Linear R] : G.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).symm.injective <| by
    simp [homEquiv_counit]

include adj in
/-- If the right adjoint in an adjunction `F ⊣ G` is `R`-linear, then so is the left adjoint. -/
theorem left_adjoint_linear [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).injective <| by
    simp [homEquiv_unit]

section HomLinearEquiv

variable [F.Additive] [F.Linear R]

/-- Given an adjunction `adj : F ⊣ G` between `R`-linear categories with `F` additive and
`R`-linear, `adj.homEquiv X Y` upgrades to an `R`-linear isomorphism `(F.obj X ⟶ Y) ≃ₗ[R]
(X ⟶ G.obj Y)`. -/
def homLinearEquiv (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    have := adj.right_adjoint_linear R
    simp [homEquiv_unit]

/-- `homLinearEquiv` agrees with `homEquiv` on morphisms `F.obj X ⟶ Y`. -/
@[simp]
theorem homLinearEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv R X Y f = adj.homEquiv X Y f :=
  (rfl)

/-- `homLinearEquiv.symm` agrees with `homEquiv.symm` on morphisms `X ⟶ G.obj Y`. -/
@[simp]
theorem homLinearEquiv_symm_apply (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homLinearEquiv R X Y).symm f = (adj.homEquiv X Y).symm f :=
  (rfl)

/-- `adj.homEquiv X Y` commutes with scalar multiplication. -/
@[simp]
theorem homLinearEquiv_smul (X : C) (Y : D) (r : R) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (r • f) = r • adj.homEquiv X Y f :=
  map_smul (adj.homLinearEquiv R X Y) r f

/-- `(adj.homEquiv X Y).symm` commutes with scalar multiplication. -/
@[simp]
theorem homLinearEquiv_symm_smul (X : C) (Y : D) (r : R) (f : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (r • f) = r • (adj.homEquiv X Y).symm f :=
  map_smul (adj.homLinearEquiv R X Y).symm r f

end HomLinearEquiv

end CategoryTheory.Adjunction
