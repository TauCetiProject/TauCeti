/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linear adjunctions

For an adjunction `adj : F ⊣ G` between `R`-linear categories, `R`-linearity of either adjoint
transfers to the other (`CategoryTheory.Adjunction.right_adjoint_linear` and
`CategoryTheory.Adjunction.left_adjoint_linear`), and when `F` is additive and `G` is `R`-linear,
the adjunction equivalence `adj.homEquiv X Y` upgrades to an `R`-linear equivalence
`CategoryTheory.Adjunction.homLinearEquiv`.
-/

public section

namespace CategoryTheory.Adjunction

universe t v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (R : Type t) [Semiring R] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section

include adj

/-- If the left adjoint of an adjunction between `R`-linear categories is `R`-linear, then so is
the right adjoint. -/
lemma right_adjoint_linear [F.Linear R] : G.Linear R where
  map_smul {X Y} f r := (adj.homEquiv (G.obj X) Y).symm.injective (by simp [homEquiv_counit])

/-- If the right adjoint of an adjunction between `R`-linear categories is `R`-linear, then so is
the left adjoint. -/
lemma left_adjoint_linear [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv X (F.obj Y)).injective (by simp [homEquiv_unit])

end

/-- If `adj : F ⊣ G` is an adjunction between `R`-linear categories with `F` additive and `G`
`R`-linear, then `adj.homEquiv X Y` upgrades to an `R`-linear equivalence. -/
@[expose]
def homLinearEquiv [F.Additive] [G.Linear R] (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  (adj.homAddEquiv X Y).toLinearEquiv fun r g ↦ by simp [homEquiv_unit]

/-- The linear equivalence `adj.homLinearEquiv R X Y` acts as `adj.homEquiv X Y`. -/
@[simp]
lemma homLinearEquiv_apply [F.Additive] [G.Linear R] (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv R X Y f = adj.homEquiv X Y f := by
  rfl

/-- The inverse of `adj.homLinearEquiv R X Y` acts as `(adj.homEquiv X Y).symm`. -/
@[simp]
lemma homLinearEquiv_symm_apply [F.Additive] [G.Linear R] (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homLinearEquiv R X Y).symm f = (adj.homEquiv X Y).symm f := by
  rfl

end CategoryTheory.Adjunction
