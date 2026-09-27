/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Hom from a finite biproduct in a linear category

The universal property of a biproduct identifies morphisms out of it with families of
morphisms out of its summands. In a linear category this is a linear equivalence, so finite
dimensionality and dimension of the Hom space can be read summand by summand.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Semiring

variable (k : Type t) [Semiring k] [Linear k C]
  {J : Type w} (X : J → C) [HasBiproduct X] (Y : C)

/-- Morphisms from a biproduct form the product of the Hom spaces from its summands. -/
noncomputable def homBiproductLinearEquiv :
    (⨁ X ⟶ Y) ≃ₗ[k] (∀ j, X j ⟶ Y) where
  toFun f j := biproduct.ι X j ≫ f
  invFun f := biproduct.desc f
  left_inv f := biproduct.hom_ext' _ _ fun j ↦ by simp
  right_inv f := funext fun j ↦ by simp
  map_add' f g := by
    ext j
    simp
  map_smul' r f := by
    ext j
    simp

/-- The equivalence reads off a morphism's component at a summand. -/
@[simp]
theorem homBiproductLinearEquiv_apply (f : ⨁ X ⟶ Y) (j : J) :
    homBiproductLinearEquiv k X Y f j = biproduct.ι X j ≫ f := by
  rfl

/-- The inverse assembles a family of morphisms by the biproduct desc map. -/
@[simp]
theorem homBiproductLinearEquiv_symm_apply (f : ∀ j, X j ⟶ Y) :
    (homBiproductLinearEquiv k X Y).symm f = biproduct.desc f := by
  rfl

end Semiring

section Field

variable (k : Type t) [Field k] [Linear k C]
  {J : Type w} (X : J → C) [HasBiproduct X] (Y : C)

/-- Finite-dimensional Hom spaces out of each summand give a finite-dimensional Hom space
out of a finite biproduct. -/
theorem finiteDimensional_hom_biproduct [Finite J]
    (h : ∀ j, FiniteDimensional k (X j ⟶ Y)) :
    FiniteDimensional k (⨁ X ⟶ Y) := by
  let (j : J) := h j
  exact Module.Finite.equiv (homBiproductLinearEquiv k X Y).symm

/-- The dimension of Hom out of a finite biproduct is the sum of the dimensions from its
summands. -/
theorem finrank_hom_biproduct [Fintype J]
    (h : ∀ j, FiniteDimensional k (X j ⟶ Y)) :
    Module.finrank k (⨁ X ⟶ Y) = ∑ j, Module.finrank k (X j ⟶ Y) := by
  let (j : J) := h j
  let _ := finiteDimensional_hom_biproduct k X Y h
  rw [(homBiproductLinearEquiv k X Y).finrank_eq, Module.finrank_pi_fintype]

end Field

end TauCeti
