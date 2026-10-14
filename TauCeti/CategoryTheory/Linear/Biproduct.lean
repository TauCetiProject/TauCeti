/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hom to and from a biproduct in a linear category

The universal property of a biproduct identifies morphisms out of it with families of
morphisms out of its summands. In a linear category this is a linear equivalence, so finiteness
and rank of the Hom module can be read summand by summand. Dually, morphisms into a biproduct
are families of morphisms into its summands.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (k : Type t) [Semiring k] [Linear k C]
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
    homBiproductLinearEquiv k X Y f j = biproduct.ι X j ≫ f :=
  (rfl)

/-- The inverse assembles a family of morphisms by the biproduct desc map. -/
@[simp]
theorem homBiproductLinearEquiv_symm_apply (f : ∀ j, X j ⟶ Y) :
    (homBiproductLinearEquiv k X Y).symm f = biproduct.desc f :=
  (rfl)

/-- Morphisms into a biproduct form the product of the Hom spaces into its summands. -/
noncomputable def homToBiproductLinearEquiv :
    (Y ⟶ ⨁ X) ≃ₗ[k] (∀ j, Y ⟶ X j) where
  toFun f j := f ≫ biproduct.π X j
  invFun f := biproduct.lift f
  left_inv f := biproduct.hom_ext _ _ fun j ↦ by simp
  right_inv f := funext fun j ↦ by simp
  map_add' f g := by
    ext j
    simp
  map_smul' r f := by
    ext j
    simp

/-- The equivalence reads off a morphism's component at a summand. -/
@[simp]
theorem homToBiproductLinearEquiv_apply (f : Y ⟶ ⨁ X) (j : J) :
    homToBiproductLinearEquiv k X Y f j = f ≫ biproduct.π X j :=
  (rfl)

/-- The inverse assembles a family of morphisms by the biproduct lift map. -/
@[simp]
theorem homToBiproductLinearEquiv_symm_apply (f : ∀ j, Y ⟶ X j) :
    (homToBiproductLinearEquiv k X Y).symm f = biproduct.lift f :=
  (rfl)

/-- Finite Hom modules out of each summand give a finite Hom module out of a finite
biproduct. -/
instance moduleFinite_hom_biproduct [Finite J] [∀ j, Module.Finite k (X j ⟶ Y)] :
    Module.Finite k (⨁ X ⟶ Y) :=
  .equiv (homBiproductLinearEquiv k X Y).symm

/-- The rank of Hom out of a finite biproduct is the sum of the ranks from its summands, when
these are finite free modules. -/
theorem finrank_hom_biproduct [Fintype J] [StrongRankCondition k]
    [∀ j, Module.Free k (X j ⟶ Y)] [∀ j, Module.Finite k (X j ⟶ Y)] :
    Module.finrank k (⨁ X ⟶ Y) = ∑ j, Module.finrank k (X j ⟶ Y) := by
  rw [(homBiproductLinearEquiv k X Y).finrank_eq, Module.finrank_pi_fintype]

end TauCeti
