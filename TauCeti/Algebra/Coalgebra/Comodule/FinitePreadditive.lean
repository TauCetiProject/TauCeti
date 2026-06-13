/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Preadditive structure on finitely generated comodules

This file records the preadditive structure on the category of finitely generated right
comodules over a coalgebra over a commutative ring. The category is a full subcategory of all
comodules, so Mathlib transfers the preadditive structure from `ComoduleCat`; the declarations
here expose concrete simp API needed to use finite-dimensional comodules without unfolding the
full-subcategory construction.

This is a small Layer 1 prerequisite for the reductive-groups roadmap's finite-dimensional
representation category: additive hom-sets and an additive inclusion functor are needed before
tensor products, duals, and Tannakian reconstruction can be built on finitely generated
comodules.

## Main declarations

* Simp lemmas identifying zero, addition, negation, and subtraction with the corresponding
  ambient comodule morphisms.

## References

This supplies additive-category bookkeeping for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule category should have additive hom-sets before the
rigid monoidal representation category is developed. The transfer mechanism is Mathlib's
`ObjectProperty.FullSubcategory` preadditive instance.
-/

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M N P : FGComoduleCat.{u, v, w} R C}

/-- The zero morphism of finitely generated comodules has the zero ambient comodule morphism
underneath. -/
@[simp]
theorem hom_zero_hom : (0 : M ⟶ N).hom = 0 :=
  rfl

/-- Addition of finitely generated comodule morphisms is addition of the ambient comodule
morphisms. -/
@[simp]
theorem hom_add_hom (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom :=
  rfl

/-- Negation of finitely generated comodule morphisms is negation of the ambient comodule
morphisms. -/
@[simp]
theorem hom_neg_hom (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

/-- Subtraction of finitely generated comodule morphisms is subtraction of the ambient
comodule morphisms. -/
@[simp]
theorem hom_sub_hom (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom :=
  rfl

/-- The underlying linear map of the zero morphism is zero. -/
@[simp]
theorem hom_toLinearMap_zero : (0 : M ⟶ N).hom.toLinearMap = 0 :=
  rfl

/-- The underlying linear map of a sum is the sum of the underlying linear maps. -/
@[simp]
theorem hom_toLinearMap_add (f g : M ⟶ N) :
    (f + g).hom.toLinearMap = f.hom.toLinearMap + g.hom.toLinearMap := by
  simp

/-- The underlying linear map of a negation is the negation of the underlying linear map. -/
@[simp]
theorem hom_toLinearMap_neg (f : M ⟶ N) :
    (-(f)).hom.toLinearMap = -f.hom.toLinearMap := by
  simp

/-- The underlying linear map of a subtraction is the subtraction of the underlying linear
maps. -/
@[simp]
theorem hom_toLinearMap_sub (f g : M ⟶ N) :
    (f - g).hom.toLinearMap = f.hom.toLinearMap - g.hom.toLinearMap := by
  simp

/-- The zero finitely generated comodule morphism evaluates to zero. -/
@[simp]
theorem zero_apply (m : M) : (0 : M ⟶ N) m = 0 :=
  rfl

/-- Addition of finitely generated comodule morphisms is pointwise. -/
@[simp]
theorem add_apply (f g : M ⟶ N) (m : M) : (f + g) m = f m + g m := by
  rfl

/-- Negation of finitely generated comodule morphisms is pointwise. -/
@[simp]
theorem neg_apply (f : M ⟶ N) (m : M) : (-f) m = -f m := by
  -- Pass through the ambient comodule morphism, where pointwise negation is already API.
  change (-f).hom m = -f.hom m
  rw [hom_neg_hom]
  exact ComoduleCat.neg_apply (R := R) (C := C) f.hom m

/-- Subtraction of finitely generated comodule morphisms is pointwise. -/
@[simp]
theorem sub_apply (f g : M ⟶ N) (m : M) : (f - g) m = f m - g m := by
  -- Pass through the ambient comodule morphism, where pointwise subtraction is already API.
  change (f - g).hom m = f.hom m - g.hom m
  rw [hom_sub_hom]
  exact ComoduleCat.sub_apply (R := R) (C := C) f.hom g.hom m

/-- The inclusion into all comodules sends zero morphisms to zero morphisms. -/
@[simp]
theorem incl_map_zero : (incl (R := R) (C := C)).map (0 : M ⟶ N) = 0 :=
  rfl

end FGComoduleCat

end TauCeti
