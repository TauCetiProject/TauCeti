/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite semisimple categories

An abelian category is finite semisimple when every object is isomorphic to a finite biproduct of
simple objects. This file introduces that property, proves that it is invariant under equivalence
of categories, and verifies it for finite-dimensional vector spaces over a field.

The decomposition condition is independent of a choice of coefficient field. Linearity and
finite-dimensionality of morphism spaces are separate hypotheses when they are needed.

## Main results

* `TauCeti.IsFiniteSemisimpleCategory`: every object is a finite biproduct of simple objects.
* `TauCeti.IsFiniteSemisimpleCategory.of_equivalence`: transport finite semisimplicity across an
  equivalence.
* `TauCeti.instIsFiniteSemisimpleCategoryFGModuleCat`: finite-dimensional vector spaces over a
  field form a finite semisimple category.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

/-- An abelian category is finite semisimple if every object is isomorphic to a finite biproduct
of simple objects. -/
class IsFiniteSemisimpleCategory (C : Type u) [Category.{v} C] [Abelian C] : Prop where
  /-- Every object is isomorphic to a finite biproduct of simple objects. -/
  exists_biproduct_simples : ∀ X : C, ∃ (ι : Type) (_ : Fintype ι) (f : ι → C)
    (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f), Nonempty (X ≅ ⨁ f)

namespace IsFiniteSemisimpleCategory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Finite semisimplicity is preserved by an equivalence of abelian categories. -/
theorem of_equivalence (e : C ≌ D) [IsFiniteSemisimpleCategory C] :
    IsFiniteSemisimpleCategory D where
  exists_biproduct_simples X := by
    obtain ⟨ι, hι, f, hf, hbf, ⟨i⟩⟩ :=
      exists_biproduct_simples (e.inverse.obj X)
    let _ := hι
    let _ : ∀ j, Simple (f j) := hf
    let _ := hbf
    let _ : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
    refine ⟨ι, inferInstance, fun j ↦ e.functor.obj (f j), fun j ↦ ?_, inferInstance, ?_⟩
    · exact CategoryTheory.simple_obj e.functor (f j)
    · let comparison : e.functor.obj (⨁ f) ≅ ⨁ fun j ↦ e.functor.obj (f j) :=
        e.functor.mapIso (biproduct.isoProduct f) ≪≫
          PreservesProduct.iso e.functor f ≪≫
          (biproduct.isoProduct fun j ↦ e.functor.obj (f j)).symm
      exact ⟨(e.counitIso.app X).symm ≪≫ e.functor.mapIso i ≪≫ comparison⟩

/-- Equivalent abelian categories are finite semisimple simultaneously. -/
theorem iff_of_equivalence (e : C ≌ D) :
    IsFiniteSemisimpleCategory C ↔ IsFiniteSemisimpleCategory D := by
  constructor
  · intro h
    let _ := h
    exact of_equivalence e
  · intro h
    let _ := h
    exact of_equivalence e.symm

end IsFiniteSemisimpleCategory

section FGModuleCat

variable (K : Type u) [Field K]

/-- Finite-dimensional vector spaces over a field form a finite semisimple category. -/
noncomputable instance instIsFiniteSemisimpleCategoryFGModuleCat :
    IsFiniteSemisimpleCategory (FGModuleCat.{u} K) where
  exists_biproduct_simples X := by
    let ι := Fin (Module.finrank K X)
    let f : ι → FGModuleCat.{u} K := fun _ ↦ FGModuleCat.of K K
    have hf (j : ι) : Simple (f j) := by
      let F := forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)
      let _ : Simple (F.obj (f j)) := by
        dsimp [F, f]
        exact simple_of_finrank_eq_one (k := K) (R := K) (V := ModuleCat.of K K)
          (Module.finrank_self K)
      exact F.simple_of_simple_obj (f j)
    let _ : ∀ j, Simple (f j) := hf
    let _ : HasFiniteBiproducts (FGModuleCat.{u} K) := Abelian.hasFiniteBiproducts
    let _ : HasBiproduct f := inferInstance
    refine ⟨ι, inferInstance, f, hf, inferInstance, ?_⟩
    let F := forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)
    let e₁ : F.obj X ≅ ModuleCat.of K (ι → K) :=
      (Module.finBasis K X).equivFun.toModuleIso
    let e₂ : ModuleCat.of K (ι → K) ≅ ⨁ fun _ : ι ↦ ModuleCat.of K K :=
      (ModuleCat.biproductIsoPi fun _ : ι ↦ ModuleCat.of K K).symm
    let e₃ : (⨁ F.obj ∘ f) ≅ F.obj (⨁ f) :=
      (F.mapIso (biproduct.isoProduct f) ≪≫ PreservesProduct.iso F f ≪≫
        (biproduct.isoProduct (F.obj ∘ f)).symm).symm
    exact ⟨F.preimageIso (e₁ ≪≫ e₂ ≪≫ e₃)⟩

end FGModuleCat

end TauCeti
