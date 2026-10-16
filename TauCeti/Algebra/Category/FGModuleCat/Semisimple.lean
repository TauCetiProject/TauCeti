/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Finite-dimensional vector spaces are finite semisimple

Finite-dimensional vector spaces over a division ring form a finite semisimple category: each one
decomposes along a basis as a finite biproduct of copies of the one-dimensional space.

## Main results

* `TauCeti.instIsFiniteSemisimpleCategoryFGModuleCat`: finite-dimensional vector spaces over a
  division ring form a finite semisimple category.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (K : Type u) [DivisionRing K]

/-- Finite-dimensional vector spaces over a division ring form a finite semisimple category. -/
noncomputable instance instIsFiniteSemisimpleCategoryFGModuleCat :
    IsFiniteSemisimpleCategory (FGModuleCat.{u} K) where
  exists_biproduct_simples X := by
    let ι := Fin (Module.finrank K X)
    let f : ι → FGModuleCat.{u} K := fun _ ↦ FGModuleCat.of K K
    let F := forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)
    have hf (j : ι) : Simple (f j) := by
      let _ : Simple (F.obj (f j)) := simple_of_isSimpleModule (R := K) (M := K)
      exact F.simple_of_simple_obj (f j)
    let _ : ∀ j, Simple (f j) := hf
    let _ : HasFiniteBiproducts (FGModuleCat.{u} K) := Abelian.hasFiniteBiproducts
    let _ : HasBiproduct f := inferInstance
    refine ⟨ι, inferInstance, f, hf, inferInstance, ?_⟩
    have := preservesBiproduct_of_preservesProduct F (f := f)
    let e₁ : F.obj X ≅ ModuleCat.of K (ι → K) :=
      (Module.finBasis K X).equivFun.toModuleIso
    let e₂ : ModuleCat.of K (ι → K) ≅ ⨁ fun _ : ι ↦ ModuleCat.of K K :=
      (ModuleCat.biproductIsoPi fun _ : ι ↦ ModuleCat.of K K).symm
    exact ⟨F.preimageIso (e₁ ≪≫ e₂ ≪≫ (F.mapBiproduct f).symm)⟩

end TauCeti
