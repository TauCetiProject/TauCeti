/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.FGModuleCat.Basic

/-!
# Finitely generated projective modules

This file defines the object property `TauCeti.finiteProjectiveModules R` of finitely generated
projective `R`-modules in `ModuleCat R`, together with its basic closure properties (retracts,
zero, binary products), and the regular module `TauCeti.finiteProjectiveModulesRegular R`.

## Main definitions

* `TauCeti.finiteProjectiveModules`: the finitely generated projective modules as a property of
  objects of `ModuleCat R`.
* `TauCeti.finiteProjectiveModulesRegular`: the regular module `R`, as a finitely generated
  projective `R`-module.

## Main results

* `TauCeti.finiteProjectiveModules_iff`: unfolded membership predicate.
* `TauCeti.finiteProjectiveModules_le_finiteModules` and
  `TauCeti.finiteProjectiveModules_le_categoryTheory_isProjective`: comparison with `ModuleCat.isFG`
  and `CategoryTheory.isProjective`.
* Closure of `TauCeti.finiteProjectiveModules R` under retracts, zero, and binary products.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R]

/-- The object property of being a finitely generated projective module. -/
def finiteProjectiveModules : ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Finite R M ∧ Module.Projective R M

variable {R}

@[simp]
theorem finiteProjectiveModules_iff {M : ModuleCat.{u} R} :
    finiteProjectiveModules R M ↔ Module.Finite R M ∧ Module.Projective R M :=
  Iff.rfl

/-- The underlying module of an object of the subcategory of finitely generated projectives is
finitely generated. -/
instance (X : (finiteProjectiveModules R).FullSubcategory) : Module.Finite R X.obj :=
  (finiteProjectiveModules_iff.mp X.property).1

/-- The underlying module of an object of the subcategory of finitely generated projectives is
projective. -/
instance (X : (finiteProjectiveModules R).FullSubcategory) : Module.Projective R X.obj :=
  (finiteProjectiveModules_iff.mp X.property).2

variable (R)

/-- Every finitely generated projective `R`-module is finitely generated. -/
theorem finiteProjectiveModules_le_finiteModules :
    finiteProjectiveModules R ≤ ModuleCat.isFG R := fun _ h =>
  (ModuleCat.isFG_iff _).mpr (finiteProjectiveModules_iff.mp h).1

/-- A finitely generated projective module is a projective object of `ModuleCat R`. -/
theorem finiteProjectiveModules_le_categoryTheory_isProjective :
    finiteProjectiveModules R ≤ CategoryTheory.isProjective (ModuleCat.{u} R) := fun M hM ↦
  have : Module.Projective R M := (finiteProjectiveModules_iff.mp hM).2
  inferInstance

/-- A direct summand of a finitely generated projective module is finitely generated and
projective. In particular the finitely generated projective modules are closed under
isomorphisms. -/
instance : (finiteProjectiveModules R).IsStableUnderRetracts where
  of_retract {M N} h hN := by
    have : Module.Finite R N := (finiteProjectiveModules_iff.mp hN).1
    have : Module.Projective R N := (finiteProjectiveModules_iff.mp hN).2
    have hs : h.r.hom ∘ₗ h.i.hom = LinearMap.id := by
      rw [← ModuleCat.hom_comp, h.retract, ModuleCat.hom_id]
    exact finiteProjectiveModules_iff.mpr
      ⟨Module.Finite.of_surjective h.r.hom fun x ↦ ⟨h.i.hom x, congr($hs x)⟩,
        Module.Projective.of_split h.i.hom h.r.hom hs⟩

/-- The zero `R`-module is finitely generated and projective. -/
instance : (finiteProjectiveModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

/-- Finitely generated projective `R`-modules are closed under binary products. -/
instance : (finiteProjectiveModules R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : Module.Finite R M := (finiteProjectiveModules_iff.mp hM).1
    have : Module.Projective R M := (finiteProjectiveModules_iff.mp hM).2
    have : Module.Finite R N := (finiteProjectiveModules_iff.mp hN).1
    have : Module.Projective R N := (finiteProjectiveModules_iff.mp hN).2
    exact finiteProjectiveModules_iff.mpr
      ⟨Module.Finite.equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm,
        Module.Projective.of_equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm⟩

/-- Finitely generated projective `R`-modules are closed under finite products. -/
instance : (finiteProjectiveModules R).IsClosedUnderFiniteProducts :=
  .mk'

/-- The full subcategory of finitely generated projective `R`-modules has finite biproducts. -/
instance : HasFiniteBiproducts (finiteProjectiveModules R).FullSubcategory :=
  .of_hasFiniteProducts

/-- The full subcategory of finitely generated projective `R`-modules has binary biproducts. -/
instance : HasBinaryBiproducts (finiteProjectiveModules R).FullSubcategory :=
  .of_hasBinaryProducts

/-- The regular module `R`, as a finitely generated projective `R`-module. -/
def finiteProjectiveModulesRegular : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finiteProjectiveModules_iff.2
    ⟨inferInstanceAs (Module.Finite R R), inferInstanceAs (Module.Projective R R)⟩⟩

/-- The underlying module of `TauCeti.finiteProjectiveModulesRegular R` is `R`. -/
@[simp]
theorem finiteProjectiveModulesRegular_obj :
    (finiteProjectiveModulesRegular R).obj = ModuleCat.of R R :=
  (rfl)

end TauCeti
