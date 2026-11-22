/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.FGModuleCat.Basic

import TauCeti.Algebra.Module.Projective.FreeComplement

/-!
# The category of finitely generated projective modules

For a ring `R`, this file defines the object property `TauCeti.finiteProjectiveModules R` on
`ModuleCat R` (finitely generated projective `R`-modules), its regular object
`TauCeti.finiteProjectiveModulesRegular R`, the standard finite free objects
`TauCeti.FiniteProjectiveModules.finFreeObj R n`, closure under retracts, zero objects, binary
biproducts, and essential smallness, as well as the categorical free-complement theorem
`TauCeti.FiniteProjectiveModules.exists_biprod_iso_fin` (`P ⊞ Q ≅ Rⁿ`).
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

@[simp] theorem finiteProjectiveModules_iff {M : ModuleCat.{u} R} :
    finiteProjectiveModules R M ↔ Module.Finite R M ∧ Module.Projective R M := Iff.rfl

/-- The underlying module of an object of the subcategory of finitely generated projectives is
finitely generated. -/
instance (X : (finiteProjectiveModules R).FullSubcategory) : Module.Finite R X.obj :=
  (finiteProjectiveModules_iff.mp X.property).1

/-- The underlying module of an object of the subcategory of finitely generated projectives is
projective. -/
instance (X : (finiteProjectiveModules R).FullSubcategory) : Module.Projective R X.obj :=
  (finiteProjectiveModules_iff.mp X.property).2

variable (R)

theorem finiteProjectiveModules_le_finiteModules :
    finiteProjectiveModules R ≤ ModuleCat.isFG R := fun _ h =>
  (ModuleCat.isFG_iff _).mpr (finiteProjectiveModules_iff.mp h).1

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

instance : (finiteProjectiveModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

/-- The regular module `R`, as a finitely generated projective `R`-module. -/
@[expose] def finiteProjectiveModulesRegular : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finiteProjectiveModules_iff.2
    ⟨inferInstanceAs (Module.Finite R R), inferInstanceAs (Module.Projective R R)⟩⟩

/-- The underlying module of `TauCeti.finiteProjectiveModulesRegular R` is `R`. -/
@[simp]
theorem finiteProjectiveModulesRegular_obj :
    (finiteProjectiveModulesRegular R).obj = ModuleCat.of R R :=
  (rfl)

instance : ObjectProperty.EssentiallySmall.{u} (finiteProjectiveModules R) :=
  letI : ObjectProperty.EssentiallySmall.{u} (ModuleCat.isFG.{u} R) :=
    (ObjectProperty.exists_equivalence_iff _).1 ⟨_, _, ⟨equivSmallModel.{u} (FGModuleCat.{u} R)⟩⟩
  ObjectProperty.EssentiallySmall.of_le (finiteProjectiveModules_le_finiteModules R)

instance : (finiteProjectiveModules R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN => by
    have : Module.Finite R M := (finiteProjectiveModules_iff.mp hM).1
    have : Module.Projective R M := (finiteProjectiveModules_iff.mp hM).2
    have : Module.Finite R N := (finiteProjectiveModules_iff.mp hN).1
    have : Module.Projective R N := (finiteProjectiveModules_iff.mp hN).2
    let e := (ModuleCat.biprodIsoProd M N).toLinearEquiv
    exact finiteProjectiveModules_iff.mpr
      ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

instance : (finiteProjectiveModules R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

instance : HasFiniteBiproducts (finiteProjectiveModules R).FullSubcategory :=
  .of_hasFiniteProducts

instance : HasBinaryBiproducts (finiteProjectiveModules R).FullSubcategory :=
  hasBinaryBiproducts_of_finite_biproducts _

namespace FiniteProjectiveModules

variable {R}

/-- The underlying module of a biproduct of finitely generated projective modules is the product of
the underlying modules: the inclusion into `ModuleCat R` is additive, so it carries biproducts to
products. -/
noncomputable def biprodLinearEquiv
    (X Y : (finiteProjectiveModules R).FullSubcategory) :
    (X ⊞ Y).obj ≃ₗ[R] X.obj × Y.obj :=
  letI : PreservesBinaryBiproduct X Y (finiteProjectiveModules R).ι :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  (((finiteProjectiveModules R).ι.mapBiprod X Y).trans (ModuleCat.biprodIsoProd _ _)).toLinearEquiv

section FreeObjects

variable (R)

/-- The finite free module `Fin n → R` in `(finiteProjectiveModules R).FullSubcategory`. -/
@[expose] def finFreeObj (n : ℕ) : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem finFreeObj_obj (n : ℕ) : (finFreeObj R n).obj = ModuleCat.of R (Fin n → R) := (rfl)

end FreeObjects

/-- **Categorical free-complement theorem:** every finite projective module `P` admits a complement
`Q` and `n : ℕ` with `P ⊞ Q ≅ Rⁿ`. -/
theorem exists_biprod_iso_fin (P : (finiteProjectiveModules R).FullSubcategory) :
    ∃ (Q : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      Nonempty (P ⊞ Q ≅ finFreeObj R n) := by
  obtain ⟨N, _, _, hfin, hproj, n, ⟨e⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin R P.obj
  exact ⟨⟨ModuleCat.of R N, finiteProjectiveModules_iff.mpr ⟨hfin, hproj⟩⟩, n,
    ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso
      ((biprodLinearEquiv P _).trans e).toModuleIso⟩⟩

end FiniteProjectiveModules

end TauCeti
