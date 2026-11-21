/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic

import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension as a ring homomorphism on split `K₀`

For commutative rings `R` and `S`, extension of scalars along any ring homomorphism `f : R →+* S`
upgrades `SplitK0.map f.finiteProjectiveModulesExtendScalars` to a ring homomorphism
`RingHom.finiteProjectiveModulesSplitK0Extend : K₀(proj R) →+* K₀(proj S)`, functorial in `f`.

## Main definitions

* `RingHom.finiteProjectiveModulesSplitK0Extend`: the ring homomorphism
  `K₀(proj R) →+* K₀(proj S)` induced by scalar extension along `f : R →+* S`.

## Main results

* `RingHom.finiteProjectiveModulesSplitK0Extend_toAddMonoidHom`,
  `RingHom.finiteProjectiveModulesSplitK0Extend_of`,
  `RingHom.finiteProjectiveModulesSplitK0Extend_id`, and
  `RingHom.finiteProjectiveModulesSplitK0Extend_comp`: underlying additive map, action on
  generators, and functoriality.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace RingHom

open TauCeti

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

-- The monoidal unit in `(finiteProjectiveModules R).FullSubcategory` reduces definitionally to `R`.
private theorem tensorUnit_obj (R : Type u) [CommRing R] :
    (𝟙_ (finiteProjectiveModules R).FullSubcategory).obj = ModuleCat.of R R := rfl

-- The monoidal tensor product in `(finiteProjectiveModules R).FullSubcategory` reduces
-- definitionally to `⊗[R]`.
private theorem tensorObj_obj {R : Type u} [CommRing R]
    (P Q : (finiteProjectiveModules R).FullSubcategory) :
    (P ⊗ Q).obj = ModuleCat.of R (P.obj ⊗[R] Q.obj) := rfl

/-- Scalar extension preserves multiplication on split `K₀` of finitely generated projective
modules over commutative rings. -/
private theorem map_extendScalars_mul (f : R →+* S) :
    ∀ x y : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory,
      SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (x * y) =
        SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x *
          SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars y := by
  rw [AddMonoidHom.map_mul_iff]
  refine SplitK0.hom_ext fun P ↦ SplitK0.hom_ext fun Q ↦ ?_
  let : Algebra R S := f.toAlgebra
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, SplitK0.of_mul_of, SplitK0.map_of]
  let e (X : (finiteProjectiveModules R).FullSubcategory) :
      S ⊗[R] X.obj ≃ₗ[S] (f.finiteProjectiveModulesExtendScalars.obj X).obj :=
    (BalancedExtension.equivTensorProduct R S X.obj).symm.trans
      (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj X)).symm.toLinearEquiv
  exact SplitK0.of_extendScalars_obj (P := P ⊗ Q)
    (Q := f.finiteProjectiveModulesExtendScalars.obj P ⊗
      f.finiteProjectiveModulesExtendScalars.obj Q) <|
    (BalancedExtension.congr f (eqToIso (tensorObj_obj P Q)).toLinearEquiv).trans
      ((BalancedExtension.equivTensorProduct R S (P.obj ⊗[R] Q.obj)).trans
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R S P.obj Q.obj).trans
          ((TensorProduct.congr (e P) (e Q)).trans
            (eqToIso (tensorObj_obj _ _)).symm.toLinearEquiv)))

/-- **Extension of scalars as a ring homomorphism on split `K₀`.** For commutative rings, a ring
homomorphism `f : R →+* S` induces a ring homomorphism
`K₀(proj R) →+* K₀(proj S)` extending `SplitK0.map f.finiteProjectiveModulesExtendScalars`. -/
noncomputable def finiteProjectiveModulesSplitK0Extend (f : R →+* S) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+*
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory where
  __ := SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars
  map_one' := by
    let : Algebra R S := f.toAlgebra
    rw [SplitK0.one_def, SplitK0.one_def, AddMonoidHom.toFun_eq_coe, SplitK0.map_of]
    exact SplitK0.of_extendScalars_obj (Q := 𝟙_ (finiteProjectiveModules S).FullSubcategory)
      ((BalancedExtension.equivTensorProduct R S R).trans
        ((TensorProduct.AlgebraTensorModule.rid R S S).trans
          (eqToIso (tensorUnit_obj S)).symm.toLinearEquiv))
  map_mul' := map_extendScalars_mul f

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_toAddMonoidHom (f : R →+* S) :
    (f.finiteProjectiveModulesSplitK0Extend : _ →+ _) =
      SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars := (rfl)

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_of (f : R →+* S)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesSplitK0Extend (SplitK0.of.{u} P) =
      SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars P

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_id :
    (RingHom.id R).finiteProjectiveModulesSplitK0Extend = RingHom.id _ := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  rw [finiteProjectiveModulesSplitK0Extend_of, RingHom.id_apply]
  exact SplitK0.of_extendScalars_obj (BalancedExtension.lid R P.obj)

theorem finiteProjectiveModulesSplitK0Extend_comp (g : S →+* T) (f : R →+* S) :
    (g.comp f).finiteProjectiveModulesSplitK0Extend =
      g.finiteProjectiveModulesSplitK0Extend.comp f.finiteProjectiveModulesSplitK0Extend := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  simp only [RingHom.comp_apply, finiteProjectiveModulesSplitK0Extend_of]
  exact (SplitK0.of_extendScalars_obj (P := f.finiteProjectiveModulesExtendScalars.obj P)
    (Q := (g.comp f).finiteProjectiveModulesExtendScalars.obj P) <|
    (BalancedExtension.congr g
        (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P)).toLinearEquiv).trans
      ((BalancedExtension.cancelBaseChange f g).trans
        (eqToIso ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P)).symm.toLinearEquiv)
    ).symm

end RingHom
