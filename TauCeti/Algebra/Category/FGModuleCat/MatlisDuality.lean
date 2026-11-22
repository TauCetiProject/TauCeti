/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic
public import TauCeti.RingTheory.Artinian.FiniteLength
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

import TauCeti.Algebra.Category.FGModuleCat.End
import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Duality
import TauCeti.CategoryTheory.Preadditive.Projectivization

/-!
# The Matlis duality between left and right modules over an Artin algebra

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra. Over `A` the finitely generated modules are the modules of finite length over
`R`, so the Matlis duality `ModuleCat.matlisDualityOn` of
`TauCeti/Algebra/Category/ModuleCat/MatlisDuality/FiniteLength.lean` restricts to an
anti-equivalence between the finitely generated left `A`-modules and the finitely generated right
`A`-modules, the modules over `Aᵐᵒᵖ`.

The dual of the regular right module is the left module `D A = Hom_R(A, E)`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`), defined as the image of `Aᵐᵒᵖ` under
the duality. Facts about projective right modules then dualize to facts about `D A`: it is an
injective object of `mod A`, and every injective object of `mod A` is a direct summand of a finite
direct sum of copies of `D A`.

## Main definitions

* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`: the anti-equivalence
  `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`, whose unit and counit are evaluation.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`: the Matlis dual `D A` of the right
  regular module, a finitely generated left `A`-module.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegularEquiv`: the underlying module of `D A`
  is the Matlis dual `Hom_R(A, E)` of the right regular module.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso`: the Matlis
  dual of `D A` is the right regular module, by evaluation.

## Main results

* `TauCeti.IsInjectiveEnvelope.injective_fgModuleCatMatlisDualRegular`: `D A` is injective in
  `mod A`.
* `TauCeti.IsInjectiveEnvelope.additiveClosure_fgModuleCatMatlisDualRegular_of_injective`: every
  injective object of `mod A` lies in `add (D A)`.
* `FGModuleCat.projective_end_op_matlisDual_of_additiveClosure`: if `D A` lies in `add M`, then the
  dual `D M` is a projective right module over the endomorphism ring of `M`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

noncomputable section

open CategoryTheory Opposite TauCeti TauCeti.MatlisDual

universe u v t w

namespace TauCeti

open ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E}

section Duality

variable {A : Type t} [Ring A] [Algebra R A] [Module.Finite R A]

/-- **Matlis duality for Artin algebras.** For an injective hull `E` of `R ⧸ J(R)`, the dual
`D_R = Hom_R(-, E)` is an anti-equivalence between the finitely generated left and the finitely
generated right modules over an Artin `R`-algebra `A`. -/
@[expose]
def IsInjectiveEnvelope.fgModuleCatMatlisDuality (hf : IsInjectiveEnvelope f) :
    (FGModuleCat.{v} A)ᵒᵖ ≌ FGModuleCat.{v} Aᵐᵒᵖ :=
  have := hf.moduleInjective
  matlisDualityOn.{u, v, v, t} hf.length_quotient_linearMap_eq_one (isFG A) (isFG Aᵐᵒᵖ)
    (fun M (_ : Module.Finite A M) ↦ isFiniteLength_of_finite_trans R A M)
    (fun N (_ : Module.Finite Aᵐᵒᵖ N) ↦ isFiniteLength_of_finite_trans R Aᵐᵒᵖ N)
    (fun M (_ : Module.Finite A M) ↦
      have := hf.finite_op_matlisDual (A := A) (N := M)
      Module.Finite.equiv (matlisDualObjEquiv R E M).symm)
    (fun N (_ : Module.Finite Aᵐᵒᵖ N) ↦
      have := hf.finite_matlisDual_of_finite_op (A := A) (N := N)
      Module.Finite.equiv (matlisDualOpObjEquiv R E N).symm)

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_functor_obj_obj (hf : IsInjectiveEnvelope f)
    (M : (FGModuleCat.{v} A)ᵒᵖ) :
    (hf.fgModuleCatMatlisDuality.functor.obj M).obj = matlisDualObj R E M.unop.obj :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_functor_map_hom (hf : IsInjectiveEnvelope f)
    {M M' : (FGModuleCat.{v} A)ᵒᵖ} (g : M ⟶ M') :
    (hf.fgModuleCatMatlisDuality.functor.map g).hom = matlisDualMap R E g.unop.hom :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_inverse_obj_unop_obj
    (hf : IsInjectiveEnvelope f) (N : FGModuleCat.{v} Aᵐᵒᵖ) :
    (hf.fgModuleCatMatlisDuality.inverse.obj N).unop.obj = matlisDualOpObj R E N.obj :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_inverse_map_unop_hom
    (hf : IsInjectiveEnvelope f) {N N' : FGModuleCat.{v} Aᵐᵒᵖ} (g : N ⟶ N') :
    (hf.fgModuleCatMatlisDuality.inverse.map g).unop.hom = matlisDualOpMap R E g.hom :=
  rfl

/-- The unit of the Matlis duality is evaluation `M → D_R (D_R M)`. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_unitIso_inv_app (hf : IsInjectiveEnvelope f)
    (M : (FGModuleCat.{v} A)ᵒᵖ) :
    ((hf.fgModuleCatMatlisDuality (A := A)).unitIso.inv.app M).unop.hom =
      have := hf.moduleInjective
      (matlisDualEvalIso hf.length_quotient_linearMap_eq_one M.unop.obj
        (isFiniteLength_of_finite_trans R A M.unop.obj)).hom :=
  rfl

/-- The inverse of the counit of the Matlis duality is evaluation `N → D_R (D_R N)`. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_counitIso_inv_app (hf : IsInjectiveEnvelope f)
    (N : FGModuleCat.{v} Aᵐᵒᵖ) :
    ((hf.fgModuleCatMatlisDuality (A := A)).counitIso.inv.app N).hom =
      have := hf.moduleInjective
      (matlisDualEvalIsoOp (A := A) hf.length_quotient_linearMap_eq_one N.obj
        (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N.obj)).hom :=
  rfl

end Duality

section Regular

variable {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A]

/-- The Matlis dual `D A = Hom_R(A, E)` of the right regular module, as a finitely generated left
`A`-module: the image of the regular right module `Aᵐᵒᵖ` under the Matlis duality
`(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`. Defining it through the duality, rather than as the module
`Hom_R(A, E)`, makes the statements about `D A` the duals of the statements about the regular
module. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualRegular (hf : IsInjectiveEnvelope f) :
    FGModuleCat.{v} A :=
  ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).unop

theorem IsInjectiveEnvelope.fgModuleCatMatlisDualRegular_def (hf : IsInjectiveEnvelope f) :
    hf.fgModuleCatMatlisDualRegular (A := A) =
      ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).unop :=
  (rfl)

/-- The underlying module of `D A` is the Matlis dual of the regular right module. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualRegular_obj (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDualRegular (A := A)).obj =
      matlisDualOpObj R E (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := by
  rw [fgModuleCatMatlisDualRegular_def, fgModuleCatMatlisDuality_inverse_obj_unop_obj]

/-- The underlying module of `D A` is the Matlis dual `Hom_R(A, E)` of the right regular module
`Aᵐᵒᵖ`. The two sides differ only in the `R`-action on `Aᵐᵒᵖ`: through the algebra map in `D A`, and
the usual one in `MatlisDual R E Aᵐᵒᵖ`. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualRegularEquiv (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDualRegular (A := A)).obj ≃ₗ[A] MatlisDual R E Aᵐᵒᵖ :=
  (eqToIso hf.fgModuleCatMatlisDualRegular_obj).toLinearEquiv.trans <|
    (matlisDualOpObjEquiv R E (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).trans
      -- The `R`-action on `ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ` is passed explicitly: instance search would find
      -- the usual action on `Aᵐᵒᵖ` instead of the action through the algebra map.
      (@MatlisDual.congrOp R _ E _ _ A _ _ Aᵐᵒᵖ _ _ _ _ (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _
        (moduleOfAlgebra R _) _ (isScalarTower_moduleOfAlgebra R _) (LinearEquiv.refl _ _))

/-- `fgModuleCatMatlisDualRegularEquiv` is `ModuleCat.matlisDualOpObjEquiv` for the regular right
module, read through `fgModuleCatMatlisDualRegular_obj`. -/
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualRegularEquiv_apply (hf : IsInjectiveEnvelope f)
    (φ : (hf.fgModuleCatMatlisDualRegular (A := A)).obj) (a : Aᵐᵒᵖ) :
    equivLinearMap R E Aᵐᵒᵖ (hf.fgModuleCatMatlisDualRegularEquiv φ) a =
      -- The `R`-action on `ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ` is passed explicitly, as in
      -- `fgModuleCatMatlisDualRegularEquiv`.
      @equivLinearMap R _ E _ _ (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _ (moduleOfAlgebra R _)
        (matlisDualOpObjEquiv R E _ ((eqToHom hf.fgModuleCatMatlisDualRegular_obj).hom φ)) a := by
  simp [fgModuleCatMatlisDualRegularEquiv]

/-- The Matlis dual of `D A` is the regular right module, by evaluation. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso
    (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDuality (A := A)).functor.obj (op hf.fgModuleCatMatlisDualRegular) ≅
      FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ :=
  (hf.fgModuleCatMatlisDuality (A := A)).functor.mapIso
      (eqToIso (congrArg op hf.fgModuleCatMatlisDualRegular_def)) ≪≫
    (hf.fgModuleCatMatlisDuality (A := A)).counitIso.app (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)

/-- `D (D A) ≅ Aᵐᵒᵖ` is the counit of the Matlis duality at the regular right module. -/
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso_def
    (hf : IsInjectiveEnvelope f) :
    hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A) =
      (hf.fgModuleCatMatlisDuality (A := A)).functor.mapIso
          (eqToIso (congrArg op hf.fgModuleCatMatlisDualRegular_def)) ≪≫
        (hf.fgModuleCatMatlisDuality (A := A)).counitIso.app (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) :=
  (rfl)

/-- The inverse of `D (D A) ≅ Aᵐᵒᵖ` sends `a` to evaluation at `a`. A pre-simp lemma
(`simp↓`): it applies before `fgModuleCatMatlisDuality_functor_obj_obj` rewrites the type of the
morphism. -/
@[simp↓]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso_inv_apply
    (hf : IsInjectiveEnvelope f) (a : Aᵐᵒᵖ) (φ : (hf.fgModuleCatMatlisDualRegular (A := A)).obj) :
    equivLinearMap R E _
      (matlisDualObjEquiv R E (hf.fgModuleCatMatlisDualRegular (A := A)).obj
        ((hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A)).inv.hom a)) φ =
      equivLinearMap R E Aᵐᵒᵖ (hf.fgModuleCatMatlisDualRegularEquiv φ) a := by
  have := hf.moduleInjective
  simp only [fgModuleCatMatlisDualRegularEquiv_apply,
    fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso_def, Iso.trans_inv, Iso.app_inv,
    ObjectProperty.FullSubcategory.comp_hom, fgModuleCatMatlisDuality_counitIso_inv_app,
    Functor.mapIso_inv, eqToIso.inv, eqToHom_map]
  -- The casts along `fgModuleCatMatlisDualRegular_def` and `fgModuleCatMatlisDualRegular_obj` are
  -- identities here, where `D A` unfolds to the dual of the regular right module.
  exact ModuleCat.matlisDualEvalIsoOp_hom_apply (A := A) hf.length_quotient_linearMap_eq_one
    (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _ a φ

/-- `D A` is an injective object of `mod A`, as the dual of the projective right module `Aᵐᵒᵖ`. -/
instance IsInjectiveEnvelope.injective_fgModuleCatMatlisDualRegular (hf : IsInjectiveEnvelope f) :
    Injective (hf.fgModuleCatMatlisDualRegular (A := A)) := by
  have : Projective (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := FGModuleCat.projective_of_free Aᵐᵒᵖ _
  have : Projective ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj
      (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) :=
    (hf.fgModuleCatMatlisDuality.symm.map_projective_iff _).2 inferInstance
  exact inferInstanceAs (Injective (unop _))

/-- **Finitely generated injective modules are summands of finite sums of `D A`**: an injective
object of `mod A` lies in `add (D A)`. This is the dual of the
statement that finitely generated projective modules over `Aᵐᵒᵖ` lie in `add Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.additiveClosure_fgModuleCatMatlisDualRegular_of_injective
    (hf : IsInjectiveEnvelope f) (I : FGModuleCat.{v} A) [Injective I] :
    additiveClosure (hf.fgModuleCatMatlisDualRegular (A := A)) I := by
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have : Projective (Φ.functor.obj (op I)) := (Φ.map_projective_iff _).2 inferInstance
  rw [← Φ.additiveClosure_functor_obj_op_iff]
  exact (hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A)).symm.retract
    |>.additiveClosure_le _
      (FGModuleCat.additiveClosure_of_isGenerator_of_projective (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)
        (Φ.functor.obj (op I)))

end Regular

section EndOp

attribute [local instance] RingHomInvPair.of_ringEquiv

open MatlisDual

/-- **Duals of `add M` and projectivization**: if an object `X` of `add M` has as underlying module
the dual `D_R A` of the right regular module, then the dual `D_R M` is a projective right module
over `Γ = Module.End A M`. By projectivization `Hom_A(M, X)` is a projective right `Γ`-module, and
the Hom-tensor adjunction `TauCeti.MatlisDual.equivLinearMapDualRegular` identifies it with
`D_R M`. -/
theorem _root_.FGModuleCat.projective_end_op_matlisDual_of_additiveClosure {R : Type*} [CommRing R]
    {E : Type*} [AddCommGroup E] [Module R E] {A : Type*} [Ring A] [Algebra R A]
    {M X : FGModuleCat.{w} A} [Module R M.obj] [IsScalarTower R A M.obj]
    (hX : additiveClosure M X) (e : X.obj ≃ₗ[A] MatlisDual R E A) :
    Module.Projective (Module.End A M.obj)ᵐᵒᵖ (MatlisDual R E M.obj) := by
  -- By projectivization, `Hom(M, X)` is a projective right module over `End M`.
  have : Module.Projective (End M)ᵐᵒᵖ (M ⟶ X) :=
    (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj hX)).2
  -- Postcomposition with `e` and the Hom-tensor adjunction identify `Hom(M, X)` with `D_R M`,
  -- semilinearly along the isomorphism `(End M)ᵐᵒᵖ ≅ Γᵐᵒᵖ`.
  let σ := RingEquiv.op (FGModuleCat.endRingEquiv M)
  let e' : (M ⟶ X) ≃ₛₗ[(σ : (End M)ᵐᵒᵖ →+* (Module.End A M.obj)ᵐᵒᵖ)]
      MatlisDual R E M.obj :=
    { toFun f := equivLinearMapDualRegular.symm (e.toLinearMap ∘ₗ f.hom.hom)
      invFun φ := ObjectProperty.homMk
        (ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ equivLinearMapDualRegular φ))
      map_add' f g := by simp [LinearMap.comp_add]
      map_smul' g f := by
        apply (equivLinearMapDualRegular (A := A)).injective
        -- The right action of `Γ` on `D_R M` is dualization of endomorphisms.
        have hσ (γ : (Module.End A M.obj)ᵐᵒᵖ) (φ : MatlisDual R E M.obj) :
            γ • φ = MatlisDual.map γ.unop φ :=
          MatlisDual.ext fun x ↦ by simp [Module.End.smul_def]
        rw [hσ, equivLinearMapDualRegular_map, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
        ext x
        simp [End.smul_left, σ]
      left_inv f := by
        ext x
        simp
      right_inv φ := by
        simp }
  exact .of_equiv e'

end EndOp

end TauCeti
