/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual
public import TauCeti.RingTheory.Artinian.FiniteLength
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# The Matlis duality between left and right modules over an Artin algebra

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra. This file restricts the Matlis dual `D_R = Hom_R(-, E)` of
`TauCeti/Algebra/Category/ModuleCat/MatlisDual.lean` to an anti-equivalence between the finitely
generated left `A`-modules and the finitely generated right `A`-modules, the modules over `Aᵐᵒᵖ`.

## Main definitions

* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDual` and
  `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualOp`: `D_R` on finitely generated left and right
  modules.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`: the anti-equivalence
  `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`, whose unit and counit are evaluation.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

noncomputable section

open CategoryTheory Opposite TauCeti TauCeti.MatlisDual

universe u v t

namespace TauCeti

open ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t} [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- The Matlis dual as a functor from finitely generated left to finitely generated right
modules. -/
@[expose]
def IsInjectiveEnvelope.fgModuleCatMatlisDual (hf : IsInjectiveEnvelope f) :
    (FGModuleCat.{v} A)ᵒᵖ ⥤ FGModuleCat.{v} Aᵐᵒᵖ :=
  ObjectProperty.lift _ ((ModuleCat.isFG A).ι.op ⋙ ModuleCat.matlisDual R E) fun M =>
    have := hf.finite_op_matlisDual (A := A) (N := M.unop)
    Module.Finite.equiv (matlisDualObjEquiv R E M.unop.obj).symm

/-- The Matlis dual as a functor from finitely generated right to finitely generated left
modules. -/
@[expose]
def IsInjectiveEnvelope.fgModuleCatMatlisDualOp (hf : IsInjectiveEnvelope f) :
    (FGModuleCat.{v} Aᵐᵒᵖ)ᵒᵖ ⥤ FGModuleCat.{v} A :=
  ObjectProperty.lift _ ((ModuleCat.isFG Aᵐᵒᵖ).ι.op ⋙ ModuleCat.matlisDualOp R E) fun N =>
    have := hf.finite_matlisDual_of_finite_op (A := A) (N := N.unop)
    Module.Finite.equiv (matlisDualOpObjEquiv R E N.unop.obj).symm

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDual_obj_obj (hf : IsInjectiveEnvelope f)
    (M : (FGModuleCat.{v} A)ᵒᵖ) :
    (hf.fgModuleCatMatlisDual.obj M).obj = matlisDualObj R E M.unop.obj :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDual_map_hom (hf : IsInjectiveEnvelope f)
    {M M' : (FGModuleCat.{v} A)ᵒᵖ} (g : M ⟶ M') :
    (hf.fgModuleCatMatlisDual.map g).hom = matlisDualMap R E g.unop.hom :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualOp_obj_obj (hf : IsInjectiveEnvelope f)
    (N : (FGModuleCat.{v} Aᵐᵒᵖ)ᵒᵖ) :
    (hf.fgModuleCatMatlisDualOp.obj N).obj = matlisDualOpObj R E N.unop.obj :=
  rfl

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualOp_map_hom (hf : IsInjectiveEnvelope f)
    {N N' : (FGModuleCat.{v} Aᵐᵒᵖ)ᵒᵖ} (g : N ⟶ N') :
    (hf.fgModuleCatMatlisDualOp.map g).hom = matlisDualOpMap R E g.unop.hom :=
  rfl

/-- **Matlis duality for Artin algebras.** For an injective hull `E` of `R ⧸ J(R)`, the dual
`D_R = Hom_R(-, E)` is an anti-equivalence between the finitely generated left and the finitely
generated right modules over an Artin `R`-algebra `A`. -/
@[expose]
def IsInjectiveEnvelope.fgModuleCatMatlisDuality (hf : IsInjectiveEnvelope f) :
    (FGModuleCat.{v} A)ᵒᵖ ≌ FGModuleCat.{v} Aᵐᵒᵖ where
  functor := hf.fgModuleCatMatlisDual
  inverse := hf.fgModuleCatMatlisDualOp.rightOp
  unitIso := NatIso.ofComponents (fun M =>
      (ObjectProperty.isoMk _ (hf.moduleCatEvalIso M.unop.obj
        (isFiniteLength_of_finite_trans R A M.unop.obj))).symm.op)
    (fun g => Quiver.Hom.unop_inj <| (Iso.inv_comp_eq _).mpr <|
      ((Iso.eq_comp_inv _).mpr <| ObjectProperty.hom_ext _ <|
        hf.moduleCatEvalIso_hom_naturality g.unop.hom _ _).trans (Category.assoc _ _ _))
  counitIso := NatIso.ofComponents (fun N =>
      (ObjectProperty.isoMk _ (hf.moduleCatEvalIsoOp (A := A) N.obj
        (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N.obj))).symm)
    (fun g => (Iso.comp_inv_eq _).mpr <| ((Iso.eq_inv_comp _).mpr <|
      (ObjectProperty.hom_ext _ <|
        hf.moduleCatEvalIsoOp_hom_naturality (A := A) g.hom _ _).symm).trans
        (Category.assoc _ _ _).symm)
  functor_unitIso_comp M := by
    refine ObjectProperty.hom_ext _ ?_
    exact (Iso.comp_inv_eq_id (hf.moduleCatEvalIsoOp (A := A) (hf.fgModuleCatMatlisDual.obj M).obj
      (isFiniteLength_of_finite_trans R Aᵐᵒᵖ _))).mpr
      (hf.moduleCatEvalIsoOp_matlisDualObj_hom M.unop.obj
        (isFiniteLength_of_finite_trans R A M.unop.obj) _).symm

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_functor (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDuality (A := A)).functor = hf.fgModuleCatMatlisDual :=
  (rfl)

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_inverse (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDuality (A := A)).inverse = hf.fgModuleCatMatlisDualOp.rightOp :=
  (rfl)

/-- The unit of the Matlis duality is evaluation `M → D_R (D_R M)`. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_unitIso_inv_app (hf : IsInjectiveEnvelope f)
    (M : (FGModuleCat.{v} A)ᵒᵖ) :
    ((hf.fgModuleCatMatlisDuality (A := A)).unitIso.inv.app M).unop.hom =
      (hf.moduleCatEvalIso M.unop.obj
        (isFiniteLength_of_finite_trans R A M.unop.obj)).hom :=
  (rfl)

/-- The inverse of the counit of the Matlis duality is evaluation `N → D_R (D_R N)`. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_counitIso_inv_app (hf : IsInjectiveEnvelope f)
    (N : FGModuleCat.{v} Aᵐᵒᵖ) :
    ((hf.fgModuleCatMatlisDuality (A := A)).counitIso.inv.app N).hom =
      (hf.moduleCatEvalIsoOp (A := A) N.obj
        (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N.obj)).hom :=
  (rfl)

end TauCeti
