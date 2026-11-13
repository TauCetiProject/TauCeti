/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality
public import TauCeti.RingTheory.Artinian.FiniteLength
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# The Matlis duality between left and right modules over an Artin algebra

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra. Over `A` the finitely generated modules are the modules of finite length over
`R`, so the Matlis duality `ModuleCat.matlisDualityOn` of
`TauCeti/Algebra/Category/ModuleCat/MatlisDuality.lean` restricts to an anti-equivalence between
the finitely generated left `A`-modules and the finitely generated right `A`-modules, the modules
over `Aᵐᵒᵖ`.

## Main definitions

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

end TauCeti
