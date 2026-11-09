/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# The Matlis duality between left and right modules over an Artin algebra

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra. This file packages the Matlis dual `D_R = Hom_R(-, E)` of
`TauCeti/RingTheory/MatlisDuality/ArtinAlgebra.lean` as an anti-equivalence between the finitely
generated left `A`-modules and the finitely generated right `A`-modules, the modules over `Aᵐᵒᵖ`.

## Main definitions

* `ModuleCat.matlisDual` and `ModuleCat.matlisDualOp`: `D_R` as a contravariant additive functor
  from left to right modules and from right to left modules.
* `TauCeti.IsInjectiveEnvelope.moduleCatEvalIso` and
  `TauCeti.IsInjectiveEnvelope.moduleCatEvalIsoOp`: biduality for bundled modules of finite length.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`: the anti-equivalence
  `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`.

## Implementation notes

A module over an `R`-algebra `A` is bundled in `ModuleCat A`, which remembers only the action of
`A`, so its `R`-action is recovered through the algebra map, by `ModuleCat.moduleOfAlgebra`. On the
dual of a module this equals the `R`-action on the values only propositionally, not definitionally.
As in `ModuleCat.rightScalarDual`, the bundled duals `ModuleCat.matlisDualObj` and
`ModuleCat.matlisDualOpObj` are therefore not reducible to `MatlisDual`, and are compared with it by
`ModuleCat.matlisDualObjEquiv` and `ModuleCat.matlisDualOpObjEquiv`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

noncomputable section

open CategoryTheory Opposite TauCeti TauCeti.MatlisDual

universe u v t

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- A module over an `R`-algebra, as a module over `R`. Mathlib records this for algebras over a
field in `ModuleCat.moduleOfAlgebraModule`. -/
abbrev moduleOfAlgebra {B : Type t} [Ring B] [Algebra R B] (M : ModuleCat.{v} B) : Module R M :=
  Module.restrictScalars R B M

attribute [local instance] moduleOfAlgebra

/-- The action of `R` given by `ModuleCat.moduleOfAlgebra` is the action through the algebra map. -/
theorem isScalarTower_moduleOfAlgebra {B : Type t} [Ring B] [Algebra R B] (M : ModuleCat.{v} B) :
    IsScalarTower R B M :=
  IsScalarTower.restrictScalars R B M

attribute [local instance] isScalarTower_moduleOfAlgebra

variable {A : Type t} [Ring A] [Algebra R A] (E : Type v) [AddCommGroup E] [Module R E]

section Left

/-- The Matlis dual of a left `A`-module, as a bundled right `A`-module. -/
def matlisDualObj (M : ModuleCat.{v} A) : ModuleCat.{v} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (MatlisDual R E M)

/-- The underlying module of the bundled dual of a left module is its Matlis dual. -/
def matlisDualObjEquiv (M : ModuleCat.{v} A) : matlisDualObj R E M ≃ₗ[Aᵐᵒᵖ] MatlisDual R E M :=
  LinearEquiv.refl _ _

/-- The dual of a morphism of left modules. -/
def matlisDualMap {M M' : ModuleCat.{v} A} (g : M ⟶ M') :
    matlisDualObj R E M' ⟶ matlisDualObj R E M :=
  ModuleCat.ofHom ((matlisDualObjEquiv R E M).symm.toLinearMap ∘ₗ mapOp g.hom ∘ₗ
    (matlisDualObjEquiv R E M').toLinearMap)

@[simp]
theorem matlisDualObjEquiv_map_apply {M M' : ModuleCat.{v} A} (g : M ⟶ M')
    (φ : matlisDualObj R E M') (x : M) :
    equivLinearMap R E M (matlisDualObjEquiv R E M (matlisDualMap R E g φ)) x =
      equivLinearMap R E M' (matlisDualObjEquiv R E M' φ) (g x) :=
  mapOp_apply g.hom (matlisDualObjEquiv R E M' φ) x

/-- The Matlis dual `D_R = Hom_R(-, E)`, from left to right `A`-modules. -/
@[expose, simps]
def matlisDual : (ModuleCat.{v} A)ᵒᵖ ⥤ ModuleCat.{v} Aᵐᵒᵖ where
  obj M := matlisDualObj R E M.unop
  map g := matlisDualMap R E g.unop
  map_id M := by
    ext φ
    apply (matlisDualObjEquiv R E M.unop).injective
    ext x
    simp
  map_comp g h := by
    ext φ
    apply (matlisDualObjEquiv R E _).injective
    ext x
    simp

theorem matlisDualMap_add {M M' : ModuleCat.{v} A} (g h : M ⟶ M') :
    matlisDualMap R E (g + h) = matlisDualMap R E g + matlisDualMap R E h := by
  ext φ
  apply (matlisDualObjEquiv R E _).injective
  ext x
  refine (matlisDualObjEquiv_map_apply R E (g + h) φ x).trans ?_
  simp [ModuleCat.hom_add, map_add]

instance : (matlisDual R E (A := A)).Additive where
  map_add := matlisDualMap_add R E _ _

end Left

section Right

/-- The Matlis dual of a right `A`-module, as a bundled left `A`-module. -/
def matlisDualOpObj (N : ModuleCat.{v} Aᵐᵒᵖ) : ModuleCat.{v} A :=
  ModuleCat.of A (MatlisDual R E N)

/-- The underlying module of the bundled dual of a right module is its Matlis dual. -/
def matlisDualOpObjEquiv (N : ModuleCat.{v} Aᵐᵒᵖ) : matlisDualOpObj R E N ≃ₗ[A] MatlisDual R E N :=
  LinearEquiv.refl _ _

/-- The dual of a morphism of right modules. -/
def matlisDualOpMap {N N' : ModuleCat.{v} Aᵐᵒᵖ} (g : N ⟶ N') :
    matlisDualOpObj R E N' ⟶ matlisDualOpObj R E N :=
  ModuleCat.ofHom ((matlisDualOpObjEquiv R E N).symm.toLinearMap ∘ₗ map g.hom ∘ₗ
    (matlisDualOpObjEquiv R E N').toLinearMap)

@[simp]
theorem matlisDualOpObjEquiv_map_apply {N N' : ModuleCat.{v} Aᵐᵒᵖ} (g : N ⟶ N')
    (φ : matlisDualOpObj R E N') (x : N) :
    equivLinearMap R E N (matlisDualOpObjEquiv R E N (matlisDualOpMap R E g φ)) x =
      equivLinearMap R E N' (matlisDualOpObjEquiv R E N' φ) (g x) :=
  map_apply g.hom (matlisDualOpObjEquiv R E N' φ) x

/-- The Matlis dual `D_R = Hom_R(-, E)`, from right to left `A`-modules. -/
@[expose, simps]
def matlisDualOp : (ModuleCat.{v} Aᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{v} A where
  obj N := matlisDualOpObj R E N.unop
  map g := matlisDualOpMap R E g.unop
  map_id N := by
    ext φ
    apply (matlisDualOpObjEquiv R E N.unop).injective
    ext x
    simp
  map_comp g h := by
    ext φ
    apply (matlisDualOpObjEquiv R E _).injective
    ext x
    simp

theorem matlisDualOpMap_add {N N' : ModuleCat.{v} Aᵐᵒᵖ} (g h : N ⟶ N') :
    matlisDualOpMap R E (g + h) = matlisDualOpMap R E g + matlisDualOpMap R E h := by
  ext φ
  apply (matlisDualOpObjEquiv R E _).injective
  ext x
  refine (matlisDualOpObjEquiv_map_apply R E (g + h) φ x).trans ?_
  simp [ModuleCat.hom_add, map_add]

instance : (matlisDualOp R E (A := A)).Additive where
  map_add := matlisDualOpMap_add R E _ _

end Right

end ModuleCat

namespace TauCeti

open ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

section Eval

variable {R : Type u} [CommRing R] [IsSemisimpleRing (R ⧸ Ring.jacobson R)] {E : Type v}
  [AddCommGroup E] [Module R E] [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t}
  [Ring A] [Algebra R A] (hf : IsInjectiveEnvelope f)

include hf

/-- Matlis biduality for a left `A`-module `M` of finite length over `R`, as an isomorphism
`M ≅ D_R (D_R M)` of bundled modules. -/
def IsInjectiveEnvelope.moduleCatEvalIso (M : ModuleCat.{v} A) (hM : IsFiniteLength R M) :
    M ≅ matlisDualOpObj R E (matlisDualObj R E M) :=
  ((hf.matlisDualEvalEquiv hM).trans
    ((MatlisDual.congr (matlisDualObjEquiv R E M)).trans
      (matlisDualOpObjEquiv R E (matlisDualObj R E M)).symm)).toModuleIso

/-- The isomorphism `M ≅ D_R (D_R M)` is evaluation. -/
@[simp]
theorem IsInjectiveEnvelope.moduleCatEvalIso_hom_apply (M : ModuleCat.{v} A)
    (hM : IsFiniteLength R M) (x : M) (φ : matlisDualObj R E M) :
    equivLinearMap R E _ (matlisDualOpObjEquiv R E _ ((hf.moduleCatEvalIso M hM).hom x)) φ =
      equivLinearMap R E M (matlisDualObjEquiv R E M φ) x := by
  simp [moduleCatEvalIso]

/-- Matlis biduality for a right `A`-module `N` of finite length over `R`, as an isomorphism
`N ≅ D_R (D_R N)` of bundled modules. -/
def IsInjectiveEnvelope.moduleCatEvalIsoOp (N : ModuleCat.{v} Aᵐᵒᵖ) (hN : IsFiniteLength R N) :
    N ≅ matlisDualObj R E (matlisDualOpObj R E N) :=
  ((hf.matlisDualEvalEquivOp (A := A) hN).trans
    ((MatlisDual.congrOp (matlisDualOpObjEquiv R E N)).trans
      (matlisDualObjEquiv R E (matlisDualOpObj R E N)).symm)).toModuleIso

/-- The isomorphism `N ≅ D_R (D_R N)` is evaluation. -/
@[simp]
theorem IsInjectiveEnvelope.moduleCatEvalIsoOp_hom_apply (N : ModuleCat.{v} Aᵐᵒᵖ)
    (hN : IsFiniteLength R N) (x : N) (φ : matlisDualOpObj R E N) :
    equivLinearMap R E _ (matlisDualObjEquiv R E _ ((hf.moduleCatEvalIsoOp N hN).hom x)) φ =
      equivLinearMap R E N (matlisDualOpObjEquiv R E N φ) x := by
  simp [moduleCatEvalIsoOp]

/-- The isomorphism `M ≅ D_R (D_R M)` is natural in `M`. -/
theorem IsInjectiveEnvelope.moduleCatEvalIso_hom_naturality {M M' : ModuleCat.{v} A} (g : M ⟶ M')
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    g ≫ (hf.moduleCatEvalIso M' hM').hom =
      (hf.moduleCatEvalIso M hM).hom ≫ matlisDualOpMap R E (matlisDualMap R E g) := by
  ext x
  apply (matlisDualOpObjEquiv R E _).injective
  ext φ
  simp

/-- The isomorphism `N ≅ D_R (D_R N)` is natural in `N`. -/
theorem IsInjectiveEnvelope.moduleCatEvalIsoOp_hom_naturality {N N' : ModuleCat.{v} Aᵐᵒᵖ}
    (g : N ⟶ N') (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    g ≫ (hf.moduleCatEvalIsoOp N' hN').hom =
      (hf.moduleCatEvalIsoOp N hN).hom ≫ matlisDualMap R E (matlisDualOpMap R E g) := by
  ext x
  apply (matlisDualObjEquiv R E _).injective
  ext φ
  simp

end Eval

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t} [Ring A] [Algebra R A]
  [Module.Finite R A]

omit [Small.{v} R] [Algebra R A] [Module.Finite R A] in
/-- A finitely generated module over an Artin algebra has finite length over the base. -/
private theorem isFiniteLength_fgModuleCat {B : Type t} [Ring B] [Algebra R B] [Module.Finite R B]
    (M : FGModuleCat.{v} B) : IsFiniteLength R M :=
  have : Module.Finite R M := Module.Finite.trans B M
  IsArtinianRing.isFiniteLength_of_finite R M

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
def IsInjectiveEnvelope.fgModuleCatMatlisDuality (hf : IsInjectiveEnvelope f) :
    (FGModuleCat.{v} A)ᵒᵖ ≌ FGModuleCat.{v} Aᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk hf.fgModuleCatMatlisDual hf.fgModuleCatMatlisDualOp.rightOp
    (NatIso.ofComponents (fun M =>
      (ObjectProperty.isoMk _ (hf.moduleCatEvalIso M.unop.obj
        (isFiniteLength_fgModuleCat M.unop))).symm.op)
      (fun g => Quiver.Hom.unop_inj <| (Iso.inv_comp_eq _).mpr <|
        ((Iso.eq_comp_inv _).mpr <| ObjectProperty.hom_ext _ <|
          hf.moduleCatEvalIso_hom_naturality g.unop.hom _ _).trans (Category.assoc _ _ _)))
    (NatIso.ofComponents (fun N =>
      (ObjectProperty.isoMk _ (hf.moduleCatEvalIsoOp (A := A) N.obj
        (isFiniteLength_fgModuleCat N))).symm)
      (fun g => (Iso.comp_inv_eq _).mpr <| ((Iso.eq_inv_comp _).mpr <|
        (ObjectProperty.hom_ext _ <|
          hf.moduleCatEvalIsoOp_hom_naturality (A := A) g.hom _ _).symm).trans
          (Category.assoc _ _ _).symm))

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_functor (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDuality (A := A)).functor = hf.fgModuleCatMatlisDual :=
  (rfl)

@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDuality_inverse (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDuality (A := A)).inverse = hf.fgModuleCatMatlisDualOp.rightOp :=
  (rfl)

end TauCeti
