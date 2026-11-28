/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.FiniteBiproducts
public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.RestrictedYoneda

/-!
# Finitely presented modules as finitely presented functors

Because a module is finitely presented exactly when it is the cokernel of a morphism between
finitely generated projective modules (`TauCeti.presented_finiteProjectiveModules`), the Yoneda
description of finitely presented functors on a category of projective objects identifies the
finitely presented `R`-modules with `mod (proj R)`, the finitely presented functors on the category
of finitely generated projective `R`-modules. Evaluating a functor `F` in `mod (proj R)` at the
regular module `R` with the `R`-action induced by right multiplication on `R` gives the inverse
equivalence.

## Main definitions

* `TauCeti.finitePresentationEquivalenceMod`: the equivalence between the finitely presented
  `R`-modules and `mod (proj R)`.
* `TauCeti.finitePresentationEquivalenceModCompιIso`: the forward functor is `M ↦ (-, M)|_{proj R}`.
* `TauCeti.finitePresentationEquivalenceModCompEvaluationIso`: the composite of this equivalence
  with evaluation at `R` is the underlying abelian group of a module.
* `TauCeti.finitePresentationEvaluationFunctor`: evaluation at the regular module `R`, equipped
  with the `R`-action induced by right multiplication on `R`.
* `TauCeti.finitePresentationEvaluationFunctorCompForgetIso`: the underlying abelian group of
  `TauCeti.finitePresentationEvaluationFunctor` is evaluation at `R`.
* `TauCeti.finitePresentationEvaluationFunctorIso`: `TauCeti.finitePresentationEvaluationFunctor`
  is naturally isomorphic to `(TauCeti.finitePresentationEquivalenceMod R).inverse`.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer (1966), 189–231.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace TauCeti

variable (R : Type u) [Ring R]

/-- **The finitely presented modules are `mod (proj R)`.** The functor `M ↦ (-, M)|_{proj R}` is an
equivalence from the finitely presented `R`-modules to the finitely presented functors on the
finitely generated projective `R`-modules. -/
noncomputable def finitePresentationEquivalenceMod :
    (finitePresentationModules R).FullSubcategory ≌
      (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory :=
  ObjectProperty.equivalenceMod (finiteProjectiveModules_le_categoryTheory_isProjective R)
    (presented_finiteProjectiveModules R).symm

/-- The functor of `finitePresentationEquivalenceMod` is `M ↦ (-, M)|_{proj R}`. -/
noncomputable def finitePresentationEquivalenceModCompιIso :
    (finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      (finitePresentationModules R).ι ⋙ (finiteProjectiveModules R).restrictedPreadditiveYoneda :=
  ObjectProperty.equivalenceModCompιIso _ _

private def finitePresentationEvalComp (M : (finitePresentationModules R).FullSubcategory) :
    ((finitePresentationModules R).ι ⋙
        (finiteProjectiveModules R).restrictedPreadditiveYoneda ⋙
        (evaluation _ _).obj (op (finiteProjectiveModulesRegular R))).obj M ≅
      ((finitePresentationModules R).ι ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M :=
  (ModuleCat.homAddEquiv.trans
    (LinearMap.ringLmapEquivSelf R ℕ M.obj).toAddEquiv).toAddCommGrpIso

private theorem finitePresentationEvalComp_hom_apply
    (M : (finitePresentationModules R).FullSubcategory)
    (g : ((finiteProjectiveModules R).restrictedPreadditiveYoneda.obj M.obj).obj
      (op (finiteProjectiveModulesRegular R))) :
    (finitePresentationEvalComp R M).hom g =
      (g : (finiteProjectiveModulesRegular R).obj ⟶ M.obj).hom (1 : R) :=
  rfl

/-- The functor attached to a finitely presented `R`-module `M` takes the value `(R, M)` at the
regular module, and `(R, M)` is the underlying abelian group of `M`, naturally in `M`. -/
noncomputable def finitePresentationEquivalenceModCompEvaluationIso :
    ((finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι) ⋙
        (evaluation _ _).obj (op (finiteProjectiveModulesRegular R)) ≅
      (finitePresentationModules R).ι ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (finitePresentationEquivalenceModCompιIso R) _ ≪≫
    NatIso.ofComponents (finitePresentationEvalComp R) fun {M N} f ↦
      AddCommGrpCat.ext fun g ↦ by
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        dsimp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
          evaluation_obj_map]
        rw [finitePresentationEvalComp_hom_apply, finitePresentationEvalComp_hom_apply,
          (finiteProjectiveModules R).restrictedPreadditiveYoneda_map_app_apply f.hom
            (op (finiteProjectiveModulesRegular R)) g]
        exact ModuleCat.comp_apply (g : (finiteProjectiveModulesRegular R).obj ⟶ M.obj) f.hom _

/-- The forward comparison `TauCeti.finitePresentationEquivalenceModCompEvaluationIso` evaluates
the Yoneda-represented morphism at `1 : R` after applying
`TauCeti.finitePresentationEquivalenceModCompιIso`. -/
@[simp]
theorem finitePresentationEquivalenceModCompEvaluationIso_hom_app_apply
    (M : (finitePresentationModules R).FullSubcategory)
    (x : ((finitePresentationEquivalenceMod R).functor.obj M).obj.obj
      (op (finiteProjectiveModulesRegular R))) :
    dsimp% (finitePresentationEquivalenceModCompEvaluationIso R).hom.app M x =
      (((finitePresentationEquivalenceModCompιIso R).hom.app M).app
        (op (finiteProjectiveModulesRegular R)) x :
          (finiteProjectiveModulesRegular R).obj ⟶ M.obj).hom (1 : R) := by
  dsimp [finitePresentationEquivalenceModCompEvaluationIso]
  exact finitePresentationEvalComp_hom_apply R M _

private def finiteProjectiveModulesRegularMulRight (r : R) :
    finiteProjectiveModulesRegular R ⟶ finiteProjectiveModulesRegular R :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.mulRight R r))

private theorem finiteProjectiveModulesRegularMulRight_hom_apply (r x : R) :
    (finiteProjectiveModulesRegularMulRight R r).hom.hom x = x * r :=
  rfl

private theorem finiteProjectiveModulesRegularMulRight_one :
    finiteProjectiveModulesRegularMulRight R 1 = 𝟙 _ :=
  ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <| LinearMap.ext fun (x : R) ↦ mul_one x

private theorem finiteProjectiveModulesRegularMulRight_mul (r s : R) :
    finiteProjectiveModulesRegularMulRight R (r * s) =
      finiteProjectiveModulesRegularMulRight R r ≫
        finiteProjectiveModulesRegularMulRight R s :=
  ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <| LinearMap.ext fun (x : R) ↦
    (mul_assoc x r s).symm

private theorem finiteProjectiveModulesRegularMulRight_add (r s : R) :
    finiteProjectiveModulesRegularMulRight R (r + s) =
      finiteProjectiveModulesRegularMulRight R r +
        finiteProjectiveModulesRegularMulRight R s :=
  ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <| LinearMap.ext fun (x : R) ↦ mul_add x r s

private theorem finiteProjectiveModulesRegularMulRight_zero :
    finiteProjectiveModulesRegularMulRight R 0 = 0 :=
  ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <| LinearMap.ext fun (x : R) ↦ mul_zero x

private instance finitePresentationEvalSMul
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory) :
    SMul R (F.obj.obj (op (finiteProjectiveModulesRegular R))) where
  smul r x := (F.obj.map (finiteProjectiveModulesRegularMulRight R r).op).hom x

private theorem finitePresentationEvalSMul_def
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory)
    (r : R) (x : F.obj.obj (op (finiteProjectiveModulesRegular R))) :
    r • x = (F.obj.map (finiteProjectiveModulesRegularMulRight R r).op).hom x :=
  rfl

private instance finitePresentationEvalModuleInst
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory) :
    Module R (F.obj.obj (op (finiteProjectiveModulesRegular R))) where
  one_smul x := by
    rw [finitePresentationEvalSMul_def, finiteProjectiveModulesRegularMulRight_one]
    simp
  mul_smul r s x := by
    rw [finitePresentationEvalSMul_def, finitePresentationEvalSMul_def,
      finitePresentationEvalSMul_def, finiteProjectiveModulesRegularMulRight_mul]
    simp
  smul_zero _ := by
    rw [finitePresentationEvalSMul_def, map_zero]
  smul_add _ _ _ := by
    rw [finitePresentationEvalSMul_def, finitePresentationEvalSMul_def,
      finitePresentationEvalSMul_def, map_add]
  add_smul r s x := by
    have := F.property.additive
    rw [finitePresentationEvalSMul_def, finitePresentationEvalSMul_def,
      finitePresentationEvalSMul_def, finiteProjectiveModulesRegularMulRight_add, op_add,
      F.obj.map_add, AddCommGrpCat.hom_add, AddMonoidHom.add_apply]
  zero_smul x := by
    have := F.property.additive
    rw [finitePresentationEvalSMul_def, finiteProjectiveModulesRegularMulRight_zero, op_zero,
      F.obj.map_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]

private abbrev finitePresentationEvalModuleObj
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory) :
    ModuleCat.{u} R :=
  ModuleCat.of R (F.obj.obj (op (finiteProjectiveModulesRegular R)))

private def finitePresentationEvalModule :
    (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory ⥤
      ModuleCat.{u} R where
  obj := finitePresentationEvalModuleObj R
  map {F G} θ := ModuleCat.ofHom
    (X := finitePresentationEvalModuleObj R F) (Y := finitePresentationEvalModuleObj R G)
    { toFun := fun x ↦ (θ.hom.app (op (finiteProjectiveModulesRegular R))).hom x
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r x ↦ by
        rw [RingHom.id_apply, finitePresentationEvalSMul_def, finitePresentationEvalSMul_def]
        have hn := ConcreteCategory.congr_hom
          (θ.hom.naturality (finiteProjectiveModulesRegularMulRight R r).op) x
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
        exact hn }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

private noncomputable def finitePresentationEquivalenceModCompEvalModuleIso :
    (finitePresentationEquivalenceMod R).functor ⋙ finitePresentationEvalModule R ≅
      (finitePresentationModules R).ι :=
  NatIso.ofComponents
    (fun M ↦
      let f : finitePresentationEvalModuleObj R
          ((finitePresentationEquivalenceMod R).functor.obj M) →ₗ[R] M.obj :=
        { toFun := fun x ↦ (finitePresentationEquivalenceModCompEvaluationIso R).hom.app M x
          map_add' := fun _ _ ↦ map_add _ _ _
          map_smul' := fun r x ↦ by
            rw [RingHom.id_apply, finitePresentationEvalSMul_def,
              finitePresentationEquivalenceModCompEvaluationIso_hom_app_apply,
              finitePresentationEquivalenceModCompEvaluationIso_hom_app_apply]
            have hn := ConcreteCategory.congr_hom
              (((finitePresentationEquivalenceModCompιIso R).hom.app M).naturality
                (finiteProjectiveModulesRegularMulRight R r).op) x
            rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
            dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hn
            let ψ : (finiteProjectiveModulesRegular R).obj ⟶ M.obj :=
              ((finitePresentationEquivalenceModCompιIso R).hom.app M).app
                (op (finiteProjectiveModulesRegular R)) x
            have hy : ((finiteProjectiveModules R).restrictedPreadditiveYoneda.obj M.obj).map
                (finiteProjectiveModulesRegularMulRight R r).op ψ =
                (finiteProjectiveModulesRegularMulRight R r).hom ≫ ψ :=
              ObjectProperty.restrictedPreadditiveYoneda_obj_map_apply _ _ _ _
            have hmul : ((finiteProjectiveModulesRegularMulRight R r).hom ≫ ψ).hom (1 : R) =
                r • ψ.hom (1 : R) := by
              have hcomp : ((finiteProjectiveModulesRegularMulRight R r).hom ≫ ψ).hom =
                  ψ.hom ∘ₗ (finiteProjectiveModulesRegularMulRight R r).hom.hom :=
                ModuleCat.hom_comp _ _
              have h1 := LinearMap.congr_fun hcomp (1 : R)
              have h2 : (finiteProjectiveModulesRegularMulRight R r).hom.hom (1 : R) =
                  r • (1 : R) := by
                rw [finiteProjectiveModulesRegularMulRight_hom_apply, one_mul, smul_eq_mul,
                  mul_one]
              exact h1.trans <| (congrArg ψ.hom h2).trans (map_smul ψ.hom r (1 : R))
            exact (congrArg (fun k ↦ k.hom (1 : R)) (hn.trans hy)).trans hmul }
      (LinearEquiv.ofBijective f
        (ConcreteCategory.bijective_of_isIso
          ((finitePresentationEquivalenceModCompEvaluationIso R).hom.app M))).toModuleIso)
    fun {M N} f ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
      have hn := ConcreteCategory.congr_hom
        ((finitePresentationEquivalenceModCompEvaluationIso R).hom.naturality f) x
      exact hn

/-- Evaluation at the regular module `R`, equipped with the `R`-action induced by right
multiplication on `R`, as a functor from `mod (proj R)` to finitely presented `R`-modules. -/
noncomputable def finitePresentationEvaluationFunctor :
    (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory ⥤
      (finitePresentationModules R).FullSubcategory :=
  ObjectProperty.lift (finitePresentationModules R) (finitePresentationEvalModule R) fun F ↦ by
    let E := finitePresentationEquivalenceMod R
    let e : (finitePresentationEvalModule R).obj F ≅ (E.inverse.obj F).obj :=
      (finitePresentationEvalModule R).mapIso (E.counitIso.app F).symm ≪≫
        (finitePresentationEquivalenceModCompEvalModuleIso R).app (E.inverse.obj F)
    exact (finitePresentationModules R).prop_of_iso e.symm (E.inverse.obj F).property

/-- The underlying abelian group of `(TauCeti.finitePresentationEvaluationFunctor R).obj F` is
`F` evaluated at the regular module `R`. -/
noncomputable def finitePresentationEvaluationFunctorCompForgetIso :
    (finitePresentationEvaluationFunctor R ⋙ (finitePresentationModules R).ι) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      (isFinitelyPresentedFunctor _).ι ⋙
        (evaluation _ _).obj (op (finiteProjectiveModulesRegular R)) :=
  NatIso.ofComponents
    (fun _ ↦ AddEquiv.toAddCommGrpIso (AddEquiv.refl _))
    fun _ ↦ AddCommGrpCat.ext fun _ ↦ rfl

private theorem finitePresentationEvaluationFunctorCompForgetIso_hom_app_apply
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory)
    (x : ((finitePresentationEvaluationFunctor R).obj F).obj) :
    (finitePresentationEvaluationFunctorCompForgetIso R).hom.app F x = x :=
  rfl

private theorem finitePresentationEvaluationFunctor_obj_smul
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory)
    (r : R) (x : ((finitePresentationEvaluationFunctor R).obj F).obj) :
    r • x = (F.obj.map (finiteProjectiveModulesRegularMulRight R r).op).hom x :=
  finitePresentationEvalSMul_def R F r x

/-- Under `TauCeti.finitePresentationEvaluationFunctorCompForgetIso`, scalar multiplication by
`r : R` corresponds to the action of right multiplication by `r` on the regular module `R`. -/
@[simp]
theorem finitePresentationEvaluationFunctorCompForgetIso_hom_app_smul
    (F : (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory)
    (r : R) (x : ((finitePresentationEvaluationFunctor R).obj F).obj) :
    dsimp% (finitePresentationEvaluationFunctorCompForgetIso R).hom.app F (r • x) =
      (F.obj.map (ObjectProperty.homMk
        (ModuleCat.ofHom (LinearMap.mulRight R r)) :
          finiteProjectiveModulesRegular R ⟶ finiteProjectiveModulesRegular R).op).hom
        ((finitePresentationEvaluationFunctorCompForgetIso R).hom.app F x) := by
  rw [finitePresentationEvaluationFunctorCompForgetIso_hom_app_apply,
    finitePresentationEvaluationFunctorCompForgetIso_hom_app_apply,
    finitePresentationEvaluationFunctor_obj_smul, finiteProjectiveModulesRegularMulRight]

/-- Evaluation at the regular module `R`, equipped with its induced `R`-action, is naturally
isomorphic to `(TauCeti.finitePresentationEquivalenceMod R).inverse`. -/
noncomputable def finitePresentationEvaluationFunctorIso :
    finitePresentationEvaluationFunctor R ≅ (finitePresentationEquivalenceMod R).inverse :=
  let hcomp :
      (finitePresentationEquivalenceMod R).functor ⋙
          finitePresentationEvaluationFunctor R ≅
        𝟭 (finitePresentationModules R).FullSubcategory :=
    NatIso.ofComponents
      (fun M ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
        ((finitePresentationEquivalenceModCompEvalModuleIso R).app M))
      fun {M N} f ↦ (ObjectProperty.fullyFaithfulι _).map_injective <| by
        simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Functor.comp_map,
          ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, Functor.id_map]
        exact (finitePresentationEquivalenceModCompEvalModuleIso R).hom.naturality f
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (finitePresentationEquivalenceMod R).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ hcomp ≪≫
    Functor.rightUnitor _

end TauCeti
