/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.HomFromProjective.Functor
public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.Grothendieck
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.Algebra.Category.ModuleCat.Generator
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# The regular module generates the unbounded derived category

The regular module placed in degree zero has a coproduct-preserving additive Hom functor,
and its integer shifts detect zero objects of the unbounded derived category. More generally,
additive Hom from the regular module placed in degree `n` is the underlying abelian group
of `n`-th cohomology, naturally in the target complex.

The lifted comparison works with any chosen derived hom universe. When that universe agrees
with the module universe, it gives an unlifted comparison; the small-Hom derived category
supplied by `CategoryTheory.IsGrothendieckAbelian.hasDerivedCategory` is one such choice.
No commutativity, finiteness or boundedness is required.
The shift convention is cohomological: shifting `R[0]` by `-n` places it in degree `n`.

This is the module case of compact generation in Stacks, Theorem 36.15.3 (Tag 09IS).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Functor ZeroObject DerivedCategory

universe w u

namespace TauCeti

variable (R : Type u) [Ring R]

section Lifted

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Additive Hom from the regular stalk is cohomology, after lifting both abelian groups
into a common universe, for any chosen derived localization. -/
def derivedModuleCatPreadditiveCoyonedaRingLiftIso (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R))) ⋙
        AddCommGrpCat.uliftFunctor.{u, w} ≅
      (homologyFunctor (ModuleCat.{u} R) n ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ⋙
        AddCommGrpCat.uliftFunctor.{w, u} :=
  preadditiveCoyonedaSingleLiftIso (ModuleCat.of R R) n ≪≫
    isoWhiskerRight (isoWhiskerLeft _ (moduleCatPreadditiveCoyonedaRingIso R))
      AddCommGrpCat.uliftFunctor.{w, u}

/-- The lifted regular-stalk comparison evaluates the cohomology map at `1`. -/
@[simp]
lemma derivedModuleCatPreadditiveCoyonedaRingLiftIso_hom_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R))
    (f : ULift.{u} ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E)) :
    DFunLike.coe (F := ULift.{u} ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      ULift.{w} ((homologyFunctor (ModuleCat R) n).obj E))
      ((derivedModuleCatPreadditiveCoyonedaRingLiftIso R n).hom.app E).hom f =
      ULift.up ((((singleFunctorCompHomologyFunctorIso (ModuleCat R) n).inv.app
        (ModuleCat.of R R)) ≫ (homologyFunctor (ModuleCat R) n).map f.down).hom (1 : R)) := by
  simp only [derivedModuleCatPreadditiveCoyonedaRingLiftIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    AddCommGrpCat.uliftFunctor_map]
  -- Specify the bundled Hom types so the two component rules can rewrite without unfolding.
  change ULift.up (DFunLike.coe (F := (ModuleCat.of R R ⟶
      (homologyFunctor (ModuleCat R) n).obj E) →+ (homologyFunctor (ModuleCat R) n).obj E)
    ((moduleCatPreadditiveCoyonedaRingIso R).hom.app _).hom
      (DFunLike.coe (F := ULift.{u}
        ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
        ULift.{w} (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E))
        ((preadditiveCoyonedaSingleLiftIso (ModuleCat.of R R) n).hom.app E).hom f).down) = _
  rw [preadditiveCoyonedaSingleLiftIso_hom_app_apply,
    ModuleCat.moduleCatPreadditiveCoyonedaRingIso_hom_app_apply]

/-- The inverse lifted regular-stalk comparison constructs a map from a cohomology class. -/
@[simp]
lemma derivedModuleCatPreadditiveCoyonedaRingLiftIso_inv_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R))
    (m : ULift.{w} ((homologyFunctor (ModuleCat R) n).obj E)) :
    DFunLike.coe (F := ULift.{w} ((homologyFunctor (ModuleCat R) n).obj E) →+
      ULift.{u} ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E))
      ((derivedModuleCatPreadditiveCoyonedaRingLiftIso R n).inv.app E).hom m =
      ULift.up ((homFromProjectiveSingleAddEquiv (ModuleCat.of R R) E n).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ m.down))) := by
  simp only [derivedModuleCatPreadditiveCoyonedaRingLiftIso, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, whiskerRight_app, isoWhiskerLeft_inv, whiskerLeft_app,
    AddCommGrpCat.uliftFunctor_map]
  -- Give the inverse components their explicit Hom types for rewriting under implicit transparency.
  change DFunLike.coe (F := ULift.{w}
    (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E) →+
    ULift.{u} ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E))
    ((preadditiveCoyonedaSingleLiftIso (ModuleCat.of R R) n).inv.app E).hom
      (ULift.up (DFunLike.coe (F := (homologyFunctor (ModuleCat R) n).obj E →+
        (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E))
        ((moduleCatPreadditiveCoyonedaRingIso R).inv.app _).hom m.down)) = _
  rw [preadditiveCoyonedaSingleLiftIso_inv_app_apply,
    ModuleCat.moduleCatPreadditiveCoyonedaRingIso_inv_app_apply]

/-- Every small coproduct is preserved by additive Hom from the regular module placed in
any one degree, for any chosen derived localization. -/
instance preservesColimitsOfShape_preadditiveCoyoneda_ring (n : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj
        (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)))) := by
  have := preservesColimitsOfShape_of_natIso (J := Discrete J)
    (derivedModuleCatPreadditiveCoyonedaRingLiftIso R n).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ AddCommGrpCat.uliftFunctor.{u, w}

end Lifted

variable [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Additive Hom from the regular module in degree `n` is the underlying abelian group of
`n`-th cohomology. -/
def derivedModuleCatPreadditiveCoyonedaRingIso (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R))) ≅
      homologyFunctor (ModuleCat.{u} R) n ⋙ forget₂ (ModuleCat R) AddCommGrpCat :=
  preadditiveCoyonedaSingleIso (ModuleCat.of R R) n ≪≫
    isoWhiskerLeft _ (moduleCatPreadditiveCoyonedaRingIso R)

/-- The cohomology class corresponding to a derived morphism from the regular module is
obtained by evaluating its cohomology map at `1`. -/
@[simp]
lemma derivedModuleCatPreadditiveCoyonedaRingIso_hom_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R))
    (f : (singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) :
    DFunLike.coe (F := ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      (homologyFunctor (ModuleCat R) n).obj E)
      ((derivedModuleCatPreadditiveCoyonedaRingIso R n).hom.app E).hom f =
      (((singleFunctorCompHomologyFunctorIso (ModuleCat R) n).inv.app (ModuleCat.of R R)) ≫
        (homologyFunctor (ModuleCat R) n).map f).hom (1 : R) := by
  simp only [derivedModuleCatPreadditiveCoyonedaRingIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app]
  rw [AddCommGrpCat.hom_comp]
  -- The component's bundled object types need default transparency for pointwise composition.
  erw [AddMonoidHom.comp_apply]
  -- Fix the underlying Hom types explicitly: the bundled functor objects otherwise prevent
  -- rewriting the evaluation lemma at implicit transparency.
  let g : ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E :=
    DFunLike.coe (F := ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E))
      ((preadditiveCoyonedaSingleIso (ModuleCat.of R R) n).hom.app E).hom f
  change DFunLike.coe (F := (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E) →+
    (homologyFunctor (ModuleCat R) n).obj E)
    ((moduleCatPreadditiveCoyonedaRingIso R).hom.app _).hom g = _
  rw [ModuleCat.moduleCatPreadditiveCoyonedaRingIso_hom_app_apply]
  exact congrArg (fun g : ModuleCat.of R R ⟶ _ ↦ g.hom (1 : R))
    (preadditiveCoyonedaSingleIso_hom_app_apply (ModuleCat.of R R) n E f)

/-- The inverse regular-stalk comparison constructs a derived morphism from a cohomology class. -/
@[simp]
lemma derivedModuleCatPreadditiveCoyonedaRingIso_inv_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R)) (m : (homologyFunctor (ModuleCat R) n).obj E) :
    DFunLike.coe (F := (homologyFunctor (ModuleCat R) n).obj E →+
      ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E))
      ((derivedModuleCatPreadditiveCoyonedaRingIso R n).inv.app E).hom m =
      (homFromProjectiveSingleAddEquiv (ModuleCat.of R R) E n).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ m)) := by
  simp only [derivedModuleCatPreadditiveCoyonedaRingIso, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, whiskerLeft_app]
  rw [AddCommGrpCat.hom_comp]
  -- The component's bundled object types need default transparency for pointwise composition.
  erw [AddMonoidHom.comp_apply]
  -- Specify the component Hom types hidden by the bundled functor objects.
  change DFunLike.coe (F := (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E) →+
    ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E))
    ((preadditiveCoyonedaSingleIso (ModuleCat.of R R) n).inv.app E).hom
      (DFunLike.coe (F := (homologyFunctor (ModuleCat R) n).obj E →+
        (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E))
        ((moduleCatPreadditiveCoyonedaRingIso R).inv.app _).hom m) = _
  rw [preadditiveCoyonedaSingleIso_inv_app_apply,
    ModuleCat.moduleCatPreadditiveCoyonedaRingIso_inv_app_apply]

end TauCeti
