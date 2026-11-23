/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.InternalHom.Basic
public import TauCeti.Condensed.Light.LocallyConstant

import TauCeti.Topology.LocallyConstant.Product

/-!
# Internal Hom with discrete coefficients

For light profinite spaces `S` and `T`, sections on `T` of internal Hom from the free
source `R[S]` to a discrete target module `M` are locally constant maps from `T` into
the discrete module `LocallyConstant S M`. The product comparison first identifies these
sections with locally constant functions on `S × T`; compactness supplies the exponential law.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory LightCondensed Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

private lemma tensorLeftLinear (A : LightCondMod R) : (tensorLeft A).Linear R := by
  let J := coherentTopology LightProfinite.{u}
  let I := sheafToPresheaf J (ModuleCat.{u} R)
  let Q := presheafToSheaf J (ModuleCat.{u} R)
  let adj : Q ⊣ I := sheafificationAdjunction J (ModuleCat.{u} R)
  have : I.Linear R := inferInstanceAs ((sheafToPresheaf _ _).Linear R)
  have : Q.Linear R := by
    constructor
    intro X Y f r
    apply (adj.homEquiv X (Q.obj Y)).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_smul]
    have h (g : X ⟶ Y) : g ≫ adj.unit.app Y = adj.unit.app X ≫ I.map (Q.map g) :=
      adj.unit.naturality g
    rw [← h, Linear.comp_smul, ← h, Linear.smul_comp]
  have : (tensorLeft (I.obj A)).Linear R := by
    constructor
    intro X Y f r
    apply NatTrans.ext
    funext T
    change ((I.obj A) ◁ (r • f)).app T = (r • ((I.obj A) ◁ f)).app T
    simp only [Monoidal.whiskerLeft_app, NatTrans.app_smul, MonoidalLinear.whiskerLeft_smul]
    rfl
  have e : (I ⋙ tensorLeft (I.obj A)) ⋙ Q ≅ tensorLeft A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft I (Functor.Monoidal.commTensorLeft Q (I.obj A)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit) _ ≪≫
      Functor.leftUnitor _ ≪≫
      (tensoringLeft _).mapIso (asIso (adj.counit.app A))
  exact Functor.linear_of_iso _ e

private lemma uncurry_smul {A B C : LightCondMod R} (r : R) (f : B ⟶ A ⟶[LightCondMod R] C) :
    MonoidalClosed.uncurry (r • f) = r • MonoidalClosed.uncurry f := by
  let := tensorLeftLinear A
  have h : A ◁ (r • f) = r • (A ◁ f) := (tensorLeft A).map_smul r f
  rw [MonoidalClosed.uncurry_eq, h, Linear.smul_comp, MonoidalClosed.uncurry_eq]

/-- Sections of internal Hom from a free test object, as functions on a product. -/
noncomputable def internalHomProductEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃+
        LocallyConstant (S × T) M := by
  let F := lightProfiniteToLightCondSet ⋙ LightCondensed.free R
  exact (tensorHomSectionsAddEquiv R (F.obj S)
    ((LightCondMod.LocallyConstant.functor R).obj M) T).symm.trans
    (((Linear.homCongr ℤ (Functor.Monoidal.μIso F S T) (Iso.refl _)).toAddEquiv).trans
      ((S ⊗ T).freeModuleHomEquiv.trans
        (ModuleCat.sectionsEquiv M (S ⊗ T)).toAddEquiv))

/-- Uncurry the section map, precompose with the inverse free monoidal comparison, and
then evaluate the resulting free-module map as a section on `S × T`. -/
lemma internalHomProductEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    internalHomProductEquiv M S T s =
      ModuleCat.sectionsEquiv M (S ⊗ T)
        ((S ⊗ T).freeModuleHomEquiv
          ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R) S T).inv ≫
            MonoidalClosed.uncurry (T.freeModuleHomEquiv.symm s))) := by
  unfold internalHomProductEquiv
  calc
    _ = ModuleCat.sectionsEquiv M (S ⊗ T) ((S ⊗ T).freeModuleHomEquiv
        (Linear.homCongr ℤ
          (Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R) S T)
          (Iso.refl _) ((tensorHomSectionsAddEquiv R _ _ T).symm s))) :=
      (AddEquiv.trans_apply _ _ _).trans (AddEquiv.trans_apply _ _ _)
    _ = _ := by
      rw [Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
        tensorHomSectionsAddEquiv_symm_apply]

private lemma whiskerLeft_apply (S : LightProfinite.{u}) {T U : LightProfinite.{u}}
    (f : T ⟶ U) (x : S) (y : T) :
    (S ◁ f).hom.hom (x, y) = (x, f y) := by
  rfl

/-- Restriction of product sections is precomposition by `id × f`. -/
lemma internalHomProductEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) :
    internalHomProductEquiv M S T
      (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) =
      (internalHomProductEquiv M S U s).comap (S ◁ f).hom.hom := by
  let F := lightProfiniteToLightCondSet ⋙ LightCondensed.free R
  let N := ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
    (LightCondMod.LocallyConstant.functor R).obj M)
  have h : T.freeModuleHomEquiv.symm (N.obj.map f.op s) =
      F.map f ≫ U.freeModuleHomEquiv.symm s := by
    apply T.freeModuleHomEquiv.injective
    rw [Functor.comp_map,
      LightProfinite.freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  have hδ := Functor.OplaxMonoidal.δ_natural_right F S f
  have hn : (Functor.Monoidal.μIso F S T).inv ≫ MonoidalClosed.uncurry
      (T.freeModuleHomEquiv.symm (N.obj.map f.op s)) =
      F.map (S ◁ f) ≫ (Functor.Monoidal.μIso F S U).inv ≫
        MonoidalClosed.uncurry (U.freeModuleHomEquiv.symm s) := by
    rw [h, MonoidalClosed.uncurry_natural_left]
    simpa only [Functor.Monoidal.μIso_inv, Category.assoc] using
      congrArg (fun k ↦ k ≫ MonoidalClosed.uncurry (U.freeModuleHomEquiv.symm s)) hδ
  have hs := congrArg ((S ⊗ T).freeModuleHomEquiv (M :=
    (LightCondMod.LocallyConstant.functor R).obj M)) hn
  rw [Functor.comp_map,
    LightProfinite.freeModuleHomEquiv_comp] at hs
  ext ⟨x, y⟩
  have he := congrArg (fun z ↦
    ModuleCat.sectionsEquiv M (S ⊗ T) z (x, y)) hs
  have he' := he.trans (ModuleCat.sectionsEquiv_map_apply M
    (S ◁ f) _ (x, y))
  rw [internalHomProductEquiv_apply, internalHomProductEquiv_apply]
  erw [whiskerLeft_apply] at he'
  erw [LocallyConstant.coe_comap_apply]
  exact he'

private lemma internalHomProductEquiv_smul (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) (r : R)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    internalHomProductEquiv M S T (r • s) = r • internalHomProductEquiv M S T s := by
  have hs : T.freeModuleHomEquiv.symm (r • s) = r • T.freeModuleHomEquiv.symm s := by
    simpa only [LightProfinite.freeModuleHomLinearEquiv_symm_apply] using
      (T.freeModuleHomLinearEquiv (M := _)).symm.map_smul r s
  rw [internalHomProductEquiv_apply, internalHomProductEquiv_apply, hs, uncurry_smul,
    Linear.comp_smul, LightProfinite.freeModuleHomEquiv_smul, map_smul]
  rfl

/-- For free source `R[S]` and discrete target `M`, internal Hom sections on `T` are
locally constant maps from `T` into the discrete module `LocallyConstant S M`. -/
noncomputable def internalHomSectionsEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃ₗ[R]
        LocallyConstant T (LocallyConstant S M) where
  toAddEquiv := (internalHomProductEquiv M S T).trans
    (((LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)).toAddEquiv)
  map_smul' r s := by
    let e : LocallyConstant (S × T) M ≃ₗ[R] LocallyConstant T (LocallyConstant S M) :=
      (LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)
    exact (congrArg e (internalHomProductEquiv_smul M S T r s)).trans
      (e.map_smul r (internalHomProductEquiv M S T s))

/-- Curried evaluation agrees with evaluation on the product. -/
@[simp]
lemma internalHomSectionsEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) (y : T) (x : S) :
    internalHomSectionsEquiv M S T s y x = internalHomProductEquiv M S T s (x, y) := by
  simp [internalHomSectionsEquiv]

/-- Restriction acts by precomposition on the parameter of the curried section. -/
lemma internalHomSectionsEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) :
    internalHomSectionsEquiv M S T
      (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) =
      (internalHomSectionsEquiv M S U s).comap f.hom.hom := by
  ext y x
  simp only [internalHomSectionsEquiv_apply, LocallyConstant.coe_comap_apply]
  have h := congrArg (fun g : LocallyConstant (S × T) M ↦ g (x, y))
    (internalHomProductEquiv_naturality M S f s)
  erw [LocallyConstant.coe_comap_apply] at h
  erw [whiskerLeft_apply] at h
  exact h

private noncomputable def internalHomDiscreteIsoApp (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≅
      (((LightCondMod.LocallyConstant.functor R).obj
        (ModuleCat.of R (LocallyConstant S M))).obj.obj (op T)) :=
  ((internalHomSectionsEquiv M S T).trans
    (sectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T).symm).toModuleIso

private lemma internalHomDiscreteIsoApp_hom_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    sectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T
      ((internalHomDiscreteIsoApp M S T).hom s) = internalHomSectionsEquiv M S T s := by
  exact (sectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T).apply_symm_apply
    (internalHomSectionsEquiv M S T s)

/-- Internal Hom from a free test object to a discrete module is the discrete realization
of the module of locally constant functions on the test object. -/
noncomputable def internalHomDiscreteIso (M : ModuleCat.{u} R) (S : LightProfinite.{u}) :
    ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M) ≅
        (LightCondMod.LocallyConstant.functor R).obj (ModuleCat.of R (LocallyConstant S M)) :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents (fun T ↦ internalHomDiscreteIsoApp M S T.unop)
    (fun {T U} f ↦ by
      ext s
      apply (sectionsEquiv (ModuleCat.of R (LocallyConstant S M)) U.unop).injective
      erw [ModuleCat.comp_apply, ModuleCat.comp_apply, internalHomDiscreteIsoApp_hom_apply]
      ext y x
      erw [sectionsEquiv_map_apply (ModuleCat.of R (LocallyConstant S M)) f.unop,
        internalHomDiscreteIsoApp_hom_apply]
      have h := congrArg (fun z : LocallyConstant U.unop (LocallyConstant S M) ↦ z y x)
        (internalHomSectionsEquiv_naturality M S f.unop s)
      erw [LocallyConstant.coe_comap_apply] at h
      simp only [Quiver.Hom.op_unop] at h
      exact h)

/-- On sections, the discrete internal Hom isomorphism is the linear section comparison. -/
lemma internalHomDiscreteIso_hom_app_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    sectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T
      ((internalHomDiscreteIso M S).hom.hom.app (op T) s) =
        internalHomSectionsEquiv M S T s := by
  exact internalHomDiscreteIsoApp_hom_apply M S T s

end ModuleCat
