/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.InternalHom.Basic
public import TauCeti.Condensed.Light.LocallyConstant

import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive
import TauCeti.Topology.Category.LightProfinite.Cartesian
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

/-- Sections of internal Hom from a free test object, as functions on a product. -/
noncomputable def lightCondFreeInternalHomProductEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃+
        LocallyConstant (S × T) M := by
  let F := lightProfiniteToLightCondSet ⋙ LightCondensed.free R
  exact (tensorHomSectionsAddEquiv R (F.obj S)
    ((LightCondMod.LocallyConstant.functor R).obj M) T).symm.trans
    (((Linear.homCongr ℤ (Functor.Monoidal.μIso F S T) (Iso.refl _)).toAddEquiv).trans
      ((S ⊗ T).freeModuleHomEquiv.trans
        (ModuleCat.lightLocallyConstantSectionsEquiv M (S ⊗ T)).toAddEquiv))

/-- Uncurry the section map, precompose with the inverse free monoidal comparison, and
then evaluate the resulting free-module map as a section on `S × T`. -/
lemma lightCondFreeInternalHomProductEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    lightCondFreeInternalHomProductEquiv M S T s =
      ModuleCat.lightLocallyConstantSectionsEquiv M (S ⊗ T)
        ((S ⊗ T).freeModuleHomEquiv
          ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R) S T).inv ≫
            MonoidalClosed.uncurry (T.freeModuleHomEquiv.symm s))) := by
  unfold lightCondFreeInternalHomProductEquiv
  calc
    _ = ModuleCat.lightLocallyConstantSectionsEquiv M (S ⊗ T) ((S ⊗ T).freeModuleHomEquiv
        (Linear.homCongr ℤ
          (Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R) S T)
          (Iso.refl _) ((tensorHomSectionsAddEquiv R _ _ T).symm s))) :=
      (AddEquiv.trans_apply _ _ _).trans (AddEquiv.trans_apply _ _ _)
    _ = _ := by
      rw [Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
        tensorHomSectionsAddEquiv_symm_apply]

/-- Restriction of product sections is precomposition by `id × f`. -/
lemma lightCondFreeInternalHomProductEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) :
    lightCondFreeInternalHomProductEquiv M S T
      (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) =
      (lightCondFreeInternalHomProductEquiv M S U s).comap (S ◁ f).hom.hom := by
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
  rw [lightCondFreeInternalHomProductEquiv_apply, lightCondFreeInternalHomProductEquiv_apply, hn,
    Functor.comp_map, LightProfinite.freeModuleHomEquiv_comp]
  ext ⟨x, y⟩
  exact (lightLocallyConstantSectionsEquiv_map_apply M (S ◁ f) _ (x, y)).trans
    (LocallyConstant.coe_comap_apply _ _ _).symm

/-- The product comparison commutes with scalar multiplication in the coefficient module. -/
lemma lightCondFreeInternalHomProductEquiv_smul (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) (r : R)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    lightCondFreeInternalHomProductEquiv M S T (r • s) =
      r • lightCondFreeInternalHomProductEquiv M S T s := by
  have hs : T.freeModuleHomEquiv.symm (r • s) = r • T.freeModuleHomEquiv.symm s := by
    simpa only [LightProfinite.freeModuleHomLinearEquiv_symm_apply] using
      (T.freeModuleHomLinearEquiv (M := _)).symm.map_smul r s
  rw [lightCondFreeInternalHomProductEquiv_apply, lightCondFreeInternalHomProductEquiv_apply, hs,
    TauCeti.uncurry_smul, Linear.comp_smul, LightProfinite.freeModuleHomEquiv_smul]
  exact (lightLocallyConstantSectionsEquiv M (S ⊗ T)).map_smul r _

/-- For free source `R[S]` and discrete target `M`, internal Hom sections on `T` are
locally constant maps from `T` into the discrete module `LocallyConstant S M`. -/
noncomputable def lightCondFreeInternalHomSectionsEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃ₗ[R]
        LocallyConstant T (LocallyConstant S M) where
  toAddEquiv := (lightCondFreeInternalHomProductEquiv M S T).trans
    (((LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)).toAddEquiv)
  map_smul' r s := by
    let e : LocallyConstant (S × T) M ≃ₗ[R] LocallyConstant T (LocallyConstant S M) :=
      (LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)
    exact (congrArg e (lightCondFreeInternalHomProductEquiv_smul M S T r s)).trans
      (e.map_smul r (lightCondFreeInternalHomProductEquiv M S T s))

/-- Curried evaluation agrees with evaluation on the product. -/
@[simp]
lemma lightCondFreeInternalHomSectionsEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) (y : T) (x : S) :
    lightCondFreeInternalHomSectionsEquiv M S T s y x =
      lightCondFreeInternalHomProductEquiv M S T s (x, y) := by
  simp [lightCondFreeInternalHomSectionsEquiv]

/-- Restriction acts by precomposition on the parameter of the curried section. -/
lemma lightCondFreeInternalHomSectionsEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) :
    lightCondFreeInternalHomSectionsEquiv M S T
      (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) =
      (lightCondFreeInternalHomSectionsEquiv M S U s).comap f.hom.hom := by
  ext y x
  simp only [lightCondFreeInternalHomSectionsEquiv_apply, LocallyConstant.coe_comap_apply]
  have h := congrArg (fun g : LocallyConstant (S × T) M ↦ g (x, y))
    (lightCondFreeInternalHomProductEquiv_naturality M S f s)
  -- Comap is on the concrete product, while whiskering is on the monoidal product.
  erw [LocallyConstant.coe_comap_apply] at h
  exact h.trans (congrArg (lightCondFreeInternalHomProductEquiv M S U s)
    (S.whiskerLeft_apply f x y))

private noncomputable def lightCondFreeInternalHomDiscreteIsoApp (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≅
      (((LightCondMod.LocallyConstant.functor R).obj
        (ModuleCat.of R (LocallyConstant S M))).obj.obj (op T)) :=
  ((lightCondFreeInternalHomSectionsEquiv M S T).trans
    (lightLocallyConstantSectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T).symm).toModuleIso

private lemma lightCondFreeInternalHomDiscreteIsoApp_hom_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    lightLocallyConstantSectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T
      ((lightCondFreeInternalHomDiscreteIsoApp M S T).hom s) =
        lightCondFreeInternalHomSectionsEquiv M S T s := by
  exact LinearEquiv.apply_symm_apply
    (lightLocallyConstantSectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T) _

/-- Internal Hom from a free test object to a discrete module is the discrete realization
of the module of locally constant functions on the test object. -/
noncomputable def lightCondFreeInternalHomDiscreteIso (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M) ≅
        (LightCondMod.LocallyConstant.functor R).obj (ModuleCat.of R (LocallyConstant S M)) :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun T ↦ lightCondFreeInternalHomDiscreteIsoApp M S T.unop) (fun {T U} f ↦ by
      ext s
      apply (lightLocallyConstantSectionsEquiv (ModuleCat.of R (LocallyConstant S M))
        U.unop).injective
      -- The component isomorphisms act on the underlying modules of sheaf sections.
      erw [ModuleCat.comp_apply, ModuleCat.comp_apply,
        lightCondFreeInternalHomDiscreteIsoApp_hom_apply]
      ext y x
      -- The locally constant realization restricts along the unop of the presheaf map.
      erw [lightLocallyConstantSectionsEquiv_map_apply _ f.unop,
        lightCondFreeInternalHomDiscreteIsoApp_hom_apply]
      have h := congrArg (fun z : LocallyConstant U.unop (LocallyConstant S M) ↦ z y x)
        (lightCondFreeInternalHomSectionsEquiv_naturality M S f.unop s)
      simp only [LocallyConstant.coe_comap_apply, Quiver.Hom.op_unop] at h
      -- The comap uses the continuous map underlying the light profinite morphism.
      exact h)

/-- On sections, the discrete internal Hom isomorphism is the linear section comparison. -/
lemma lightCondFreeInternalHomDiscreteIso_hom_app_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    lightLocallyConstantSectionsEquiv (ModuleCat.of R (LocallyConstant S M)) T
      ((lightCondFreeInternalHomDiscreteIso M S).hom.hom.app (op T) s) =
        lightCondFreeInternalHomSectionsEquiv M S T s := by
  exact lightCondFreeInternalHomDiscreteIsoApp_hom_apply M S T s

end ModuleCat
