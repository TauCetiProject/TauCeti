/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.InternalHom
public import TauCeti.Condensed.Light.LocallyConstant

import Mathlib.CategoryTheory.Linear.Basic
import TauCeti.Topology.LocallyConstant.Product

/-!
# Internal Hom with discrete coefficients

For a light profinite space S, internal Hom from its free module to a discrete module is
represented by locally constant functions on S. Compactness supplies the exponential law.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory LightCondensed Opposite

namespace LightCondMod.LocallyConstant

variable {R : Type u} [CommRing R]

/-- Sections of internal Hom from a free test object, as functions on a product. -/
noncomputable def internalHomProductEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃+
        LocallyConstant (S × T) M := by
  let F := lightProfiniteToLightCondSet ⋙ free R
  exact (tensorHomSectionsAddEquiv R (F.obj S)
    ((LightCondMod.LocallyConstant.functor R).obj M) T).symm.trans
    (((Linear.homCongr ℤ (Functor.Monoidal.μIso F S T) (Iso.refl _)).toAddEquiv).trans
      ((S ⊗ T).freeModuleHomEquiv.trans
        (LightCondMod.LocallyConstant.sectionsEquiv M (S ⊗ T)).toAddEquiv))

/-- Product evaluation is the tensor–Hom comparison followed by the free monoidal map. -/
lemma internalHomProductEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) :
    internalHomProductEquiv M S T s =
      LightCondMod.LocallyConstant.sectionsEquiv M (S ⊗ T)
        ((S ⊗ T).freeModuleHomEquiv
          ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ free R) S T).inv ≫
            MonoidalClosed.uncurry (T.freeModuleHomEquiv.symm s))) := by
  simp only [internalHomProductEquiv, AddEquiv.trans_apply,
     AddEquiv.coe_mk, Equiv.coe_fn_mk ]
  rw [tensorHomSectionsAddEquiv_symm_apply]
  rfl

private lemma internalHomProductEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) (x : S) (y : T) :
    internalHomProductEquiv M S T
      (((free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) (x, y) =
      internalHomProductEquiv M S U s (x, f y) := by
  let F := lightProfiniteToLightCondSet ⋙ free R
  let N := ((free R).obj S.toCondensed ⟶[LightCondMod R]
    (LightCondMod.LocallyConstant.functor R).obj M)
  have h : T.freeModuleHomEquiv.symm (N.obj.map f.op s) =
      F.map f ≫ U.freeModuleHomEquiv.symm s := by
    apply T.freeModuleHomEquiv.injective
    rw [show F.map f = (free R).map (lightProfiniteToLightCondSet.map f) from rfl,
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
  rw [show F.map (S ◁ f) = (free R).map
    (lightProfiniteToLightCondSet.map (S ◁ f)) from rfl,
    LightProfinite.freeModuleHomEquiv_comp] at hs
  have he := congrArg (fun z ↦
    LightCondMod.LocallyConstant.sectionsEquiv M (S ⊗ T) z (x, y)) hs
  have he' := he.trans (LightCondMod.LocallyConstant.sectionsEquiv_map_apply M
    (S ◁ f) _ (x, y))
  rw [internalHomProductEquiv_apply, internalHomProductEquiv_apply]
  exact he'

/-- Internal Hom from a compact test object has discrete locally constant coefficients. -/
noncomputable def internalHomSectionsEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃+
        LocallyConstant T (LocallyConstant S M) :=
  (internalHomProductEquiv M S T).trans
    (((LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)).toAddEquiv)

/-- Curried evaluation agrees with evaluation on the product. -/
lemma internalHomSectionsEquiv_apply (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u})
    (s : (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T))) (y : T) (x : S) :
    internalHomSectionsEquiv M S T s y x = internalHomProductEquiv M S T s (x, y) := by
  simp [internalHomSectionsEquiv]

/-- Restriction acts by precomposition on the parameter of the curried section. -/
lemma internalHomSectionsEquiv_naturality (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) {T U : LightProfinite.{u}} (f : T ⟶ U)
    (s : (((free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op U))) :
    internalHomSectionsEquiv M S T
      (((free R).obj S.toCondensed ⟶[LightCondMod R]
        (LightCondMod.LocallyConstant.functor R).obj M).obj.map f.op s) =
      (internalHomSectionsEquiv M S U s).comap f.hom.hom := by
  ext y x
  simp only [internalHomSectionsEquiv_apply, LocallyConstant.coe_comap_apply]
  convert internalHomProductEquiv_naturality M S f s x y using 1
  rfl

end LightCondMod.LocallyConstant
