/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.InternalHom.Basic
public import TauCeti.Condensed.Light.LocallyConstant

import Mathlib.CategoryTheory.Linear.Basic
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
  change sectionsEquiv M (S ⊗ T) ((S ⊗ T).freeModuleHomEquiv
    (Linear.homCongr ℤ
      (Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R) S T)
      (Iso.refl _) ((tensorHomSectionsAddEquiv R _ _ T).symm s))) = _
  rw [Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    tensorHomSectionsAddEquiv_symm_apply]

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
  exact he'

/-- For free source `R[S]` and discrete target `M`, internal Hom sections on `T` are
locally constant maps from `T` into the discrete module `LocallyConstant S M`. -/
noncomputable def internalHomSectionsEquiv (M : ModuleCat.{u} R)
    (S T : LightProfinite.{u}) :
    (((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M).obj.obj (op T)) ≃+
        LocallyConstant T (LocallyConstant S M) :=
  (internalHomProductEquiv M S T).trans
    (((LocallyConstant.congrLeftₗ R (Homeomorph.prodComm S T)).trans
      (LocallyConstant.curryLinearEquiv R)).toAddEquiv)

/-- Curried evaluation agrees with evaluation on the product. -/
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
  have hf (z : T) : f.hom.hom z = f z := rfl
  rw [hf]
  exact congrArg (fun g : LocallyConstant (S × T) M ↦ g (x, y))
    (internalHomProductEquiv_naturality M S f s)

end ModuleCat
