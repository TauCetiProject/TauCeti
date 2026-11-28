/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RingedSpace.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic

/-!
# Comparison of holomorphic and complex-smooth locally ringed spaces

On a `C¹` complex manifold `(X, I)` modelled on a boundaryless finite-dimensional complex normed
space, `TauCeti.holomorphicStructureSheaf.smoothLocallyRingedSpaceIso` canonically identifies the
holomorphic locally ringed space `locallyRingedSpace I X` with Mathlib's complex-smooth locally
ringed space `ChartedSpace.locallyRingedSpace I X` over `ℂ`.

We record the action of `smoothLocallyRingedSpaceIso` on sections, stalks, and pointwise function
values, and prove that it intertwines `locallyRingedSpaceMap` with Mathlib's
`ChartedSpace.locallyRingedSpaceMap` (`locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom`).

## Main definitions

* `TauCeti.holomorphicStructureSheaf.smoothLocallyRingedSpaceIso`: canonical isomorphism over
  `𝟙 (TopCat.of X)` between `locallyRingedSpace I X` and `ChartedSpace.locallyRingedSpace I X`.

## Main results

* `smoothLocallyRingedSpaceIso_hom_c_app`, `smoothLocallyRingedSpaceIso_inv_c_app`: section maps of
  `smoothLocallyRingedSpaceIso` in terms of `smoothSectionsEquiv`.
* `smoothLocallyRingedSpaceIso_hom_stalkMap`, `smoothLocallyRingedSpaceIso_inv_stalkMap`: stalk
  maps of `smoothLocallyRingedSpaceIso` in terms of `smoothStalkIso`.
* `locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom`: naturality with respect to
  `locallyRingedSpaceMap`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory IsManifold Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section SmoothComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

-- Exposed so `.hom.base` and `.inv.base` reduce definitionally in the dependent types of the
-- `.c.app` and `.stalkMap` comparison lemmas below (`smoothSheafIso` remains unexposed).
/-- On a `C¹` finite-dimensional boundaryless complex manifold, the holomorphic locally ringed space
is canonically isomorphic over the identity on `X` to Mathlib's complex-smooth locally ringed space
`ChartedSpace.locallyRingedSpace I X`. -/
@[expose]
def smoothLocallyRingedSpaceIso :
    locallyRingedSpace I X ≅ ChartedSpace.locallyRingedSpace I X :=
  LocallyRingedSpace.isoOfSheafIso _ _ (smoothSheafIso I X)

/-- The forward direction of `smoothLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_base :
    (smoothLocallyRingedSpaceIso I X).hom.base = 𝟙 (TopCat.of X) :=
  LocallyRingedSpace.isoOfSheafIso_hom_base _ _ _

/-- The inverse direction of `smoothLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_base :
    (smoothLocallyRingedSpaceIso I X).inv.base = 𝟙 (TopCat.of X) :=
  LocallyRingedSpace.isoOfSheafIso_inv_base _ _ _

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` is the inverse section equivalence
`(smoothSectionsEquiv I X U).symm`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).hom.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).symm.toRingHom :=
  (LocallyRingedSpace.isoOfSheafIso_hom_c_app _ _ (smoothSheafIso I X) U).trans
    (smoothSheafIso_inv_app U)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` is the section equivalence
`smoothSectionsEquiv I X U`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).inv.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).toRingHom :=
  (LocallyRingedSpace.isoOfSheafIso_inv_c_app _ _ (smoothSheafIso I X) U).trans
    (smoothSheafIso_hom_app U)

private theorem smoothLocallyRingedSpaceIso_hom_c_app_hom_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :
    ((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s =
      (smoothSectionsEquiv I X U).symm s :=
  (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_hom_c_app I X U)).trans
    (CommRingCat.ofHom_apply _ s)

private theorem smoothLocallyRingedSpaceIso_inv_c_app_hom_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) :
    ((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s =
      smoothSectionsEquiv I X U s :=
  (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_inv_c_app I X U)).trans
    (CommRingCat.ofHom_apply _ s)

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).hom` agrees with
`(smoothStalkIso I X x).inv`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).hom.stalkMap x = (smoothStalkIso I X x).inv := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨U, hx, g, rfl⟩ := (ChartedSpace.locallyRingedSpace I X).presheaf.exists_germ_eq s
  rw [LocallyRingedSpace.stalkMap_germ_apply, smoothLocallyRingedSpaceIso_hom_c_app_hom_apply]
  exact (smoothStalkIso_inv_germ x U hx g).symm

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).inv` agrees with
`(smoothStalkIso I X x).hom`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).inv.stalkMap x = (smoothStalkIso I X x).hom := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨U, hx, g, rfl⟩ := (locallyRingedSpace I X).presheaf.exists_germ_eq s
  rw [LocallyRingedSpace.stalkMap_germ_apply, smoothLocallyRingedSpaceIso_inv_c_app_hom_apply]
  exact (smoothStalkIso_hom_germ x U hx g).symm

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_hom_c_app_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : U) :
    toFun I X (op U) (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s) x =
      (s : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯) x := by
  rw [smoothLocallyRingedSpaceIso_hom_c_app_hom_apply]
  exact smoothSectionsEquiv_symm_apply U s x

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_inv_c_app_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : U) :
    DFunLike.coe (F := C^∞⟮I, U; 𝓘(ℂ), ℂ⟯)
        (((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s) x =
      toFun I X (op U) s x := by
  rw [smoothLocallyRingedSpaceIso_inv_c_app_hom_apply]
  exact smoothSectionsEquiv_apply U s x

variable {I X} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- `smoothLocallyRingedSpaceIso` intertwines `locallyRingedSpaceMap` with Mathlib's
`ChartedSpace.locallyRingedSpaceMap`. -/
@[reassoc]
theorem locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom
    (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpaceMap f hf ≫ (smoothLocallyRingedSpaceIso J Y).hom =
      (smoothLocallyRingedSpaceIso I X).hom ≫
        ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp)) := by
  have hbase :
      (locallyRingedSpaceMap f hf ≫ (smoothLocallyRingedSpaceIso J Y).hom).base =
        ((smoothLocallyRingedSpaceIso I X).hom ≫
          ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).base := by
    rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base, locallyRingedSpaceMap_base,
      smoothLocallyRingedSpaceIso_hom_base, smoothLocallyRingedSpaceIso_hom_base,
      ChartedSpace.locallyRingedSpaceMap_base, Category.comp_id, Category.id_comp]
  refine locallyRingedSpace_hom_ext hbase fun U s x ↦ ?_
  rw [LocallyRingedSpace.comp_c_app_apply, LocallyRingedSpace.comp_c_app_apply]
  have hL1 := locallyRingedSpaceMap_c_app_apply f hf U
    (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op U)).hom s) ⟨x.val, x.property⟩
  have hL2 := smoothLocallyRingedSpaceIso_hom_c_app_apply J Y U s ⟨f x.val, x.property⟩
  have hR1 := smoothLocallyRingedSpaceIso_hom_c_app_apply I X
    ((Opens.map (ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).base).obj U)
    (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) x
  have hR2 := ChartedSpace.locallyRingedSpaceMap_c_app_apply f (hf.of_le (by simp)) s x.property
  exact hL1.trans (hL2.trans (hR1.trans hR2).symm)

end SmoothComparison

end TauCeti.holomorphicStructureSheaf
