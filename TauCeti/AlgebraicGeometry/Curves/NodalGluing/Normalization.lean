/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.RingedSpace
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RingedSpace
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# The normalization map of a glued nodal curve

Let `d` be flag-pair gluing data whose normalization components `X i` are charted spaces on a
common complex model. The normalization `Σ i, X i`, with its sheaf of holomorphic functions, maps
to the glued curve `NodalGluing.GluedCurve d`, with its sheaf of holomorphic functions agreeing at
the two points of each flag pair. On points this map is the quotient map, and on sections it
reads a matching function on the glued curve as a holomorphic function upstairs.

* `NodalGluing.normalizationSheafedSpaceHom`: the normalization map as a morphism of sheafed
  spaces. Its stalk map at a point of the normalization is restriction of germs to that branch
  (`NodalGluing.stalkMap_normalizationSheafedSpaceHom`).
* `NodalGluing.normalizationLocallyRingedSpaceHom`: the same map as a morphism of locally ringed
  spaces, for finitely many flag pairs on Hausdorff components; its stalk maps are local also at
  the flag points.

The main result is that, away from the finitely many flag points, the normalization map is an
open immersion of ringed spaces onto the complement of the nodes. It combines the homeomorphism
`NodalGluing.quotientMapOnComplNodeSetHomeomorph` of the two complements with the identification
`NodalGluing.quotientStalkBranchEquiv` of the stalks there.

* `NodalGluing.isOpenImmersion_ofRestrict_comp_normalizationSheafedSpaceHom` and its locally
  ringed version: the restriction of the normalization map to the complement of the flag points
  is an open immersion, with range the complement of the nodes
  (`NodalGluing.range_ofRestrict_comp_normalizationSheafedSpaceHom`).
* `NodalGluing.restrictComplFlagPointSetIso`: the normalization restricted to the complement of
  the flag points is isomorphic, as a sheafed space, to the glued curve restricted to the
  complement of its nodes, compatibly with the normalization map
  (`NodalGluing.restrictComplFlagPointSetIso_hom_ofRestrict`).

The open immersion is proved by Mathlib's criterion
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`: an open embedding with
isomorphisms on all stalks.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for the normalization description of nodal Riemann
  surfaces.
-/

public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace TauCeti.NodalGluing

open holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {ι : Type} {Flag : Type*} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace H (X i)] (d : FlagPairData ι Flag X)

/-- The normalization map of a glued nodal curve as a morphism of sheafed spaces: the quotient
map on points, and on sections the inclusion of matching holomorphic functions into holomorphic
functions on the normalization. -/
@[expose] def normalizationSheafedSpaceHom :
    holomorphicStructureSheaf.sheafedSpace I (Σ i, X i) ⟶ sheafedSpace I d :=
  InducedCategory.homMk
    { base := TopCat.quotientMk (gluedRelSetoid d)
      c := (quotientSheafι I (gluedRelSetoid d)).hom }

/-- On points, the normalization map is the quotient map. -/
@[simp]
theorem normalizationSheafedSpaceHom_hom_base_apply (x : Σ i, X i) :
    (normalizationSheafedSpaceHom I d).hom.base x = Quotient.mk (gluedRelSetoid d) x := (rfl)

/-- On sections, the normalization map is the inclusion `quotientSheafι` of matching holomorphic
functions into holomorphic functions on the normalization. -/
@[simp]
theorem normalizationSheafedSpaceHom_hom_c_app (U : (Opens (GluedCurve d))ᵒᵖ) :
    (normalizationSheafedSpaceHom I d).hom.c.app U =
      (quotientSheafι I (gluedRelSetoid d)).hom.app U := (rfl)

/-- The stalk map of the normalization map at a point of the normalization is restriction of
germs on the glued curve to that branch. -/
theorem stalkMap_normalizationSheafedSpaceHom (x : Σ i, X i) :
    (normalizationSheafedSpaceHom I d).hom.stalkMap x =
      CommRingCat.ofHom (quotientStalkBranch I (gluedRelSetoid d) _ x
        (normalizationSheafedSpaceHom_hom_base_apply I d x).symm) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_)
  rw [CommRingCat.comp_apply, PresheafedSpace.stalkMap_germ_apply,
    normalizationSheafedSpaceHom_hom_c_app]
  exact (congrArg _ (quotientSheafι_app_apply I (gluedRelSetoid d) U g)).trans
    (quotientStalkBranch_germ I (gluedRelSetoid d) _ x _ U hx g).symm

/-- The stalk map of the normalization map at a point of the normalization restricts a germ to
that branch. -/
@[simp]
theorem stalkMap_normalizationSheafedSpaceHom_apply (x : Σ i, X i)
    (g : (sheafedSpace I d).presheaf.stalk ((normalizationSheafedSpaceHom I d).hom.base x)) :
    ((normalizationSheafedSpaceHom I d).hom.stalkMap x).hom g =
      quotientStalkBranch I (gluedRelSetoid d) _ x
        (normalizationSheafedSpaceHom_hom_base_apply I d x).symm g := by
  rw [stalkMap_normalizationSheafedSpaceHom, CommRingCat.hom_ofHom]

variable [Finite Flag]

/-- Away from the flag points, the stalk maps of the normalization map are isomorphisms. -/
theorem isIso_stalkMap_normalizationSheafedSpaceHom [∀ i, T1Space (X i)] {x : Σ i, X i}
    (hx : x ∉ flagPointSet d) : IsIso ((normalizationSheafedSpaceHom I d).hom.stalkMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  rw [stalkMap_normalizationSheafedSpaceHom]
  exact quotientStalkBranch_bijective I d hx

/-- On points, the normalization map restricted to the complement of the flag points is the
restriction of the quotient map. -/
theorem ofRestrict_comp_normalizationSheafedSpaceHom_hom_base [∀ i, T1Space (X i)] :
    ⇑((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d).hom.base =
      fun x : complFlagPointSet d ↦ Quotient.mk (gluedRelSetoid d) (x : Σ i, X i) := (rfl)

/-- On points, the normalization map restricted to the complement of the flag points is the
quotient map. -/
theorem ofRestrict_comp_normalizationSheafedSpaceHom_hom_base_apply [∀ i, T1Space (X i)]
    (x : complFlagPointSet d) :
    ((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d).hom.base x =
      Quotient.mk (gluedRelSetoid d) (x : Σ i, X i) := (rfl)

/-- **The normalization map is an open immersion off the flag points.** Restricted to the
complement of the flag points, the normalization map of a glued curve with finitely many flag
pairs on `T1` components is an open immersion of sheafed spaces. -/
instance isOpenImmersion_ofRestrict_comp_normalizationSheafedSpaceHom [∀ i, T1Space (X i)] :
    SheafedSpace.IsOpenImmersion
      ((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d) := by
  refine SheafedSpace.IsOpenImmersion.of_stalk_iso _ ?_ (H := fun x ↦ ?_)
  · rw [ofRestrict_comp_normalizationSheafedSpaceHom_hom_base]
    exact isOpenEmbedding_domRestrict_quotient_mk d
  · have h₁ : IsIso ((normalizationSheafedSpaceHom I d).hom.stalkMap
        (((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
          (complFlagPointSet d).isOpenEmbedding).hom.base x)) :=
      isIso_stalkMap_normalizationSheafedSpaceHom I d ((mem_complFlagPointSet d).mp x.property)
    rw [InducedCategory.comp_hom, PresheafedSpace.stalkMap.comp]
    exact IsIso.comp_isIso' h₁ (PresheafedSpace.ofRestrict_stalkMap_isIso _ _ x)

/-- The restriction of the normalization map to the complement of the flag points has the
complement of the nodes as its range. -/
theorem range_ofRestrict_comp_normalizationSheafedSpaceHom [∀ i, T1Space (X i)] :
    Set.range ((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d).hom.base =
      (nodeSet d)ᶜ := by
  rw [ofRestrict_comp_normalizationSheafedSpaceHom_hom_base, ← image_quotient_mk_compl,
    ← coe_complFlagPointSet, Set.image_eq_range]
  -- An open set and its underlying set give the same subtype.
  rfl

/-- **The smooth locus of a glued curve is the normalization off the flag points.** The
normalization restricted to the complement of the flag points and the glued curve restricted to
the complement of its nodes are isomorphic sheafed spaces, through the normalization map. -/
def restrictComplFlagPointSetIso [∀ i, T1Space (X i)] :
    (holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).restrict
        (complFlagPointSet d).isOpenEmbedding ≅
      (sheafedSpace I d).restrict (complNodeSet d).isOpenEmbedding :=
  haveI : PresheafedSpace.IsOpenImmersion
      ((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d).hom :=
    isOpenImmersion_ofRestrict_comp_normalizationSheafedSpaceHom I d
  haveI : PresheafedSpace.IsOpenImmersion
      ((sheafedSpace I d).ofRestrict (complNodeSet d).isOpenEmbedding).hom :=
    SheafedSpace.IsOpenImmersion.ofRestrict _ _
  InducedCategory.isoMk
    (PresheafedSpace.IsOpenImmersion.isoOfRangeEq
      ((holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d).hom
      ((sheafedSpace I d).ofRestrict (complNodeSet d).isOpenEmbedding).hom (by
        rw [range_ofRestrict_comp_normalizationSheafedSpaceHom]
        exact Subtype.range_coe.symm))

/-- The isomorphism of the two complements, followed by the inclusion of the complement of the
nodes, is the normalization map on the complement of the flag points. -/
@[simp, reassoc]
theorem restrictComplFlagPointSetIso_hom_ofRestrict [∀ i, T1Space (X i)] :
    (restrictComplFlagPointSetIso I d).hom ≫ (sheafedSpace I d).ofRestrict
        (complNodeSet d).isOpenEmbedding =
      (holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d := by
  apply InducedCategory.hom_ext
  simp only [restrictComplFlagPointSetIso, InducedCategory.isoMk_hom,
    PresheafedSpace.IsOpenImmersion.isoOfRangeEq_hom]
  rw [InducedCategory.comp_hom, InducedCategory.homMk_hom,
    PresheafedSpace.IsOpenImmersion.lift_fac]

/-- The inverse of the isomorphism of the two complements, followed by the normalization map,
is the inclusion of the complement of the nodes. -/
@[simp, reassoc]
theorem restrictComplFlagPointSetIso_inv_ofRestrict_comp [∀ i, T1Space (X i)] :
    (restrictComplFlagPointSetIso I d).inv ≫
        (holomorphicStructureSheaf.sheafedSpace I (Σ i, X i)).ofRestrict
          (complFlagPointSet d).isOpenEmbedding ≫ normalizationSheafedSpaceHom I d =
      (sheafedSpace I d).ofRestrict (complNodeSet d).isOpenEmbedding := by
  rw [Iso.inv_comp_eq, restrictComplFlagPointSetIso_hom_ofRestrict]

/-- On points, the isomorphism of the two complements is the quotient map. -/
@[simp]
theorem coe_restrictComplFlagPointSetIso_hom_base_apply [∀ i, T1Space (X i)]
    (x : complFlagPointSet d) :
    ((restrictComplFlagPointSetIso I d).hom.hom.base x).val =
      Quotient.mk (gluedRelSetoid d) (x : Σ i, X i) :=
  (congrArg (fun f ↦ f.hom.base x) (restrictComplFlagPointSetIso_hom_ofRestrict I d)).trans
    (ofRestrict_comp_normalizationSheafedSpaceHom_hom_base_apply I d x)

/-- Restriction of germs on the glued curve to a branch is a local homomorphism, also at the
flag points. -/
instance isLocalHom_stalkMap_normalizationSheafedSpaceHom [∀ i, T2Space (X i)]
    (x : Σ i, X i) : IsLocalHom ((normalizationSheafedSpaceHom I d).hom.stalkMap x).hom := by
  refine ⟨fun a ha ↦ IsLocalRing.notMem_maximalIdeal.mp fun hmem ↦ ?_⟩
  rw [stalkMap_normalizationSheafedSpaceHom_apply] at ha
  -- The maximal ideal of the local ring of the glued curve is the kernel of evaluation.
  have hx := (normalizationSheafedSpaceHom_hom_base_apply I d x).symm
  have hker : a ∈ RingHom.ker
      ((eval I _ x).comp (quotientStalkBranch I (gluedRelSetoid d) _ x hx)) := by
    rw [IsLocalRing.ker_eq_maximalIdeal _ (eval_comp_quotientStalkBranch_surjective I _ _ x hx)]
    exact hmem
  exact (isUnit_stalk_iff I _ _).mp ha hker

/-- The normalization map of a glued nodal curve as a morphism of locally ringed spaces. -/
def normalizationLocallyRingedSpaceHom [∀ i, T2Space (X i)] :
    holomorphicStructureSheaf.locallyRingedSpace I (Σ i, X i) ⟶ locallyRingedSpace I d :=
  ⟨(normalizationSheafedSpaceHom I d).hom,
    isLocalHom_stalkMap_normalizationSheafedSpaceHom I d⟩

/-- The underlying morphism of sheafed spaces of the locally ringed normalization map. -/
@[simp]
theorem normalizationLocallyRingedSpaceHom_toShHom [∀ i, T2Space (X i)] :
    (normalizationLocallyRingedSpaceHom I d).toShHom = normalizationSheafedSpaceHom I d := (rfl)

/-- **The normalization map is an open immersion of locally ringed spaces off the flag
points.** -/
instance isOpenImmersion_ofRestrict_comp_normalizationLocallyRingedSpaceHom
    [∀ i, T2Space (X i)] :
    LocallyRingedSpace.IsOpenImmersion
      ((holomorphicStructureSheaf.locallyRingedSpace I (Σ i, X i)).ofRestrict
        (complFlagPointSet d).isOpenEmbedding ≫ normalizationLocallyRingedSpaceHom I d) :=
  isOpenImmersion_ofRestrict_comp_normalizationSheafedSpaceHom I d

end TauCeti.NodalGluing
