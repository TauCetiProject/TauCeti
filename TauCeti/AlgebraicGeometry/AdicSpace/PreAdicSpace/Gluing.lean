/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Descent
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Gluing
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.HasColimits
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# Gluing pre-adic spaces

Compatibility with stalk valuations can be checked after precomposition with a jointly
surjective family of morphisms. In particular it can be checked on an open cover. This lets a
morphism of presheafed spaces obtained by gluing chartwise morphisms lift uniquely to a morphism of
pre-adic spaces. Consequently, a cocone of pre-adic spaces with jointly surjective legs is a
colimit whenever its underlying cocone of presheafed spaces is a colimit.

This gives gluing in the category `𝒱^pre` of pre-adic spaces. Glue data in `𝒱^pre`
(`TauCeti.PreAdicSpace.GlueData`) consist of pre-adic spaces `U i`, open immersions
`f i j : V i j ⟶ U i` and transition morphisms `t i j : V i j ⟶ V j i` of pre-adic spaces
satisfying the cocycle condition. Their underlying presheafed spaces of complete separated
topological rings glue (`AlgebraicGeometry.PresheafedSpace.GlueData`), and the charts of the glued
presheafed space are open immersions, so its stalks are those of the `U i`. Two points of the
charts with the same image come from a point of an overlap `V i j`, where the transition
morphisms are compatible with the stalk valuations; so the stalk valuations of the `U i` descend
to the glued space (`TauCeti.PreAdicSpace.descend`). The resulting pre-adic space, with the charts
as legs, is a colimit in `𝒱^pre` by the lifting statement above. As for schemes, the glued object
is then `CategoryTheory.GlueData.glued`, its charts `ι i` are open immersions which are jointly
surjective, and `V i j` is the intersection of the images of `U i` and `U j`.

Gluing adic spaces gives an adic space. The glued space is sheafy because a colimit of presheafed
spaces with sheaf structure presheaves has a sheaf structure presheaf
(`AlgebraicGeometry.PresheafedSpace.isSheaf_of_isColimit`). It is locally affinoid because its
charts are open immersions covering it. Conversely its charts are open adic subspaces, so the
glued space is adic exactly when every piece is (`TauCeti.PreAdicSpace.GlueData.isAdic_glued_iff`).
Since `(Adic)` is a full subcategory of `𝒱^pre`, the glued adic space is then a colimit of the
gluing diagram in `(Adic)`.

## Main definitions

* `TauCeti.PreAdicSpace.Hom.ofCover`: lift a presheafed-space morphism from its chartwise
  lifts, for a jointly surjective family.
* `TauCeti.PreAdicSpace.isColimitOfIsColimitForgetToPresheafedSpace`: lift an underlying
  colimit cocone with jointly surjective legs.
* `TauCeti.PreAdicSpace.GlueData`: glue data of pre-adic spaces along open immersions.
* `TauCeti.PreAdicSpace.GlueData.isoPresheafedSpace`: the underlying presheafed space of the glued
  pre-adic space is the glued presheafed space.
* `TauCeti.PreAdicSpace.GlueData.vPullbackConeIsLimit`: `V i j` is the pullback of the charts
  `U i` and `U j` of the glued space.
* `TauCeti.PreAdicSpace.GlueData.gluedAdicι`: for adic pieces, the charts of the glued adic
  space, as a natural transformation out of the gluing diagram in `(Adic)`.
* `TauCeti.PreAdicSpace.GlueData.isColimitGluedAdicCocone`: the universal property of the glued
  adic space in `(Adic)`.

## Main results

* The `HasMulticoequalizer` instance for `TauCeti.PreAdicSpace.GlueData`: glue data of pre-adic
  spaces have a glued pre-adic space `CategoryTheory.GlueData.glued`, and the forgetful functor to
  presheafed spaces preserves it.
* `TauCeti.PreAdicSpace.GlueData.ι_isOpenImmersion`: the charts of the glued space are open
  immersions.
* `TauCeti.PreAdicSpace.GlueData.ι_jointly_surjective`: the charts of the glued space are jointly
  surjective.
* `TauCeti.PreAdicSpace.GlueData.ι_eq_iff_rel`: two points of the charts have the same image in
  the glued space exactly when they come from a common point of an overlap.
* `TauCeti.PreAdicSpace.GlueData.isSheafy_glued_iff`,
  `TauCeti.PreAdicSpace.GlueData.isLocallyAffinoid_glued_iff`,
  `TauCeti.PreAdicSpace.GlueData.isAdic_glued_iff`: the glued space is sheafy, locally affinoid,
  or adic exactly when every piece is.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and §8.3.
* Mathlib's `AlgebraicGeometry.PresheafedSpace.GlueData` provides the underlying gluing;
  `CategoryTheory.Limits.IsColimit.ofFaithful` lifts its universal property. The construction of
  the glued object follows `AlgebraicGeometry.Scheme.GlueData`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.PreAdicSpace

universe u v w

variable {X Y : PreAdicSpace.{u}} {ι : Type v} {U : ι → PreAdicSpace.{u}}

/-- A presheafed-space morphism lifts to a morphism of pre-adic spaces if it lifts after
precomposition with a jointly surjective family. No sheaf condition is needed: the underlying
morphism is already given, and valuation compatibility is checked pointwise on stalks. -/
def Hom.ofCover (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) : X ⟶ Y where
  toHom := g
  stalkValuation_eq x := by
    obtain ⟨i, y, rfl⟩ := hcover x
    let y' : (U i).toRingPresheafedSpace := y
    have hf := (f i).stalkValuation_eq y'
    -- Rewrite the entire underlying morphism, including the base point in the stalk type.
    -- The composite base point is definitionally `g.base ((j i).base y)`; rewriting only
    -- that point would give an ill-typed motive.
    rw [← hfac i, toRingPresheafedSpaceHom, Functor.map_comp,
      PresheafedSpace.stalkMap.comp] at hf
    rw [(j i).stalkValuation_eq_comap y, Hom.stalkMap_def]
    exact hf.trans (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm

/-- The lift retains the given underlying morphism of presheafed spaces. -/
@[simp]
theorem Hom.ofCover_toHom (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) :
    (Hom.ofCover j hcover g f hfac).toHom = g := (rfl)

/-- The lifted morphism agrees with the given morphism on each chart. -/
@[reassoc (attr := simp)]
theorem Hom.comp_ofCover (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) (i : ι) :
    j i ≫ Hom.ofCover j hcover g f hfac = f i := by
  apply Hom.ext'
  simpa using hfac i

/-- **The universal property of gluing lifts to pre-adic spaces.** A cocone whose legs are
jointly surjective is a colimit if its underlying cocone of presheafed spaces is a colimit. In
particular, once the glued object and its chart inclusions have been equipped
with their pre-adic structures, no further valuation condition is needed for the universal
property. The diagram and the target of a descended morphism need not be sheafy. -/
noncomputable def isColimitOfIsColimitForgetToPresheafedSpace
    {J : Type v} [Category.{w} J] {F : J ⥤ PreAdicSpace.{u}} (c : Cocone F)
    (hcover : ∀ x : c.pt, ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x)
    (hc : IsColimit (forgetToPresheafedSpace.mapCocone c)) : IsColimit c := by
  refine IsColimit.ofFaithful forgetToPresheafedSpace hc
    (fun s ↦ Hom.ofCover c.ι.app hcover (hc.desc (forgetToPresheafedSpace.mapCocone s))
      s.ι.app (fun i ↦ hc.fac _ i)) (fun s ↦ ?_)
  exact Hom.ofCover_toHom c.ι.app hcover (hc.desc (forgetToPresheafedSpace.mapCocone s))
    s.ι.app (fun i ↦ hc.fac _ i)

/-- The descended morphism in the lifted colimit is the underlying presheafed-space descent.
Thus the colimit lift changes neither the continuous map nor the map of structure presheaves. -/
@[simp]
theorem isColimitOfIsColimitForgetToPresheafedSpace_desc_toHom
    {J : Type v} [Category.{w} J] {F : J ⥤ PreAdicSpace.{u}} (c : Cocone F)
    (hcover : ∀ x : c.pt, ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x)
    (hc : IsColimit (forgetToPresheafedSpace.mapCocone c)) (s : Cocone F) :
    ((isColimitOfIsColimitForgetToPresheafedSpace c hcover hc).desc s).toHom =
      hc.desc (forgetToPresheafedSpace.mapCocone s) := (rfl)

/-! ### Glue data of pre-adic spaces -/

/-- **Glue data of pre-adic spaces**: glue data in the category `𝒱^pre` whose gluing maps
`f i j : V i j ⟶ U i` are open immersions of pre-adic spaces. -/
structure GlueData extends CategoryTheory.GlueData PreAdicSpace.{u} where
  /-- The gluing maps are open immersions. -/
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The glue data of presheafed spaces of complete separated topological rings underlying glue
data of pre-adic spaces. -/
noncomputable abbrev toPresheafedSpaceGlueData :
    PresheafedSpace.GlueData CompleteSeparatedTopCommRingCat.{u} :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }

local notation "𝖣'" => D.toPresheafedSpaceGlueData.toGlueData

/-- The glue condition for the charts of the glued presheafed space, stated for the underlying
morphisms of the gluing maps of pre-adic spaces. -/
private theorem toHom_glue_condition (i j : D.J) :
    (D.f i j).toHom ≫ 𝖣'.ι i = (D.t i j ≫ D.f j i).toHom ≫ 𝖣'.ι j := by
  rw [comp_toHom]
  -- the legs of `mapGlueData forgetToPresheafedSpace` are the underlying morphisms `toHom` of
  -- the pre-adic gluing maps only definitionally, so the glue condition is applied by `exact`
  exact (D.toPresheafedSpaceGlueData.glue_condition i j).symm.trans (Category.assoc _ _ _).symm

/-- Points of charts with the same image in the glued presheafed space come from a point of an
overlap, where the transition morphisms of pre-adic spaces are compatible with the stalk
valuations. So the valuations they induce on the stalk of the glued presheafed space agree: the
compatibility hypothesis of `descend` for the charts. -/
private theorem comap_stalkMap_ι_eq (i j : D.J) (x : D.U i) (x' : D.U j)
    (h : (𝖣'.ι i).base x = (𝖣'.ι j).base x') :
    ValuationSpectrum.comap ((toRingPresheafedSpaceHom (X := D.U j) (𝖣'.ι j)).stalkMap x').hom
        ((D.U j).stalkValuation x') =
      ValuationSpectrum.comap (eqToHom (congrArg
        ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj
          𝖣'.glued).presheaf.stalk h.symm)).hom
        (ValuationSpectrum.comap ((toRingPresheafedSpaceHom (X := D.U i) (𝖣'.ι i)).stalkMap x).hom
          ((D.U i).stalkValuation x)) := by
  obtain ⟨z, rfl, rfl⟩ :
      ∃ z : D.V (i, j), (D.f i j).base z = x ∧ (D.t i j ≫ D.f j i).base z = x' :=
    (D.toPresheafedSpaceGlueData.ι_eq_iff_rel i j x x').mp h
  exact comap_stalkMap_base_eq_of_comp_eq (X := D.U) (π := fun k ↦ 𝖣'.ι k) (D.f i j)
    (D.t i j ≫ D.f j i) (D.toHom_glue_condition i j) z h

/-- The glued presheafed space with the stalk valuations descended from the charts. -/
private noncomputable def gluedPreAdicSpace : PreAdicSpace.{u} :=
  descend D.U (fun i ↦ 𝖣'.ι i) D.toPresheafedSpaceGlueData.ι_jointly_surjective fun i x ↦
    -- forgetting the topology on sections keeps the chart an open immersion
    have := PresheafedSpace.IsOpenImmersion.mapPresheaf_map
      (H := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i)
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat) (𝖣'.ι i)
    PresheafedSpace.IsOpenImmersion.stalk_iso (H := this)
      (toRingPresheafedSpaceHom (X := D.U i) (𝖣'.ι i)) x

/-- The charts of the glued presheafed space, as morphisms of pre-adic spaces. -/
private noncomputable def ιGlued (i : D.J) : D.U i ⟶ D.gluedPreAdicSpace :=
  toDescend (X := D.U) (π := fun k ↦ 𝖣'.ι k) _ _ D.comap_stalkMap_ι_eq i

/-- The underlying morphism of presheafed spaces of `ιGlued i` is the chart `𝖣'.ι i`. -/
private theorem ιGlued_toHom (i : D.J) : (D.ιGlued i).toHom = 𝖣'.ι i :=
  toDescend_toHom (X := D.U) (π := fun k ↦ 𝖣'.ι k) ..

/-- The glue condition for the charts of the glued presheafed space, as morphisms of pre-adic
spaces. -/
private theorem f_comp_ιGlued (i j : D.J) :
    D.f i j ≫ D.ιGlued i = (D.t i j ≫ D.f j i) ≫ D.ιGlued j :=
  Hom.ext' (by
    rw [comp_toHom, comp_toHom, ιGlued_toHom, ιGlued_toHom]
    exact D.toHom_glue_condition i j)

/-- The glued pre-adic space as a multicofork of the gluing diagram. -/
private noncomputable def gluedMulticofork : Multicofork 𝖣.diagram :=
  Multicofork.ofπ 𝖣.diagram D.gluedPreAdicSpace D.ιGlued fun ⟨i, j⟩ ↦ D.f_comp_ιGlued i j

/-- The underlying multicofork of presheafed spaces is the glued presheafed space. -/
private noncomputable def isColimitMapCocone :
    IsColimit (forgetToPresheafedSpace.mapCocone D.gluedMulticofork) :=
  (IsColimit.precomposeInvEquiv (𝖣.diagramIso forgetToPresheafedSpace) _).1
    ((colimit.isColimit 𝖣'.diagram.multispan).ofIsoColimit
      -- the legs of both multicoforks are the charts `𝖣'.ι i` of the glued presheafed space, up to
      -- identities; the multicoforks live over diagrams which agree only up to unfolding
      -- `GlueData.mapGlueData`, so the legs are compared definitionally rather than by rewriting
      (Multicofork.ext (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))

/-- The glued pre-adic space is a colimit of the gluing diagram in `𝒱^pre`, since its charts are
jointly surjective and its underlying multicofork is a colimit. -/
private noncomputable def isColimitGluedMulticofork : IsColimit D.gluedMulticofork :=
  isColimitOfIsColimitForgetToPresheafedSpace _ (fun x ↦
    have ⟨i, y, hy⟩ := D.toPresheafedSpaceGlueData.ι_jointly_surjective x
    -- the leg of `gluedMulticofork` at `U i` is `ιGlued i` by definition
    ⟨.right i, y, (congrArg (fun g ↦ g.base y) (D.ιGlued_toHom i)).trans hy⟩)
    D.isColimitMapCocone

/-- **Glue data of pre-adic spaces glue**: the gluing diagram has a colimit in `𝒱^pre`. Its
underlying presheafed space is the glued presheafed space, with the stalk valuations of the
charts. -/
instance : HasMulticoequalizer 𝖣.diagram :=
  ⟨⟨⟨_, D.isColimitGluedMulticofork⟩⟩⟩

/-- The forgetful functor to presheafed spaces preserves the gluing of pre-adic spaces. -/
instance : PreservesColimit 𝖣.diagram.multispan forgetToPresheafedSpace :=
  preservesColimit_of_preserves_colimit_cocone D.isColimitGluedMulticofork D.isColimitMapCocone

/-- The underlying presheafed space of the glued pre-adic space is the glued presheafed space. -/
noncomputable abbrev isoPresheafedSpace : 𝖣.glued.toPresheafedSpace ≅ 𝖣'.glued :=
  𝖣.gluedIso forgetToPresheafedSpace

/-- Under `isoPresheafedSpace`, the charts of the glued pre-adic space are those of the glued
presheafed space. -/
@[reassoc]
theorem ι_isoPresheafedSpace_inv (i : D.J) :
    𝖣'.ι i ≫ D.isoPresheafedSpace.inv = (𝖣.ι i).toHom :=
  𝖣.ι_gluedIso_inv forgetToPresheafedSpace i

/-- **The charts of a glued pre-adic space are open immersions.** -/
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [IsOpenImmersion, ← D.ι_isoPresheafedSpace_inv]
  exact PresheafedSpace.IsOpenImmersion.comp (H := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i)
    _ _

/-- On points, the chart `ι k` of the glued pre-adic space is the chart of the glued presheafed
space followed by `isoPresheafedSpace.inv`. -/
private theorem isoPresheafedSpace_inv_base_ι (k : D.J) (z : D.U k) :
    D.isoPresheafedSpace.inv.base ((𝖣'.ι k).base z) = (𝖣.ι k).base z :=
  ConcreteCategory.congr_hom (congrArg PresheafedSpace.Hom.base (D.ι_isoPresheafedSpace_inv k)) z

/-- **The charts of a glued pre-adic space are jointly surjective.** -/
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  -- the image of the cospan of open immersions `f i j`, `f i k` is again such a cospan, whose
  -- pullback is preserved by the forgetful functor to topological spaces
  have (i j k : D.J) : PreservesLimit (cospan (D.f i j) (D.f i k) ⋙ forgetToPresheafedSpace)
      (PresheafedSpace.forget _) :=
    have : PreservesLimit (cospan (forgetToPresheafedSpace.map (D.f i j))
        (forgetToPresheafedSpace.map (D.f i k))) (PresheafedSpace.forget _) :=
      PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfLeft (hf := D.f_open i j) _ _
    preservesLimit_of_iso_diagram _ (cospanCompIso _ _ _).symm
  𝖣.ι_jointly_surjective
    (forgetToPresheafedSpace ⋙ PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

/-- **Points with the same image in a glued pre-adic space.** Points `x` of `U i` and `y` of
`U j` have the same image in the glued space if and only if there is a point `z` of `V i j` with
`f i j z = x` and `f j i (t i j z) = y`. -/
theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    (𝖣.ι i).base x = (𝖣.ι j).base y ↔
      D.toPresheafedSpaceGlueData.toTopGlueData.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  rw [← D.isoPresheafedSpace_inv_base_ι i x, ← D.isoPresheafedSpace_inv_base_ι j y]
  exact ((TopCat.mono_iff_injective _).mp inferInstance).eq_iff.trans
    (D.toPresheafedSpaceGlueData.ι_eq_iff_rel i j x y)

/-- **`V i j` is the intersection of the charts `U i` and `U j`**: the square formed by
`f i j : V i j ⟶ U i`, `t i j ≫ f j i : V i j ⟶ U j` and the charts of the glued pre-adic space is
a pullback in `𝒱^pre`. -/
noncomputable def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  -- pullbacks along open immersions exist in `𝒱^pre` and are preserved by the forgetful functor,
  -- which reflects isomorphisms, so it reflects them
  have : ReflectsLimit (cospan (𝖣.ι i) (𝖣.ι j)) forgetToPresheafedSpace :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit i j)

/-! ### Gluing adic spaces -/

/-- **A glued pre-adic space is sheafy exactly when the pieces are.** The overlaps `V i j` are
sheafy as open subspaces of the `U i`, and the underlying presheafed space of the glued space is a
colimit of the gluing diagram among presheafed spaces, whose structure presheaf is a limit of
pushforwards of the structure sheaves of the `U i` and `V i j`. Conversely each `U i` is an open
subspace of the glued space. -/
@[simp]
theorem isSheafy_glued_iff : isSheafy 𝖣.glued ↔ ∀ i, isSheafy (D.U i) :=
  ⟨fun h i ↦ isSheafy_of_isOpenImmersion h (𝖣.ι i), fun hU ↦
    PresheafedSpace.isSheaf_of_isColimit (𝖣.diagram.multispan ⋙ forgetToPresheafedSpace)
      (fun
        | .left (⟨i, j⟩ : D.J × D.J) =>
          (isSheafy_of_isOpenImmersion (hU i) (D.f i j) : isSheafy (D.V (i, j)))
        | .right i => hU i)
      (isColimitOfPreserves forgetToPresheafedSpace (colimit.isColimit 𝖣.diagram.multispan))⟩

/-- **A glued pre-adic space is locally affinoid exactly when the pieces are**, since the charts
of the glued space are open immersions covering it. -/
@[simp]
theorem isLocallyAffinoid_glued_iff :
    isLocallyAffinoid 𝖣.glued ↔ ∀ i, isLocallyAffinoid (D.U i) :=
  ⟨fun h i ↦ isLocallyAffinoid_of_isOpenImmersion h (𝖣.ι i), fun hU ↦
    isLocallyAffinoid_of_jointly_surjective 𝖣.ι hU D.ι_jointly_surjective⟩

/-- **A glued pre-adic space is an adic space exactly when the pieces are**: gluing adic spaces
gives an adic space, and conversely each `U i` is an open adic subspace of the glued space. -/
@[simp]
theorem isAdic_glued_iff : isAdic 𝖣.glued ↔ ∀ i, isAdic (D.U i) := by
  simp only [isAdic_iff, isSheafy_glued_iff, isLocallyAffinoid_glued_iff, forall_and]

/-- **The gluing diagram of adic pieces lies in `(Adic)`**: if every piece `U i` is an adic
space, then so is every object of the gluing diagram, the overlaps `V i j` being open adic
subspaces of the `U i`. So the gluing diagram lifts to `(Adic)` as
`isAdic.lift 𝖣.diagram.multispan (D.isAdic_multispan_obj hU)`. -/
theorem isAdic_multispan_obj (hU : ∀ i, isAdic (D.U i)) :
    ∀ j, isAdic (𝖣.diagram.multispan.obj j)
  | .left (⟨i, j⟩ : D.J × D.J) =>
    (isAdic_of_isOpenImmersion (hU i) (D.f i j) : isAdic (D.V (i, j)))
  | .right i => hU i

/-- The charts of the glued adic space of glue data of pre-adic spaces whose pieces are adic
spaces, as a natural transformation from the gluing diagram in `(Adic)` to the constant diagram
at the glued adic space. Its legs are described by `gluedAdicι_app_right_hom` and
`gluedAdicι_app_left_hom`. -/
noncomputable def gluedAdicι (hU : ∀ i, isAdic (D.U i)) :
    isAdic.lift 𝖣.diagram.multispan (D.isAdic_multispan_obj hU) ⟶
      (Functor.const _).obj (⟨𝖣.glued, D.isAdic_glued_iff.mpr hU⟩ : AdicSpace.{u}) where
  app j := ObjectProperty.homMk (colimit.ι 𝖣.diagram.multispan j)
  naturality _ _ f := ObjectProperty.hom_ext (P := isAdic)
    ((colimit.w 𝖣.diagram.multispan f).trans (Category.comp_id _).symm)

/-- The leg of `gluedAdicι` at `U i` is the chart `ι i` of the glued pre-adic space. -/
@[simp]
theorem gluedAdicι_app_right_hom (hU : ∀ i, isAdic (D.U i)) (i : D.J) :
    ((D.gluedAdicι hU).app (.right i)).hom = 𝖣.ι i := (rfl)

/-- The leg of `gluedAdicι` at `V i j` is `f i j ≫ ι i`. -/
@[simp]
theorem gluedAdicι_app_left_hom (hU : ∀ i, isAdic (D.U i)) (i j : D.J) :
    ((D.gluedAdicι hU).app (.left (i, j))).hom = D.f i j ≫ 𝖣.ι i :=
  (congrArg (·.hom) ((Cocone.mk _ (D.gluedAdicι hU)).w (.fst (i, j)))).symm

/-- **The universal property of the glued adic space**: gluing adic spaces along open immersions
gives a colimit of the gluing diagram in the category `(Adic)` of adic spaces, with the charts
`gluedAdicι` as legs. -/
noncomputable def isColimitGluedAdicCocone (hU : ∀ i, isAdic (D.U i)) :
    IsColimit (Cocone.mk _ (D.gluedAdicι hU)) :=
  -- the image of this cocone in `𝒱^pre` is the colimit cocone of the gluing diagram, up to the
  -- definitional equality `isAdic.lift 𝖣.diagram.multispan _ ⋙ isAdic.ι = 𝖣.diagram.multispan`
  -- of `ObjectProperty.liftCompιIso`, and the fully faithful inclusion reflects colimits
  isColimitOfReflects isAdic.ι (colimit.isColimit 𝖣.diagram.multispan)

end GlueData

end TauCeti.PreAdicSpace
