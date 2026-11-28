/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Gluing ideal sheaves along a locally directed open cover

Let `𝒰` be a locally directed open cover of a scheme `X`, for instance the cover of a scheme by
its affine opens, or the cover of a relative Grassmannian by its parts over the affine opens of the
base. A family of ideal sheaves `J i` on the members `𝒰.X i` which is compatible with the
transition maps, `(J j).comap (𝒰.trans h) = J i` for `h : i ⟶ j`, glues to a unique ideal sheaf
on `X` whose inverse image on each `𝒰.X i` is `J i`
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_glue` and
`AlgebraicGeometry.Scheme.IdealSheafData.eq_glue_iff`).

The glued ideal sheaf is the kernel of a closed immersion: the closed subschemes of the `J i` form
a relative gluing datum over `𝒰` (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), since for
`h : i ⟶ j` the closed subscheme of `J i` is the part over `𝒰.X i` of that of `J j`. The glued
scheme lies over `X`, and over each `𝒰.X i` it is the closed subscheme of `J i`, so its structure
morphism is a closed immersion, local on the target. Closed conditions stated over the members of
a cover, such as closed loci of Grassmannians cut out over the affine opens of the base, glue in
this way.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.glue 𝒰 J hJ`: the ideal sheaf on `X` glued from a
  compatible family of ideal sheaves on the members of `𝒰`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_glue`: its inverse image on `𝒰.X i` is `J i`.
* `AlgebraicGeometry.Scheme.IdealSheafData.eq_glue_iff`: it is the only ideal sheaf with these
  inverse images.
* `AlgebraicGeometry.Scheme.IdealSheafData.glue_le_ker_iff`: a morphism `T ⟶ X` factors through
  the glued closed subscheme exactly when its restriction over each `𝒰.X i` factors through the
  closed subscheme of `J i`.

## References

* [The Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH), for relative
  gluing.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (𝒰 : X.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]
  (J : ∀ i, (𝒰.X i).IdealSheafData) (hJ : ∀ {i j : 𝒰.I₀} (h : i ⟶ j), (J j).comap (𝒰.trans h) = J i)

-- The closed subschemes of the `J i`, with the morphisms between them induced by the transition
-- maps of `𝒰`.
private noncomputable def glueFunctor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj i := (J i).subscheme
  map {i j} h := subschemeMap (J i) (J j) (𝒰.trans h) (le_map_iff_comap_le.2 (hJ h).le)
  map_id i := by
    rw [← cancel_mono (J i).subschemeι, subschemeMap_subschemeι, 𝒰.trans_id, Category.comp_id,
      Category.id_comp]
  map_comp {i j l} h h' := by
    rw [← cancel_mono (J l).subschemeι]
    simp [𝒰.trans_comp]

-- For `h : i ⟶ j`, the closed subscheme of `J i` is the part over `𝒰.X i` of that of `J j`.
private lemma isPullback_glueFunctor_map {i j : 𝒰.I₀} (h : i ⟶ j) :
    IsPullback ((glueFunctor 𝒰 J hJ).map h) (J i).subschemeι (J j).subschemeι (𝒰.trans h) := by
  refine (isPullback_of_isClosedImmersion (J i).subschemeι (J j).subschemeι
    ((glueFunctor 𝒰 J hJ).map h) (𝒰.trans h)
    (subschemeMap_subschemeι _ _ _ (le_map_iff_comap_le.2 (hJ h).le)).symm ?_).flip
  rw [ker_subschemeι, ker_subschemeι, hJ h]

-- The closed subschemes of the `J i` as a relative gluing datum over `𝒰`.
private noncomputable def glueGluingData : 𝒰.RelativeGluingData where
  functor := glueFunctor 𝒰 J hJ
  natTrans :=
    { app i := (J i).subschemeι
      naturality _ _ h := subschemeMap_subschemeι _ _ _ (le_map_iff_comap_le.2 (hJ h).le) }
  equifibered _ _ h := isPullback_glueFunctor_map 𝒰 J hJ h

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

-- Over each `𝒰.X i`, the glued scheme is the closed subscheme of `J i`.
private lemma isPullback_glueGluingData (i : 𝒰.I₀) :
    IsPullback (J i).subschemeι (colimit.ι (glueGluingData 𝒰 J hJ).functor i) (𝒰.f i)
      (glueGluingData 𝒰 J hJ).toBase :=
  (glueGluingData 𝒰 J hJ).isPullback_natTrans_ι_toBase i

-- The glued scheme is a closed subscheme of `X`, as it is one over each member of `𝒰`.
private instance isClosedImmersion_glueGluingData_toBase :
    IsClosedImmersion (glueGluingData 𝒰 J hJ).toBase := by
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun i ↦ ?_
  -- the base change along `𝒰.f i` is the closed immersion of `J i`, up to isomorphism; the
  -- `change` unfolds `Cover.pullbackHom`, which is by definition this second projection
  have H := (isPullback_glueGluingData 𝒰 J hJ i).flip
  change IsClosedImmersion (pullback.snd (glueGluingData 𝒰 J hJ).toBase (𝒰.f i))
  rw [← H.isoPullback_inv_snd]
  infer_instance

/-- The **ideal sheaf glued from a compatible family**: for a locally directed open cover `𝒰` of
`X` and ideal sheaves `J i` on its members compatible with its transition maps, the ideal sheaf on
`X` whose inverse image on each `𝒰.X i` is `J i`
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_glue`). -/
noncomputable def glue : X.IdealSheafData :=
  (glueGluingData 𝒰 J hJ).toBase.ker

/-- The inverse image of the glued ideal sheaf on a member `𝒰.X i` of the cover is `J i`. -/
@[simp]
theorem comap_glue (i : 𝒰.I₀) : (glue 𝒰 J hJ).comap (𝒰.f i) = J i := by
  rw [glue, ← ker_eq_comap_of_isPullback_of_isOpenImmersion (𝒰.f i)
    (isPullback_glueGluingData 𝒰 J hJ i), ker_subschemeι]

/-- **Uniqueness of the glued ideal sheaf.** An ideal sheaf on `X` is the one glued from the
`J i` exactly when its inverse image on each member `𝒰.X i` of the cover is `J i`. -/
theorem eq_glue_iff {I : X.IdealSheafData} : I = glue 𝒰 J hJ ↔ ∀ i, I.comap (𝒰.f i) = J i :=
  ⟨fun h i ↦ h ▸ comap_glue 𝒰 J hJ i, fun h ↦
    ext_of_comap_openCover 𝒰 fun i ↦ (h i).trans (comap_glue 𝒰 J hJ i).symm⟩

/-- **The glued closed subscheme on points.** A morphism `g : T ⟶ X` factors through the closed
subscheme of the glued ideal sheaf exactly when, for each member `𝒰.X i` of the cover, its
restriction `T ×_X 𝒰.X i ⟶ 𝒰.X i` factors through the closed subscheme of `J i`. -/
theorem glue_le_ker_iff {T : Scheme.{u}} (g : T ⟶ X) :
    glue 𝒰 J hJ ≤ g.ker ↔ ∀ i, J i ≤ (pullback.snd g (𝒰.f i)).ker := by
  -- an ideal sheaf lies in the kernel of a morphism exactly when its inverse image vanishes
  have hbot {Y Z : Scheme.{u}} (I : Z.IdealSheafData) (f : Y ⟶ Z) :
      I ≤ f.ker ↔ I.comap f = ⊥ := by
    rw [← map_bot, le_map_iff_comap_le, le_bot_iff]
  -- the inverse image along `T ×_X 𝒰.X i ⟶ T` is the inverse image of `J i` along the projection
  -- to `𝒰.X i`
  have hcomap (i : 𝒰.I₀) : ((glue 𝒰 J hJ).comap g).comap (pullback.fst g (𝒰.f i)) =
      (J i).comap (pullback.snd g (𝒰.f i)) := by
    rw [← comap_comp, pullback.condition, comap_comp, comap_glue]
  simp only [hbot]
  refine ⟨fun h i ↦ by rw [← hcomap, h, comap_bot], fun h ↦ ?_⟩
  refine ext_of_comap_openCover (𝒰.pullback₁ g) fun i ↦ ?_
  rw [comap_bot]
  exact (hcomap i).trans (h i)

end AlgebraicGeometry.Scheme.IdealSheafData
