/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Recognising the glued scheme of a relative gluing datum

Let `d` be a relative gluing datum over a locally directed open cover `{Uᵢ}` of `S`: schemes `Xᵢ`
over `Uᵢ` whose transition maps are pullbacks. Mathlib's
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued` glues the `Xᵢ` to a scheme over `S`
whose preimage of `Uᵢ` is `Xᵢ`. This file proves the converse uniqueness: a scheme `p : Y ⟶ S`
with compatible maps `φᵢ : Xᵢ ⟶ Y` exhibiting each `Xᵢ` as the preimage `p⁻¹ Uᵢ` is the glued
scheme. This is how one identifies a scheme with a scheme glued over the base, for instance a
base change of a relative `Proj` with the relative `Proj` of the pulled back algebra.

## Main results

* `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isIso_desc_of_isPullback`: the morphism
  `glued ⟶ Y` induced by such maps `φᵢ` is an isomorphism.
* `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isoOfIsPullback`: the resulting isomorphism
  of the glued scheme with `Y`, compatible with the charts and with the maps to `S`.

## References

* The Stacks Project, [Tag 01LH](https://stacks.math.columbia.edu/tag/01LH).
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  (d : 𝒰.RelativeGluingData) [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  {Y : Scheme.{u}} (p : Y ⟶ S) (φ : d.functor ⟶ (Functor.const 𝒰.I₀).obj Y)

/-- The morphism from the glued scheme to `Y` induced by a cocone of the gluing diagram whose legs
lie over the structure maps `Xᵢ ⟶ Uᵢ` is a morphism over `S`. -/
@[reassoc]
theorem desc_comp_eq_toBase
    (hφ : ∀ i, φ.app i ≫ p = d.natTrans.app i ≫ 𝒰.f i) :
    colimit.desc d.functor ⟨Y, φ⟩ ≫ p = d.toBase :=
  colimit.hom_ext fun i ↦ by simp [hφ]

/-- **The glued scheme is the scheme whose preimages of the `Uᵢ` are the `Xᵢ`**: if `p : Y ⟶ S`
carries compatible maps `φᵢ : Xᵢ ⟶ Y` exhibiting each `Xᵢ` as the base change of `p` along
`Uᵢ ⟶ S`, then the induced morphism from the glued scheme to `Y` is an isomorphism. -/
@[stacks 01LH]
theorem isIso_desc_of_isPullback
    (hφ : ∀ i, IsPullback (d.natTrans.app i) (φ.app i) (𝒰.f i) p) :
    IsIso (colimit.desc d.functor ⟨Y, φ⟩) := by
  have hψ := d.desc_comp_eq_toBase p φ fun i ↦ (hφ i).w.symm
  -- `Y` is covered by the `φᵢ`, open immersions as base changes of the `Uᵢ ⟶ S`
  have : ∀ i, IsOpenImmersion (φ.app i) := fun i ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hφ i) (𝒰.map_prop i)
  let 𝒱 : Y.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀ d.functor.obj φ.app fun y ↦ by
    obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (p y)
    obtain ⟨x, -, hx⟩ := Scheme.exists_preimage_of_isPullback (hφ i) u y hu
    exact ⟨i, x, hx⟩
  refine IsZariskiLocalAtTarget.of_openCover (P := .isomorphisms Scheme) 𝒱 fun i ↦ ?_
  -- over `φᵢ` the morphism is the identity of `Xᵢ`, by pasting with the square of `p` over `Uᵢ`
  have hi : IsPullback (𝟙 _ ≫ d.natTrans.app i) (colimit.ι d.functor i) (𝒰.f i)
      (colimit.desc d.functor ⟨Y, φ⟩ ≫ p) := by
    simpa [hψ] using d.isPullback_natTrans_ι_toBase i
  have h : IsPullback (colimit.ι d.functor i) (𝟙 _) (colimit.desc d.functor ⟨Y, φ⟩) (φ.app i) :=
    (hi.of_right (by simp only [Category.id_comp]; exact (colimit.ι_desc (Cocone.mk Y φ) i).symm)
      (hφ i)).flip
  -- `𝒱.pullbackHom _ i` is by definition the second projection of the pullback along the
  -- `i`-th map of `𝒱`, which is `φ.app i` by construction of `Scheme.Cover.mkOfCovers`
  change IsIso (pullback.snd (colimit.desc d.functor ⟨Y, φ⟩) (φ.app i))
  rw [← (IsPullback.of_hasPullback _ _).isoIsPullback_hom_snd _ _ h, Category.comp_id]
  infer_instance

/-- The isomorphism of the glued scheme of a relative gluing datum with a scheme `p : Y ⟶ S`
carrying compatible maps `φᵢ : Xᵢ ⟶ Y` that exhibit each `Xᵢ` as the base change of `p` along
`Uᵢ ⟶ S`. -/
noncomputable def isoOfIsPullback
    (hφ : ∀ i, IsPullback (d.natTrans.app i) (φ.app i) (𝒰.f i) p) : d.glued ≅ Y :=
  have := d.isIso_desc_of_isPullback p φ hφ
  asIso (colimit.desc d.functor ⟨Y, φ⟩)

/-- The isomorphism `isoOfIsPullback` restricts to `φᵢ` on the chart `Xᵢ`. -/
@[reassoc (attr := simp)]
theorem ι_isoOfIsPullback_hom
    (hφ : ∀ i, IsPullback (d.natTrans.app i) (φ.app i) (𝒰.f i) p) (i : 𝒰.I₀) :
    colimit.ι d.functor i ≫ (d.isoOfIsPullback p φ hφ).hom = φ.app i :=
  colimit.ι_desc _ _

/-- The isomorphism `isoOfIsPullback` is an isomorphism over `S`. -/
@[reassoc (attr := simp)]
theorem isoOfIsPullback_hom_comp
    (hφ : ∀ i, IsPullback (d.natTrans.app i) (φ.app i) (𝒰.f i) p) :
    (d.isoOfIsPullback p φ hφ).hom ≫ p = d.toBase :=
  d.desc_comp_eq_toBase p φ fun i ↦ (hφ i).w.symm

end AlgebraicGeometry.Scheme.Cover.RelativeGluingData
