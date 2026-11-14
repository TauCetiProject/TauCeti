/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict

import TauCeti.Geometry.RingedSpace.PresheafedSpace.GlueMorphisms

/-!
# Gluing morphisms of locally ringed spaces along open covers

Let `X` and `Y` be locally ringed spaces and let `U : ι → Opens X` be an open cover of `X`
(`⨆ i, U i = ⊤`). A family of morphisms `f i : X|_{U i} ⟶ Y` agreeing on the pairwise intersections
`U i ⊓ U j` glues to a unique morphism `X ⟶ Y` whose restriction to each `U i` is `f i`
(EGA I, Ch. I, proof of 2.2.4, p. 99; 10.4.6, p. 186).

On the underlying presheafed spaces, the family glues by
`AlgebraicGeometry.PresheafedSpace.glueMorphisms` because `X.presheaf` is a sheaf and the pullback
of `X|_{U i}` and `X|_{U j}` over `X` factors through `X|_{U i ⊓ U j}`. Locality of the glued
morphism on stalks is checked locally on `X`: every point `x : X` lies in some `U i`, where the
stalk map of `X|_{U i} ⟶ X` followed by that of the glued morphism is the local stalk map of `f i`.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.glueMorphisms`: the morphism `X ⟶ Y` glued from compatible
  morphisms on an open cover.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_glueMorphisms`: the glued morphism restricts to
  `f i` on each `U i`.
* `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_ofRestrict`: morphisms out of `X` are determined
  by their restrictions to an open cover.
* `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms`: unique existence of the glued
  morphism.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 2.2.4 and 10.4.6.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable {X Y : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
    X.restrictHomOfLE inf_le_right ≫ f j)

private abbrev fPsh (i : ι) :
    X.toPresheafedSpace.restrict (U i).isOpenEmbedding ⟶ Y.toPresheafedSpace :=
  (f i).toHom

include hf in
private theorem presheafedSpace_pullback_compat (i j : ι) :
    pullback.fst (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
        (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ fPsh U f i =
      pullback.snd _ _ ≫ fPsh U f j := by
  let ι₁ := X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding
  let ι₂ := X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding
  let ι₁₂ := X.toPresheafedSpace.ofRestrict (U i ⊓ U j).isOpenEmbedding
  let g := pullback.fst ι₁ ι₂ ≫ ι₁
  have hsub : Set.range g.base ⊆ Set.range ι₁₂.base := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨g.base p, ⟨((pullback.fst ι₁ ι₂).base p).2, ?_⟩⟩, rfl⟩
    have hcond : g = pullback.snd ι₁ ι₂ ≫ ι₂ := pullback.condition
    rw [congrArg (fun k ↦ k.base p) hcond]
    exact ((pullback.snd ι₁ ι₂).base p).2
  let l := PresheafedSpace.IsOpenImmersion.lift ι₁₂ g hsub
  have hl₁ : l ≫ X.toPresheafedSpace.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) =
      pullback.fst ι₁ ι₂ := by
    rw [← cancel_mono ι₁, Category.assoc, PresheafedSpace.restrictHomOfLE_ofRestrict]
    exact PresheafedSpace.IsOpenImmersion.lift_fac ι₁₂ g hsub
  have hl₂ : l ≫ X.toPresheafedSpace.restrictHomOfLE (inf_le_right : U i ⊓ U j ≤ U j) =
      pullback.snd ι₁ ι₂ := by
    rw [← cancel_mono ι₂, Category.assoc, PresheafedSpace.restrictHomOfLE_ofRestrict,
      PresheafedSpace.IsOpenImmersion.lift_fac]
    exact pullback.condition
  rw [← hl₁, ← hl₂, Category.assoc, Category.assoc]
  have h := congrArg Hom.toHom (hf i j)
  rw [LocallyRingedSpace.comp_toHom, LocallyRingedSpace.comp_toHom,
    restrictHomOfLE_toHom, restrictHomOfLE_toHom] at h
  exact congrArg (l ≫ ·) h

private noncomputable def gluePsh : X.toPresheafedSpace ⟶ Y.toPresheafedSpace :=
  PresheafedSpace.glueMorphisms X.IsSheaf U hU (fPsh U f)
    (presheafedSpace_pullback_compat U f hf)

private theorem ofRestrict_gluePsh (i : ι) :
    X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫ gluePsh U hU f hf = fPsh U f i :=
  PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU (fPsh U f)
    (presheafedSpace_pullback_compat U f hf) i

private theorem isLocalHom_stalkMap_gluePsh (x : X) :
    IsLocalHom ((gluePsh U hU f hf).stalkMap x).hom := by
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
  let j := X.ofRestrict (U i).isOpenEmbedding
  let y : X.restrict (U i).isOpenEmbedding := ⟨x, hx⟩
  have hcomp_eq : j.toHom ≫ gluePsh U hU f hf = (f i).toHom := ofRestrict_gluePsh U hU f hf i
  have hloc : IsLocalHom ((j.toHom ≫ gluePsh U hU f hf).stalkMap y).hom := by
    rw [PresheafedSpace.stalkMap.congr_hom _ _ hcomp_eq y, CommRingCat.hom_comp]
    have := isLocalHom_of_isIso (eqToHom (hcomp_eq ▸ rfl :
      Y.presheaf.stalk ((j.toHom ≫ gluePsh U hU f hf).base y) =
        Y.presheaf.stalk ((f i).base y)))
    have := (f i).prop y
    exact CommRingCat.isLocalHom_comp _ _
  rw [PresheafedSpace.stalkMap.comp] at hloc
  -- The codomain stalk of `gluePsh` is typed at `(j.toHom ≫ gluePsh ...).base y`, which is
  -- definitionally `x = j.base y`.
  have hloc' : IsLocalHom ((j.toHom.stalkMap y).hom.comp
      ((gluePsh U hU f hf).stalkMap x).hom) := hloc
  exact isLocalHom_of_comp _ (j.toHom.stalkMap y).hom

/-- **Gluing morphisms of locally ringed spaces along an open cover.** Given an open cover
`U : ι → Opens X` with `⨆ i, U i = ⊤` and morphisms `f i : X|_{U i} ⟶ Y` agreeing on every
intersection `U i ⊓ U j`, `glueMorphisms` is the unique morphism `X ⟶ Y` restricting to `f i` on
each `U i`. -/
noncomputable def glueMorphisms : X ⟶ Y where
  toHom := gluePsh U hU f hf
  prop := isLocalHom_stalkMap_gluePsh U hU f hf

/-- The glued morphism restricts to `f i` on each member `U i` of the open cover. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms U hU f hf = f i :=
  Hom.ext' (ofRestrict_gluePsh U hU f hf i)

include hU in
/-- Two morphisms of locally ringed spaces agreeing on every member of an open cover of the source
are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' :=
  Hom.ext' <| PresheafedSpace.hom_ext_of_ofRestrict X.IsSheaf U hU fun i ↦
    congrArg Hom.toHom (h i)

include hU hf in
/-- **Universal property of open-cover morphism gluing** for locally ringed spaces: there is a
unique morphism `X ⟶ Y` restricting to `f i` on each `U i`. -/
theorem existsUnique_glueMorphisms :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf, fun _ hg ↦
    hom_ext_of_ofRestrict U hU fun i ↦ (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩

end AlgebraicGeometry.LocallyRingedSpace
