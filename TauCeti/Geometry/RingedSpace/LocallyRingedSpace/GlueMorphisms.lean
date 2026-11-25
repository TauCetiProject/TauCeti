/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.GlueMorphisms

import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic

/-!
# Gluing morphisms of locally ringed spaces along open covers

For locally ringed spaces `X`, `Y` and an open cover `U : ι → Opens X` (`⨆ i, U i = ⊤`), a family
`f i : X|_{U i} ⟶ Y` agreeing on intersections `U i ⊓ U j` glues via
`AlgebraicGeometry.PresheafedSpace.glueMorphisms` to a unique morphism `glueMorphisms : X ⟶ Y`
restricting to `f i` on each `U i` (`ofRestrict_glueMorphisms`, `hom_ext_of_ofRestrict`,
`existsUnique_glueMorphisms`; EGA I, Ch. I, 2.2.4 and 10.4.6), with stalk locality checked on the
cover.
-/

public section
open CategoryTheory Limits TopologicalSpace
namespace AlgebraicGeometry.LocallyRingedSpace
universe u w
variable {X Y : LocallyRingedSpace.{u}} {ι : Type w} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
    X.restrictHomOfLE inf_le_right ≫ f j)

include hf in
/-- Transporting overlap compatibility of restricted locally ringed-space morphisms on `U i ⊓ U j`
to the presheafed-space pullback of `ofRestrict (U i)` and `ofRestrict (U j)`. -/
theorem pullback_toHom_of_restrictHomOfLE (i j : ι) :
    pullback.fst (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
        (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ (f i).toHom =
      pullback.snd (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
        (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ (f j).toHom :=
  (X.toPresheafedSpace.pullback_comp_iff_restrictHomOfLE (f i).toHom (f j).toHom).mpr <| by
    have h := congrArg Hom.toHom (hf i j)
    rw [comp_toHom, comp_toHom, restrictHomOfLE_toHom, restrictHomOfLE_toHom] at h
    exact h

private noncomputable def gluePsh : X.toPresheafedSpace ⟶ Y.toPresheafedSpace :=
  PresheafedSpace.glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
    (pullback_toHom_of_restrictHomOfLE U f hf)

private theorem isLocalHom_stalkMap_gluePsh (x : X) :
    IsLocalHom ((gluePsh U hU f hf).stalkMap x).hom := by
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
  exact isLocalHom_stalkMap_of_comp_eq (X.ofRestrict (U i).isOpenEmbedding) (gluePsh U hU f hf)
    (f i) (PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU _ _ i)
    (rfl : (X.ofRestrict (U i).isOpenEmbedding).base ⟨x, hx⟩ = x)

/-- **Gluing morphisms of locally ringed spaces along an open cover.** Given an open cover
`U : ι → Opens X` with `⨆ i, U i = ⊤` and morphisms `f i : X|_{U i} ⟶ Y` agreeing on every
intersection `U i ⊓ U j`, `glueMorphisms` is the unique morphism `X ⟶ Y` restricting to `f i` on
each `U i`. -/
noncomputable def glueMorphisms : X ⟶ Y :=
  ⟨gluePsh U hU f hf, isLocalHom_stalkMap_gluePsh U hU f hf⟩

/-- The underlying morphism of presheafed spaces of `glueMorphisms` is
`PresheafedSpace.glueMorphisms`. -/
@[simp] theorem glueMorphisms_toHom :
    (glueMorphisms U hU f hf).toHom =
      PresheafedSpace.glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
        (pullback_toHom_of_restrictHomOfLE U f hf) := (rfl)

/-- The glued morphism restricts to `f i` on each member `U i` of the open cover. -/
@[reassoc (attr := simp)] theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms U hU f hf = f i :=
  Hom.ext' (PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU _ _ i)

include hU in
/-- Two morphisms of locally ringed spaces agreeing on every member of an open cover of the source
are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' :=
  Hom.ext' <| PresheafedSpace.hom_ext_of_ofRestrict X.IsSheaf U hU fun i ↦ congrArg Hom.toHom (h i)

include hU hf in
/-- **Universal property of open-cover morphism gluing** for locally ringed spaces: there is a
unique morphism `X ⟶ Y` restricting to `f i` on each `U i`. -/
theorem existsUnique_glueMorphisms :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf, fun _ hg ↦
    hom_ext_of_ofRestrict U hU fun i ↦ (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩
end AlgebraicGeometry.LocallyRingedSpace
