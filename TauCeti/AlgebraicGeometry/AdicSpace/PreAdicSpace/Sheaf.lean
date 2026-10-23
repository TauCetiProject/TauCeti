/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.MapPresheaf
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# Pre-adic spaces with a sheaf of topological rings

A pre-adic space has a presheaf of complete separated topological rings. The objects whose
presheaf is a sheaf form a full subcategory: their morphisms retain the local and valuative
conditions of pre-adic morphisms. The underlying sheafed space forgets only those extra
conditions. This is the sheaf condition in Wedhorn's category of pre-adic spaces.

Forgetting also the topology on sections gives a sheafed space of commutative rings
(`TauCeti.SheafyPreAdicSpace.forgetToRingSheafedSpace`). Its stalks are those on which the stalk
maps of pre-adic spaces are defined, so it is the setting for arguments about morphisms through
their stalk maps. Both forgetful functors are faithful.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

/-- A pre-adic space is sheafy when its presheaf of complete separated topological rings
satisfies the sheaf condition. The condition concerns the topological-ring-valued presheaf,
not merely its underlying presheaf of sets or rings. -/
@[expose] def PreAdicSpace.isSheafy : ObjectProperty PreAdicSpace.{u} :=
  fun X ↦ X.toPresheafedSpace.presheaf.IsSheaf

/-- Being sheafy is invariant under isomorphism in `𝒱^pre`: an isomorphism `e : X ≅ Y` is a
homeomorphism of the underlying spaces along which `e.hom.c` identifies the structure presheaf of
`Y` with the pushforward of that of `X`, and the pushforward of a sheaf is a sheaf. -/
instance PreAdicSpace.isSheafy.instIsClosedUnderIsomorphisms :
    PreAdicSpace.isSheafy.{u}.IsClosedUnderIsomorphisms where
  of_iso e hX :=
    -- `e.hom.c` is an isomorphism because `e.hom.toHom` is, as the image of `e` under the
    -- forgetful functor, whose `map` is `Hom.toHom` by definition
    have : IsIso (C := PresheafedSpace CompleteSeparatedTopCommRingCat.{u}) e.hom.toHom :=
      inferInstanceAs (IsIso (PreAdicSpace.forgetToPresheafedSpace.map e.hom))
    TopCat.Presheaf.isSheaf_of_iso (asIso e.hom.c).symm
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf e.hom.base hX)

/-- The category of pre-adic spaces with sheaf structure presheaves. It is the full
subcategory of pre-adic spaces cut out by the sheaf condition. -/
abbrev SheafyPreAdicSpace : Type (u + 1) :=
  PreAdicSpace.isSheafy.{u}.FullSubcategory

namespace SheafyPreAdicSpace

/-- Forget the stalk locality and valuations while retaining the sheaf of complete
separated topological rings. -/
noncomputable def toSheafedSpace (X : SheafyPreAdicSpace.{u}) :
    SheafedSpace CompleteSeparatedTopCommRingCat.{u} where
  toPresheafedSpace := X.obj.toPresheafedSpace
  IsSheaf := X.property

@[simp]
theorem toSheafedSpace_toPresheafedSpace (X : SheafyPreAdicSpace.{u}) :
    X.toSheafedSpace.toPresheafedSpace = X.obj.toPresheafedSpace := (rfl)

/-- Forget the valuation and local-ring conditions from sheafy pre-adic spaces, retaining
their structure sheaves as sheaves of complete separated topological rings. -/
noncomputable def forgetToSheafedSpace :
    SheafyPreAdicSpace.{u} ⥤ SheafedSpace CompleteSeparatedTopCommRingCat.{u} where
  obj := toSheafedSpace
  map f := InducedCategory.homMk f.hom.toHom
  map_id X := by apply InducedCategory.hom_ext; rfl
  map_comp f g := by apply InducedCategory.hom_ext; rfl

@[simp]
theorem forgetToSheafedSpace_obj (X : SheafyPreAdicSpace.{u}) :
    forgetToSheafedSpace.obj X = X.toSheafedSpace := (rfl)

@[simp]
theorem forgetToSheafedSpace_map_hom {X Y : SheafyPreAdicSpace.{u}} (f : X ⟶ Y) :
    HEq (forgetToSheafedSpace.map f).hom f.hom.toHom := by
  unfold forgetToSheafedSpace toSheafedSpace
  rfl

/-- A morphism of sheafy pre-adic spaces is determined by its morphism of underlying
sheafed spaces. -/
instance : forgetToSheafedSpace.{u}.Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply PreAdicSpace.Hom.ext
    exact congrArg InducedCategory.Hom.hom h

/-- Forget the topology on sections, the stalk locality and the valuations of sheafy pre-adic
spaces, retaining their structure sheaves as sheaves of commutative rings. The structure presheaf
of rings is a sheaf because forgetting the topology preserves limits. Its stalks are those of
`PreAdicSpace.toRingPresheafedSpace`, on which the stalk maps of pre-adic spaces are defined. -/
-- The body is exposed, as the category structure of pre-adic spaces is: the points, continuous
-- maps and stalk maps of the image of a morphism must unfold to those of the morphism.
@[expose] noncomputable def forgetToRingSheafedSpace :
    SheafyPreAdicSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X :=
    { toPresheafedSpace := X.obj.toRingPresheafedSpace
      IsSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.property }
  map f := InducedCategory.homMk (PreAdicSpace.toRingPresheafedSpaceHom f.hom.toHom)
  map_id X := by
    apply InducedCategory.hom_ext
    exact CategoryTheory.Functor.map_id (TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).mapPresheaf X.obj.toPresheafedSpace
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact Functor.map_comp (TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).mapPresheaf f.hom.toHom g.hom.toHom

/-- The underlying presheafed space of rings of the image of `X` is
`PreAdicSpace.toRingPresheafedSpace`. -/
@[simp]
theorem forgetToRingSheafedSpace_obj_toPresheafedSpace (X : SheafyPreAdicSpace.{u}) :
    (forgetToRingSheafedSpace.obj X).toPresheafedSpace = X.obj.toRingPresheafedSpace := (rfl)

/-- The underlying morphism of presheafed spaces of rings of the image of `f` is
`PreAdicSpace.toRingPresheafedSpaceHom`. -/
@[simp]
theorem forgetToRingSheafedSpace_map_hom {X Y : SheafyPreAdicSpace.{u}} (f : X ⟶ Y) :
    (forgetToRingSheafedSpace.map f).hom = PreAdicSpace.toRingPresheafedSpaceHom f.hom.toHom :=
  (rfl)

/-- A morphism of sheafy pre-adic spaces is determined by its morphism of underlying sheafed
spaces of rings, since a continuous ring homomorphism is determined by its underlying ring
homomorphism. -/
instance : forgetToRingSheafedSpace.{u}.Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply PreAdicSpace.Hom.ext
    have h' := congrArg InducedCategory.Hom.hom h
    rw [forgetToRingSheafedSpace_map_hom, forgetToRingSheafedSpace_map_hom] at h'
    exact Functor.map_injective (TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).mapPresheaf h'

end SheafyPreAdicSpace

end TauCeti

end
