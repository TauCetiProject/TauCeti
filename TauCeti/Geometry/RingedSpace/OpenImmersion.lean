/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Topology.Sheaves.Functors

/-!
# Open immersions of presheafed and locally ringed spaces

Applying a functor `F : C ⥤ D` to the sections of a presheafed space (`Functor.mapPresheaf`)
preserves open immersions: the underlying continuous map is unchanged, and the components of the
new map of presheaves are the images under `F` of the old ones. For instance, forgetting the
topology on a presheaf of topological rings turns open immersions into open immersions of
presheafed spaces of rings, whose stalk maps are isomorphisms
(`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`).

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mapPresheaf_map`: the image of an open
  immersion under `F.mapPresheaf` is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.isIso_stalkMap_of_isOpenImmersion_comp`: if `f ≫ g` is an
  open immersion and the stalk map of `f` at `x` is invertible, so is the stalk map of `g` at
  `f x`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isSheaf_iff_of_range_eq`: the sources of two
  open immersions with the same range satisfy the sheaf condition together.
* `AlgebraicGeometry.LocallyRingedSpace.range_iso_inv_comp`: precomposing a morphism of locally
  ringed spaces with an isomorphism does not change its image.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isOpenImmersion_lift`: lifting an open
  immersion through an open immersion gives an open immersion.
-/

public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.PresheafedSpace

namespace IsOpenImmersion

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- **Applying a functor to the sections preserves open immersions** of presheafed spaces: the
components of the whiskered presheaf map are the images of the components of `f.c`. -/
theorem mapPresheaf_map (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] :
    PresheafedSpace.IsOpenImmersion (F.mapPresheaf.map f) where
  base_open := H.base_open
  c_iso U :=
    have := H.c_iso U
    Functor.map_isIso F (f.c.app (Opposite.op (H.base_open.functor.obj U)))

/-- **The sheaf condition depends only on the range of an open immersion.** If two open immersions
`f : X ⟶ Z` and `g : Y ⟶ Z` have the same range, then the presheaf of `X` is a sheaf exactly when
that of `Y` is: `isoOfRangeEq` identifies `X` with `Y`. -/
theorem isSheaf_iff_of_range_eq {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [IsOpenImmersion f]
    (g : Y ⟶ Z) [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) :
    X.presheaf.IsSheaf ↔ Y.presheaf.IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_of_iso_pushforward ((forget C).mapIso (isoOfRangeEq f g e))
    (sheafIsoOfIso (isoOfRangeEq f g e))).symm

end IsOpenImmersion

/-- **Cancelling an invertible stalk map against an open immersion.** If `f ≫ g` is an open
immersion of presheafed spaces and the stalk map of `f` at `x` is an isomorphism, then so is the
stalk map of `g` at `f x`: the stalk map of `f ≫ g` at `x`, an isomorphism, is that of `g`
followed by that of `f`. -/
theorem isIso_stalkMap_of_isOpenImmersion_comp {C : Type u} [Category.{v} C]
    [Limits.HasColimits C] {X Y Z : PresheafedSpace.{_, _, v} C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [PresheafedSpace.IsOpenImmersion (f ≫ g)] (x : X) [IsIso (f.stalkMap x)] :
    IsIso (g.stalkMap (f.base x)) := by
  have := PresheafedSpace.IsOpenImmersion.stalk_iso (f ≫ g) x
  rw [PresheafedSpace.stalkMap.comp] at this
  exact (isIso_comp_right_iff _ (f.stalkMap x)).mp this

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Precomposing a morphism of locally ringed spaces with an isomorphism preserves its image. -/
theorem range_iso_inv_comp {X Y Z : LocallyRingedSpace.{u}} (e : X ≅ Y) (g : X ⟶ Z) :
    Set.range (e.inv ≫ g).base = Set.range g.base := by
  rw [comp_base, TopCat.coe_comp,
    (Function.LeftInverse.surjective (iso_hom_base_inv_base_apply e)).range_comp]

/-- The lift of an open immersion through an open immersion is an open immersion. -/
instance IsOpenImmersion.isOpenImmersion_lift {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (H : Set.range g.base ⊆ Set.range f.base) : IsOpenImmersion (IsOpenImmersion.lift f g H) := by
  have := IsOpenImmersion.pullback_snd_isIso_of_range_subset f g H
  dsimp only [IsOpenImmersion.lift]
  infer_instance

end AlgebraicGeometry.LocallyRingedSpace
