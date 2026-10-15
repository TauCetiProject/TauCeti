/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace

/-!
# Changing the coefficients of presheafed spaces along a faithful functor

A functor `F : C ⥤ D` induces the functor `F.mapPresheaf : PresheafedSpace C ⥤ PresheafedSpace D`,
which keeps the underlying spaces and continuous maps and composes the presheaves and the maps of
sections with `F`. When `F` is faithful, so is `F.mapPresheaf`: a morphism of presheafed spaces is
its continuous map together with its maps of sections, and `F` loses no information about the
latter. For instance, forgetting the topology on the sections of a presheaf of topological rings is
faithful, so morphisms of such presheafed spaces are determined by the underlying morphisms of
presheafed spaces of rings.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.PresheafedSpace

variable {C D : Type*} [Category* C] [Category* D]

/-- Changing the coefficients of presheafed spaces along a faithful functor is faithful. -/
instance faithful_mapPresheaf (F : C ⥤ D) [F.Faithful] : F.mapPresheaf.Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨fb, fc⟩ := f
    obtain ⟨gb, gc⟩ := g
    -- `F.mapPresheaf.map f` is `f.base` together with `f.c` whiskered by `F`
    have h' : (⟨fb, Functor.whiskerRight fc F⟩ :
        Hom (F.mapPresheaf.obj X) (F.mapPresheaf.obj Y)) = ⟨gb, Functor.whiskerRight gc F⟩ := h
    obtain ⟨rfl, hc⟩ := Hom.mk.inj h'
    congr
    ext U
    exact F.map_injective (NatTrans.congr_app (eq_of_heq hc) (Opposite.op U))

end AlgebraicGeometry.PresheafedSpace
