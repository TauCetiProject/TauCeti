/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Open immersions of presheafed spaces under a change of coefficients

Applying a functor `F : C ⥤ D` to the sections of a presheafed space (`Functor.mapPresheaf`)
preserves open immersions: the underlying continuous map is unchanged, and the components of the
new map of presheaves are the images under `F` of the old ones. For instance, forgetting the
topology on a presheaf of topological rings turns open immersions into open immersions of
presheafed spaces of rings, whose stalk maps are isomorphisms
(`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`).

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mapPresheaf_map`: the image of an open
  immersion under `F.mapPresheaf` is an open immersion.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

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

end AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
