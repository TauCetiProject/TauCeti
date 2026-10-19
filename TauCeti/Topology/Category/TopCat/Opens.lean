/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Preimages and images of opens along isomorphisms and inclusions

For an isomorphism `f : X ≅ Y` in `TopCat`, taking preimages along `f.hom` and along `f.inv` are
the two directions of the order isomorphism `Homeomorph.opensCongr` of the homeomorphism
`TopCat.homeoOfIso f`, so the two round trips are the identity on opens. Mathlib records this as
the equivalence of categories `TopologicalSpace.Opens.mapMapIso`; this file records the two
round trips as equalities of opens, the form met when an open of `Y` is compared with the preimage
of its preimage.

For opens `V ≤ W` of `X`, an open `Q` of `W` pulled back to `V` along the inclusion and pushed
forward to `X` lies in the image of `Q` in `X`.

## Main results

* `TopologicalSpace.Opens.map_hom_obj_map_inv_obj`,
  `TopologicalSpace.Opens.map_inv_obj_map_hom_obj`: the preimage along `f.hom` of the preimage
  along `f.inv` of an open is that open, and the other way round.
* `TopologicalSpace.Opens.functor_obj_map_homOfLE_obj_le`: for opens `V ≤ W`, the image in `X`
  of the preimage in `V` of an open of `W` lies in the image of that open.
-/

public section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}} (f : X ≅ Y)

/-- The preimage along `f.hom` of the preimage along `f.inv` of an open `U` of `X` is `U`. -/
@[simp]
theorem map_hom_obj_map_inv_obj (U : Opens X) :
    (Opens.map f.hom).obj ((Opens.map f.inv).obj U) = U :=
  (TopCat.homeoOfIso f).opensCongr.symm_apply_apply U

/-- The preimage along `f.inv` of the preimage along `f.hom` of an open `U` of `Y` is `U`. -/
@[simp]
theorem map_inv_obj_map_hom_obj (U : Opens Y) :
    (Opens.map f.inv).obj ((Opens.map f.hom).obj U) = U :=
  (TopCat.homeoOfIso f).opensCongr.apply_symm_apply U

/-- For opens `V ≤ W` of `X` and an open `Q` of `W`, the image in `X` of the preimage of `Q` in `V`
lies in the image of `Q` in `X`. -/
theorem functor_obj_map_homOfLE_obj_le {V W : Opens X} (h : V ≤ W) (Q : Opens W) :
    V.isOpenEmbedding.functor.obj ((Opens.map ((Opens.toTopCat X).map (homOfLE h))).obj Q) ≤
      W.isOpenEmbedding.functor.obj Q := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨_, hx, rfl⟩

end TopologicalSpace.Opens

end
