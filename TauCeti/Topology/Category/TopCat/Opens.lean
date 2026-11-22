/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.Compacts

/-!
# Preimages and images of opens along isomorphisms and inclusions

For an isomorphism `f : X ≅ Y` in `TopCat`, taking preimages along `f.hom` and along `f.inv` are
the two directions of the order isomorphism `Homeomorph.opensCongr` of the homeomorphism
`TopCat.homeoOfIso f`, so the two round trips are the identity on opens. Mathlib records this as
the equivalence of categories `TopologicalSpace.Opens.mapMapIso`; this file records the two
round trips as equalities of opens, the form met when an open of `Y` is compared with the preimage
of its preimage.

For opens `V ≤ W` of `X`, an open `Q` of `W` pulled back to `V` along the inclusion and pushed
forward to `X` lies in the image of `Q` in `X`. The inclusion of `V` into `W` is an open embedding,
and an open subset of a Hausdorff space is Hausdorff. A compact subset of `X` lying in an open set
`U` is the image of a compact subset of `U`. For an injective open map `f`, the point `f y` lies in
the image of an open `V` exactly when `y` lies in `V`.

## Main results

* `TopologicalSpace.Opens.map_hom_obj_map_inv_obj`,
  `TopologicalSpace.Opens.map_inv_obj_map_hom_obj`: the preimage along `f.hom` of the preimage
  along `f.inv` of an open is that open, and the other way round.
* `TopologicalSpace.Opens.functor_obj_map_homOfLE_obj_le`: for opens `V ≤ W`, the image in `X`
  of the preimage in `V` of an open of `W` lies in the image of that open.
* `TopologicalSpace.Opens.isOpenEmbedding_toTopCat_map`: the inclusion of `V` into `W` is an open
  embedding.
* `TopologicalSpace.Opens.exists_compacts_map_inclusion'_eq`: a compact subset of `X` lying in an
  open set `U` is the image of a compact subset of `U` under its inclusion.
* `TopologicalSpace.Opens.resLE` and `TopologicalSpace.Opens.mapCompResLEIso`: the continuous map
  between open subspaces `U ≤ f ⁻¹' V` induced by `f : X ⟶ Y`, its compatibility with
  `Opens.inclusion'` (`resLE_comp_inclusion'`, `inclusion'_resLE_apply`, `functor_map_resLE_le`),
  and the induced isomorphism of preimage functors.
* `IsOpenMap.apply_mem_functor_obj_iff`: for an injective open map `f`, the point `f y` lies in the
  image of an open `V` exactly when `y` lies in `V`.
-/

public section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}} (f : X ≅ Y)

/-- The preimage along `f.hom` of the preimage along `f.inv` of an open `U` of `X` is `U`. -/
@[simp]
theorem map_hom_obj_map_inv_obj (U : Opens X) :
    (Opens.map f.hom).obj ((Opens.map f.inv).obj U) = U := by
  rw [← map_comp_obj, f.hom_inv_id, map_id_obj]

/-- The preimage along `f.inv` of the preimage along `f.hom` of an open `U` of `Y` is `U`. -/
@[simp]
theorem map_inv_obj_map_hom_obj (U : Opens Y) :
    (Opens.map f.inv).obj ((Opens.map f.hom).obj U) = U := by
  rw [← map_comp_obj, f.inv_hom_id, map_id_obj]

/-- For opens `V ≤ W` of `X` and an open `Q` of `W`, the image in `X` of the preimage of `Q` in `V`
lies in the image of `Q` in `X`. -/
theorem functor_obj_map_homOfLE_obj_le {V W : Opens X} (h : V ≤ W) (Q : Opens W) :
    V.isOpenEmbedding.functor.obj ((Opens.map ((Opens.toTopCat X).map (homOfLE h))).obj Q) ≤
      W.isOpenEmbedding.functor.obj Q := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨_, hx, rfl⟩

/-- The inclusion of an open set `V` into a larger open set `W` is an open embedding. -/
lemma isOpenEmbedding_toTopCat_map {V W : Opens X} (h : V ⟶ W) :
    Topology.IsOpenEmbedding ((toTopCat X).map h) :=
  isOpenEmbedding_of_le h.le

/-- The inclusion of `V` into `W` followed by the inclusion of `W` is the inclusion of `V`. -/
@[reassoc (attr := simp)]
lemma toTopCat_map_comp_inclusion' {V W : Opens X} (h : V ⟶ W) :
    (toTopCat X).map h ≫ inclusion' W = inclusion' V :=
  rfl

/-- A compact subset of `X` lying in an open set `U` is the image of a compact subset of `U`. -/
lemma exists_compacts_map_inclusion'_eq {U : Opens X} {K : Compacts X} (hK : (K : Set X) ⊆ U) :
    ∃ K' : Compacts ((toTopCat X).obj U),
      (K'.map (inclusion' U) (map_continuous _) : Set X) = K := by
  obtain ⟨K', hK'⟩ := (Compacts.range_map U.isOpenEmbedding.isInducing).ge
    (by rwa [set_range_inclusion'])
  exact ⟨K', congrArg SetLike.coe hK'⟩

/-- An open subset of a Hausdorff space is Hausdorff. -/
instance t2Space_toTopCat_obj [T2Space X] (V : Opens X) : T2Space ((toTopCat X).obj V) :=
  inferInstanceAs (T2Space V)

/-- The continuous map `(Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V` between open
subspaces induced by `f : X ⟶ Y` when `U ≤ (Opens.map f).obj V`. -/
def resLE (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨f x.val, e x.property⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- `Opens.resLE` commutes with the open inclusions `Opens.inclusion'` into `X` and `Y`. -/
@[reassoc (attr := simp)]
theorem resLE_comp_inclusion' (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    Opens.resLE f V U e ≫ V.inclusion' = U.inclusion' ≫ f := by
  ext x
  rfl

/-- Underlying point value of `Opens.resLE`. -/
@[simp]
theorem inclusion'_resLE_apply (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) (x : (Opens.toTopCat X).obj U) :
    V.inclusion' (Opens.resLE f V U e x) = f (U.inclusion' x) :=
  (rfl)

/-- For an open `W` of `(Opens.toTopCat Y).obj V` and `e : U ≤ (Opens.map f).obj V`, the image in
`X` of the preimage of `W` under `Opens.resLE f V U e` is contained in the preimage under `f` of
the image of `W` in `Y`. -/
theorem functor_map_resLE_le (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) (W : Opens ((Opens.toTopCat Y).obj V)) :
    U.isOpenEmbedding.functor.obj ((Opens.map (Opens.resLE f V U e)).obj W) ≤
      (Opens.map f).obj (V.isOpenEmbedding.functor.obj W) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨⟨f u.val, e u.property⟩, hu, rfl⟩

/-- Natural isomorphism between composed open-preimage functors witnessing the commutative square
`resLE_comp_inclusion'`. -/
def mapCompResLEIso (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    Opens.map f ⋙ Opens.map U.inclusion' ≅
      Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e) :=
  Opens.mapIso (U.inclusion' ≫ f) (Opens.resLE f V U e ≫ V.inclusion')
    (Opens.resLE_comp_inclusion' f V U e).symm

end TopologicalSpace.Opens

namespace IsOpenMap

/-- For an injective open map `f`, the point `f y` lies in the image of an open set `V` exactly when
`y` lies in `V`. -/
theorem apply_mem_functor_obj_iff {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenMap f)
    (hf' : Function.Injective f) {y : Y} {V : TopologicalSpace.Opens Y} :
    f y ∈ hf.functor.obj V ↔ y ∈ V :=
  hf'.mem_set_image

end IsOpenMap

end
