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

For opens `V ≤ U` of `X`, the opens of `V` can be viewed in the subspace `U` in two ways: by
direct image along the inclusion of `V` into `U`, or through the open `V` of `U`, which is
homeomorphic to `V`. The two descriptions agree, as do the resulting image opens in `X`.

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
* `TopologicalSpace.Opens.inclusionSites`, `TopologicalSpace.Opens.inclusionSitesCompIso`: for
  `V ≤ U`, the opens of `V` viewed in `U`, and the identification of their images in `X`;
  `TopologicalSpace.Opens.coe_inclusionSites_obj` and
  `TopologicalSpace.Opens.mem_inclusionSites_obj` describe the carrier in `U` as the image along
  `Set.inclusion`.
* `TopologicalSpace.Opens.relativeOpen`, `TopologicalSpace.Opens.relativeOpenIso`,
  `TopologicalSpace.Opens.relativeSites`: the open `V` of the subspace `U`, its homeomorphism
  with `V`, and the induced equivalence of opens.
* `TopologicalSpace.Opens.relativeRestrictionSitesIso`,
  `TopologicalSpace.Opens.nestedOpen_image_eq`: the two ways of viewing an open of `V` in `U`,
  and in `X`, agree.
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

end TopologicalSpace.Opens

/-! ### Nested open subsets -/

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} {U V : Opens X}

/-- For `V ≤ U`, the opens of `V` viewed as opens of the subspace `U`, by direct image along the
inclusion `V → U`. -/
@[expose]
def inclusionSites (h : V ≤ U) : Opens V ⥤ Opens U :=
  Topology.IsOpenEmbedding.functor (X := TopCat.of V) (Y := TopCat.of U)
    (f := (Opens.toTopCat X).map (homOfLE h)) (isOpenEmbedding_of_le h)

/-- The open of `U` underlying an open `D` of `V` is the image of `D` along the inclusion
`V → U`. -/
@[simp]
lemma coe_inclusionSites_obj (h : V ≤ U) (D : Opens V) :
    ((inclusionSites h).obj D : Set U) = Set.inclusion h '' D :=
  rfl

/-- A point of `U` lies in the open of `U` underlying an open `D` of `V` exactly when it is the
inclusion of a point of `D`. -/
lemma mem_inclusionSites_obj (h : V ≤ U) (D : Opens V) (x : U) :
    x ∈ (inclusionSites h).obj D ↔ ∃ y ∈ D, Set.inclusion h y = x :=
  Iff.rfl

/-- Taking an open of `V` to `U` and then to `X` is taking it to `X` directly. -/
def inclusionSitesCompIso (h : V ≤ U) :
    inclusionSites h ⋙ U.isOpenEmbedding.functor ≅ V.isOpenEmbedding.functor :=
  NatIso.ofComponents (fun T ↦ eqToIso (by
    apply Opens.ext
    -- The opens functor of `U` has source `Opens ((toTopCat X).obj U)`, so `rw` cannot see the
    -- composite; state both sides as direct images along the subtype values.
    change Subtype.val '' ((inclusionSites h).obj T : Set U) = Subtype.val '' (T : Set V)
    rw [coe_inclusionSites_obj, ← Set.image_comp]
    rfl)) (by intro T T' f; exact Subsingleton.elim _ _)

/-- The open V viewed as an open of the subspace U. -/
abbrev relativeOpen (_h : V ≤ U) : Opens U := (Opens.map U.inclusion').obj V
/-- The relative open in U is canonically the same topological space as V. -/
def relativeHomeomorph (h : V ≤ U) : (relativeOpen h) ≃ₜ V where
  toFun w := ⟨w.val.val, w.property⟩
  invFun v := ⟨⟨v.val, h v.property⟩, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
/-- The relative-open homeomorphism forgets the intermediate subtype. -/
@[simp]
lemma relativeHomeomorph_apply (h : V ≤ U) (w : relativeOpen h) :
    relativeHomeomorph h w = ⟨w.val.val, w.property⟩ := by
  rfl

/-- Its inverse inserts the membership proof in the intermediate open. -/
@[simp]
lemma relativeHomeomorph_symm_apply (h : V ≤ U) (v : V) :
    (relativeHomeomorph h).symm v = ⟨⟨v.val, h v.property⟩, v.property⟩ := by
  rfl

/-- The canonical isomorphism from the relative open to the direct open subspace. -/
def relativeOpenIso (h : V ≤ U) :
    TopCat.of (relativeOpen h) ≅ TopCat.of V :=
  @TopCat.isoOfHomeo (TopCat.of (relativeOpen h)) (TopCat.of V) (relativeHomeomorph h)
/-- The relative-open identification forgets the intermediate subtype. -/
@[simp]
lemma relativeOpenIso_hom_apply (h : V ≤ U) (w : relativeOpen h) :
    (relativeOpenIso h).hom w = ⟨w.val.val, w.property⟩ := by
  rfl

/-- The inverse identification inserts the proof that the point belongs to `U`. -/
@[simp]
lemma relativeOpenIso_inv_apply (h : V ≤ U) (v : V) :
    (relativeOpenIso h).inv v = ⟨⟨v.val, h v.property⟩, v.property⟩ := by
  rfl

/-- The inverse image open is tested on the same underlying point of `V`. -/
@[simp]
lemma mem_map_relativeOpenIso_hom_obj (h : V ≤ U) (D : Opens V) (w : relativeOpen h) :
    w ∈ (Opens.map (relativeOpenIso h).hom).obj D ↔ (⟨w.val.val, w.property⟩ : V) ∈ D :=
  Iff.rfl

/-- The site equivalence induced by the relative-open homeomorphism. -/
abbrev relativeSites (h : V ≤ U) : Opens (relativeOpen h) ≌ Opens V :=
  (Opens.mapMapIso (relativeOpenIso h)).symm

/-- The direct-image opens functor for the relative open in the intermediate subspace. -/
abbrev relativeInclusionSites (h : V ≤ U) : Opens (relativeOpen h) ⥤ Opens U :=
  @Topology.IsOpenEmbedding.functor (TopCat.of (relativeOpen h)) (TopCat.of U)
    (Opens.inclusion' (X := TopCat.of U) (relativeOpen h))
    (Opens.isOpenEmbedding (X := TopCat.of U) (relativeOpen h))

/-- Pulling an open of `V` back to the relative open and pushing it into `U` is viewing it in `U`
directly. -/
def relativeRestrictionSitesIso (h : V ≤ U) :
    Opens.map (relativeOpenIso h).hom ⋙ (relativeInclusionSites h) ≅
      inclusionSites h :=
  NatIso.ofComponents (fun D ↦ eqToIso (by
    apply Opens.ext
    let f : relativeOpen h → V := (relativeHomeomorph h)
    let g : V → U := fun v ↦ ⟨v.val, h v.property⟩
    -- `Opens.map` is direct image; the relative homeomorphism supplies its preimage carrier.
    change Subtype.val '' (f ⁻¹' (D : Set V)) = g '' (D : Set V)
    calc
      Subtype.val '' (f ⁻¹' (D : Set V)) = g '' (f '' (f ⁻¹' (D : Set V))) := by
        rw [← Set.image_comp]
        rfl
      _ = g '' (D : Set V) :=
        congrArg (g '' ·) (Set.image_preimage_eq _ (relativeHomeomorph h).surjective)))
    (by intro D D' f; exact Subsingleton.elim _ _)

private def totalNestedSitesIso (h : V ≤ U) :
    (relativeSites h).inverse ⋙ relativeInclusionSites h ⋙ U.isOpenEmbedding.functor ≅
      V.isOpenEmbedding.functor :=
  Functor.isoWhiskerRight (relativeRestrictionSitesIso h) U.isOpenEmbedding.functor ≪≫
    inclusionSitesCompIso h
/-- The composed image open in X equals the direct image of the open in V. -/
lemma nestedOpen_image_eq (h : V ≤ U) (D : Opens V) :
    U.isOpenEmbedding.functor.obj
      ((relativeInclusionSites h).obj ((relativeSites h).inverse.obj D)) =
      V.isOpenEmbedding.functor.obj D := by
  exact le_antisymm (leOfHom ((totalNestedSitesIso h).hom.app D))
    (leOfHom ((totalNestedSitesIso h).inv.app D))

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
