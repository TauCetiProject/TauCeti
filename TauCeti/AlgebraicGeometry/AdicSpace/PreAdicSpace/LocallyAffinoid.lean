/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Restrict
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Sheaf
public import TauCeti.Topology.Sheaves.Adapted

/-!
# Pre-adic spaces: locally affinoid objects of `𝒱^pre`

An open subset `U` of an object `X` of `𝒱^pre` is an *open affinoid subspace* if `X` restricted
to `U` is an affinoid pre-adic space. `X` is *locally affinoid* if its open affinoid subspaces
cover it. Wedhorn's pre-adic spaces are the locally affinoid objects whose structure presheaf is
adapted to the open affinoid subspaces: on every open `V`, the presheaf is the limit of its values
on the open affinoid subspaces contained in `V`. Their full subcategory of `𝒱^pre` is Wedhorn's
category `(PreAd)`, here `TauCeti.WedhornPreAdicSpace`.

Adaptedness is what lets the sheaf condition on an object of `𝒱^pre` be checked on its open
affinoid subspaces alone, once those form a basis of the topology: an object whose open affinoid
subspaces form a basis, whose presheaf is adapted to them and is a sheaf on them, for the topology
restricted to them, is sheafy. That the open affinoid subspaces of a locally affinoid object form a
basis is not proved here, so the basis is a hypothesis of
`isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`. Applied to a pre-adic space, whose presheaf is
adapted by definition, this is the mechanism behind Wedhorn's Remark 8.27, which produces adic
spaces from pre-adic spaces covered by sheafy affinoids.

Affinoid pre-adic spaces are locally affinoid, and being locally affinoid is invariant under
isomorphism in `𝒱^pre`, since an isomorphism carries the restriction to an open isomorphically
onto the restriction to its image (`TauCeti.PreAdicSpace.restrictIso`).

## Main definitions

* `TauCeti.PreAdicSpace.affinoidOpens`: the open affinoid subspaces of an object of `𝒱^pre`.
* `TauCeti.PreAdicSpace.isLocallyAffinoid`: the locally affinoid objects of `𝒱^pre`.
* `TauCeti.PreAdicSpace.isPreAdic`: Wedhorn's pre-adic spaces.
* `TauCeti.WedhornPreAdicSpace`: Wedhorn's category `(PreAd)`, the full subcategory of `𝒱^pre` of
  pre-adic spaces.

## Main results

* `TauCeti.PreAdicSpace.isLocallyAffinoid_of_isAffinoid`: affinoid pre-adic spaces are locally
  affinoid.
* `TauCeti.PreAdicSpace.isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`: an object of `𝒱^pre`
  whose open affinoid subspaces form a basis and whose presheaf is adapted to them and a sheaf on
  them is sheafy.
* `TauCeti.PreAdicSpace.isLocallyAffinoid.instIsClosedUnderIsomorphisms`,
  `TauCeti.PreAdicSpace.isPreAdic.instIsClosedUnderIsomorphisms`: being locally affinoid, and being
  pre-adic, are invariant under isomorphism.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.9, Remark and
  Definition 8.10, and Remark 8.27.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace

/-! ### Open affinoid subspaces and locally affinoid objects -/

variable (X : PreAdicSpace.{u})

/-- The open affinoid subspaces of an object `X` of `𝒱^pre`: the opens `U` such that `X`
restricted to `U` is an affinoid pre-adic space. -/
@[expose] def affinoidOpens : Set (Opens X) :=
  {U | isAffinoid (X.restrict U.isOpenEmbedding)}

/-- The whole space is an open affinoid subspace exactly when `X` is affinoid. -/
@[simp]
theorem top_mem_affinoidOpens_iff : ⊤ ∈ X.affinoidOpens ↔ isAffinoid X :=
  ObjectProperty.prop_iff_of_iso isAffinoid X.restrictTopIso

variable {X} in
/-- An open `U` of `Y` is an open affinoid subspace of `Y` exactly when its preimage under an
isomorphism `e : X ≅ Y` is an open affinoid subspace of `X`: `e` carries `X` restricted to
`e⁻¹(U)` isomorphically onto `Y` restricted to `U`. -/
@[simp]
theorem map_hom_base_mem_affinoidOpens_iff {Y : PreAdicSpace.{u}} (e : X ≅ Y) {U : Opens Y} :
    (Opens.map e.hom.base).obj U ∈ X.affinoidOpens ↔ U ∈ Y.affinoidOpens := by
  -- `restrictIso e` lands in `Y` restricted to the image of `e⁻¹(U)` under `e`, which is `U`
  have key := Opens.map_inv_obj_map_hom_obj (forgetToTop.mapIso e) U
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  refine ⟨fun hU ↦ key ▸ ObjectProperty.prop_of_iso isAffinoid (restrictIso e _) hU, fun hU ↦ ?_⟩
  -- `e.symm.inv` is `e.hom`
  exact ObjectProperty.prop_of_iso isAffinoid (restrictIso e.symm U) hU

/-- An object of `𝒱^pre` is locally affinoid when its open affinoid subspaces cover it. -/
@[expose] def isLocallyAffinoid : ObjectProperty PreAdicSpace.{u} :=
  fun X ↦ ∀ x : X, ∃ U ∈ X.affinoidOpens, x ∈ U

/-- `X` is locally affinoid exactly when the union of its open affinoid subspaces is `X`. -/
theorem isLocallyAffinoid_iff_sSup_eq_top : isLocallyAffinoid X ↔ sSup X.affinoidOpens = ⊤ := by
  refine ⟨fun h ↦ SetLike.ext fun x ↦ ?_, fun h x ↦ Opens.mem_sSup.mp ?_⟩
  · simpa [Opens.mem_sSup] using h x
  · rw [h]
    exact Opens.mem_top x

/-- Affinoid pre-adic spaces are locally affinoid. -/
theorem isLocallyAffinoid_of_isAffinoid {X : PreAdicSpace.{u}} (hX : isAffinoid X) :
    isLocallyAffinoid X :=
  fun _ ↦ ⟨⊤, (top_mem_affinoidOpens_iff X).mpr hX, trivial⟩

/-- Being locally affinoid is invariant under isomorphism in `𝒱^pre`. -/
instance isLocallyAffinoid.instIsClosedUnderIsomorphisms :
    isLocallyAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e hX y := by
    obtain ⟨U, hU, hx⟩ := hX (e.inv.base y)
    -- `U` is the preimage under `e.symm` of its image `e(U)`, and `e.symm.hom` is `e.inv`
    exact ⟨_, (map_hom_base_mem_affinoidOpens_iff e.symm).mpr hU, hx⟩

/-! ### Pre-adic spaces -/

/-- Wedhorn's pre-adic spaces: the locally affinoid objects of `𝒱^pre` whose structure presheaf
is adapted to the open affinoid subspaces, in the sense that on every open `V` it is the limit of
its values on the open affinoid subspaces contained in `V`. Their full subcategory of `𝒱^pre` is
Wedhorn's category `(PreAd)`, `TauCeti.WedhornPreAdicSpace`. -/
@[expose] def isPreAdic : ObjectProperty PreAdicSpace.{u} :=
  fun X ↦ isLocallyAffinoid X ∧ X.toPresheafedSpace.presheaf.IsAdapted X.affinoidOpens

theorem isPreAdic.isLocallyAffinoid {X : PreAdicSpace.{u}} (h : isPreAdic X) :
    isLocallyAffinoid X :=
  h.1

theorem isPreAdic.isAdapted {X : PreAdicSpace.{u}} (h : isPreAdic X) :
    X.toPresheafedSpace.presheaf.IsAdapted X.affinoidOpens :=
  h.2

/-- Being pre-adic is invariant under isomorphism in `𝒱^pre`: an isomorphism `e : X ≅ Y` is a
homeomorphism identifying the structure presheaves, and it matches the open affinoid subspaces of
`X` and `Y`, so adaptedness is transported along it. -/
instance isPreAdic.instIsClosedUnderIsomorphisms : isPreAdic.{u}.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- inside `isPreAdic.*`, the bare name `isLocallyAffinoid` is the accessor above
    refine ⟨ObjectProperty.prop_of_iso PreAdicSpace.isLocallyAffinoid e hX.isLocallyAffinoid, ?_⟩
    -- `X.presheaf` is adapted to the open affinoid subspaces of `X`, so its pushforward along the
    -- homeomorphism `e.hom.base` is adapted to the opens of `Y` whose preimages are open affinoid
    -- subspaces of `X`, which are the open affinoid subspaces of `Y`; `e.hom.c` identifies
    -- `Y.presheaf` with that pushforward. The two isomorphism hypotheses are those of `e.hom` as a
    -- morphism of presheafed spaces, which makes `e.hom.c` an isomorphism
    -- (`PresheafedSpace.c_isIso_of_iso`), and as a continuous map; both are the images of `e`
    -- under the forgetful functors, whose `map`s are `Hom.toHom` and `Hom.base` by definition
    have : IsIso (C := AlgebraicGeometry.PresheafedSpace CompleteSeparatedTopCommRingCat.{u})
        e.hom.toHom :=
      inferInstanceAs (IsIso (forgetToPresheafedSpace.map e.hom))
    have : IsIso e.hom.base := inferInstanceAs (IsIso (forgetToTop.map e.hom))
    have h := (hX.isAdapted.pushforward_of_iso (asIso e.hom.base)).of_iso (asIso e.hom.c).symm
    -- `(asIso e.hom.base).hom` is `e.hom.base`, and `U ∈ g ⁻¹' S` is `g U ∈ S`, by definition
    exact h.mono fun U hU ↦ (map_hom_base_mem_affinoidOpens_iff e).mp hU

/-- **The sheaf condition on the open affinoid subspaces suffices for an adapted presheaf.** If
the open affinoid subspaces of `X` form a basis and the structure presheaf is adapted to them and
is a sheaf on them, for the topology restricted to them, then it is a sheaf. For a pre-adic space
`h : isPreAdic X`, the adaptedness hypothesis is `h.isAdapted`; this is the mechanism of Wedhorn's
Remark 8.27, which makes a pre-adic space covered by sheafy affinoids an adic space. -/
theorem isSheafy_of_isAdapted_of_isSheaf_affinoidOpens {X : PreAdicSpace.{u}}
    (hB : Opens.IsBasis X.affinoidOpens)
    (hA : X.toPresheafedSpace.presheaf.IsAdapted X.affinoidOpens)
    (hs : Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : X.affinoidOpens → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : X.affinoidOpens → Opens X)).op ⋙
        X.toPresheafedSpace.presheaf)) :
    isSheafy X :=
  TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology _ _ hB hA hs

end PreAdicSpace

/-- Wedhorn's category `(PreAd)` of pre-adic spaces: the full subcategory of `𝒱^pre` whose objects
are the locally affinoid objects with structure presheaf adapted to their open affinoid subspaces
(`PreAdicSpace.isPreAdic`). -/
abbrev WedhornPreAdicSpace : Type (u + 1) :=
  PreAdicSpace.isPreAdic.{u}.FullSubcategory

end TauCeti

end
