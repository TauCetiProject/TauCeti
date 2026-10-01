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
* `TauCeti.PreAdicSpace.isLocallyAffinoid.instIsClosedUnderIsomorphisms`: being locally affinoid is
  invariant under isomorphism.

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

/-- An isomorphism `e : X ≅ Y` carries open affinoid subspaces of `X` to open affinoid subspaces
of `Y`. -/
theorem map_inv_base_mem_affinoidOpens {Y : PreAdicSpace.{u}} (e : X ≅ Y) {U : Opens X}
    (hU : U ∈ X.affinoidOpens) : (Opens.map e.inv.base).obj U ∈ Y.affinoidOpens :=
  ObjectProperty.prop_of_iso isAffinoid (restrictIso e U) hU

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
    exact ⟨_, map_inv_base_mem_affinoidOpens _ e hU, hx⟩

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
