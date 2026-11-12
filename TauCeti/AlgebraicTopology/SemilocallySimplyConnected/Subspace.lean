/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
public import TauCeti.Topology.PathComponent

/-!
# The hypotheses of covering-space theory on subspaces

The connected covering spaces of a path-connected space are classified by subgroups of its
fundamental group as soon as the space is locally path-connected and semilocally simply connected.
This file shows that these two hypotheses are local, that they pass to retracts, and that
semilocal simple connectivity passes to unions of path components.

* **Locality.** If every point of `X` has a neighbourhood which, as a subspace, is locally
  path-connected, then so is `X` (`LocallyPathConnectedSpace.of_forall_exists_mem_nhds`). If a
  neighbourhood `U` of a point is, as a subspace, semilocally simply connected at that point, then
  so is `X` (`SemilocallySimplyConnectedAt.of_mem_nhds`): a loop in `X` near the point lies in `U`,
  and a null-homotopy in `U` is one in `X`. The converse of the second statement fails, since the
  null-homotopies in `X` may leave `U`.
* **Retracts.** If `s : X → Y` and `r : Y → X` are continuous with `r ∘ s = id`, then `X` inherits
  local path-connectedness from `Y`, because `r` is a quotient map
  (`Function.LeftInverse.locallyPathConnectedSpace`), and semilocal simple connectivity, because
  `s` is injective on fundamental groups
  (`Function.LeftInverse.semilocallySimplyConnectedSpace`).
* **Unions of path components.** A subspace containing the path component of each of its points
  is semilocally simply connected when the ambient space is
  (`TauCeti.SemilocallySimplyConnectedSpace.subtype_of_pathComponent_subset`): a null-homotopy of
  a loop in it never leaves it. This generalizes the instance for a single path component.

Together these reduce the two hypotheses for a mapping space into a manifold to the case of a
mapping space into an open subset of a vector space; see
`TauCeti.Topology.MappingSpace.NeighborhoodRetract`.

## Main results

* `LocallyPathConnectedSpace.of_forall_exists_mem_nhds`,
  `TauCeti.SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds`: both hypotheses are local.
* `Function.LeftInverse.locallyPathConnectedSpace`,
  `Function.LeftInverse.semilocallySimplyConnectedSpace`: both hypotheses pass to retracts.
* `TauCeti.SemilocallySimplyConnectedSpace.subtype_of_pathComponent_subset`: semilocal simple
  connectivity passes to unions of path components.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

open Function Set Topology TauCeti
open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Locality -/

/-- A neighbourhood of a point of a subspace `U` which is itself a neighbourhood of that point
is a neighbourhood in the ambient space. -/
private theorem image_val_mem_nhds {U : Set X} {x : X} (hU : U ∈ 𝓝 x) {V : Set U}
    (hV : V ∈ 𝓝 (⟨x, mem_of_mem_nhds hU⟩ : U)) : (↑) '' V ∈ 𝓝 x := by
  rw [← nhdsWithin_eq_nhds.2 hU]
  exact mem_nhds_subtype_iff_nhdsWithin.1 hV

/-- **Local path-connectedness is local.** A space in which every point has a neighbourhood that
is locally path-connected as a subspace is locally path-connected. -/
theorem LocallyPathConnectedSpace.of_forall_exists_mem_nhds
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, LocallyPathConnectedSpace U) : LocallyPathConnectedSpace X where
  path_connected_basis x := by
    obtain ⟨U, hU, _⟩ := h x
    rw [Filter.hasBasis_self]
    intro t ht
    obtain ⟨s, ⟨hs, hsc⟩, hst : s ⊆ _⟩ := (path_connected_basis
      (⟨x, mem_of_mem_nhds hU⟩ : U)).mem_iff.1
      (continuous_subtype_val.continuousAt.preimage_mem_nhds ht)
    exact ⟨(↑) '' s, image_val_mem_nhds hU hs, hsc.image continuous_subtype_val,
      image_subset_iff.2 hst⟩

/-- **Semilocal simple connectivity at a point is local.** If a neighbourhood `U` of a point `x`
is, as a subspace, semilocally simply connected at `x`, then so is the ambient space: loops near
`x` lie in `U`, and a null-homotopy in `U` is a null-homotopy in the ambient space. -/
theorem SemilocallySimplyConnectedAt.of_mem_nhds {U : Set X} {x : X} (hU : U ∈ 𝓝 x)
    (h : SemilocallySimplyConnectedAt (⟨x, mem_of_mem_nhds hU⟩ : U)) :
    SemilocallySimplyConnectedAt x := by
  have hx : x ∈ U := mem_of_mem_nhds hU
  obtain ⟨V, hV, hloops⟩ := semilocallySimplyConnectedAt_def.1 h
  refine semilocallySimplyConnectedAt_def.2 ⟨(↑) '' V, image_val_mem_nhds hU hV, fun γ hγ ↦ ?_⟩
  have hmem (t : I) : γ t ∈ U := by
    obtain ⟨y, -, hy⟩ := hγ ⟨t, rfl⟩
    exact hy ▸ y.2
  have hγV : range (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) hmem) ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hyV, hy⟩ := hγ ⟨t, rfl⟩
    have hyt : γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) hmem t = y :=
      Subtype.ext ((Path.codRestrict_coe _ hmem t).trans hy.symm)
    rwa [hyt]
  simpa [Path.map_refl] using (hloops _ hγV).map ⟨Subtype.val, continuous_subtype_val⟩

/-- **Semilocal simple connectivity is local.** A space in which every point has a neighbourhood
that is semilocally simply connected as a subspace is semilocally simply connected. -/
theorem TauCeti.SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, SemilocallySimplyConnectedSpace U) :
    SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := by
    obtain ⟨U, hU, _⟩ := h x
    exact .of_mem_nhds hU (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt _)

/-! ### Retracts -/

/-- **A retract of a locally path-connected space is locally path-connected.** The retraction
`r` has the continuous section `s`, so it is a quotient map. -/
theorem Function.LeftInverse.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] {s : X → Y}
    {r : Y → X} (h : LeftInverse r s) (hr : Continuous r) (hs : Continuous s) :
    LocallyPathConnectedSpace X :=
  (IsQuotientMap.of_inverse hs hr h).locallyPathConnectedSpace

/-- **A retract of a semilocally simply connected space is semilocally simply connected.** The
section `s` is injective on fundamental groups, since `r` is a left inverse of it. -/
theorem Function.LeftInverse.semilocallySimplyConnectedSpace [SemilocallySimplyConnectedSpace Y]
    {s : X → Y} {r : Y → X} (h : LeftInverse r s) (hr : Continuous r) (hs : Continuous s) :
    SemilocallySimplyConnectedSpace X :=
  .of_map_injective ⟨s, hs⟩ (isIncompressible_of_leftInverse (f := ⟨s, hs⟩) (r := ⟨r, hr⟩)
    (ContinuousMap.ext fun x ↦ h x)).fundamentalGroup_injective

/-! ### Unions of path components -/

/-- **A union of path components inherits semilocal simple connectivity.** If `S` contains the
path component of each of its points, a null-homotopy in the ambient space of a loop in `S`
stays in `S`. -/
theorem TauCeti.SemilocallySimplyConnectedSpace.subtype_of_pathComponent_subset
    [SemilocallySimplyConnectedSpace X] {S : Set X} (hS : ∀ x ∈ S, pathComponent x ⊆ S) :
    SemilocallySimplyConnectedSpace S where
  semilocallySimplyConnectedAt a := by
    obtain ⟨U, hU, hloops⟩ := semilocallySimplyConnectedAt_def.1
      (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (a : X))
    refine semilocallySimplyConnectedAt_def.2
      ⟨(↑) ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, fun γ hγ ↦ ?_⟩
    obtain ⟨H⟩ := hloops (γ.map continuous_subtype_val) (by
      rintro _ ⟨t, rfl⟩
      exact hγ ⟨t, rfl⟩)
    -- At each time `t`, the homotopy runs in the path component of `γ t`, which lies in `S`.
    have hmem : ∀ p : I × I, H p ∈ S := fun ⟨s, t⟩ ↦
      hS _ (γ t).2 ((H.evalAt t).mem_pathComponent s)
    exact Path.homotopic_of_continuous_square (fun p ↦ ⟨H p, hmem p⟩)
      (H.continuous.subtype_mk hmem) (fun t ↦ Subtype.ext (by simp)) (fun t ↦ Subtype.ext (by simp))
      (fun t ↦ Subtype.ext (by simp)) (fun t ↦ Subtype.ext (by simp))
