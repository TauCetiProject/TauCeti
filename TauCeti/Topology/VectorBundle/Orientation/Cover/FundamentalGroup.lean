/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Orientability of vector bundles from the fundamental group

A finite-dimensional real vector bundle over a connected, locally path-connected base is
orientable if the fundamental group of the base has no subgroup of index two. Otherwise the
orientation double cover is connected, and the image of its fundamental group has index equal
to the number of sheets, namely two
(`TauCeti.VectorBundleOrientationCover.pathConnectedSpace_of_isEmpty` gives the path-connectedness
of the double cover of a non-orientable bundle). In particular, every such bundle over a simply
connected base is orientable.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218, Springer, 2013,
  Chapter 15, The Orientation Covering.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.32
  (the number of sheets is the index of the induced subgroup).
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B] [LocallyPathConnectedSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]

/-- The orientation double cover of a non-orientable real vector bundle over a connected, locally
path-connected base is path connected, provided `ι` has cardinality the rank of the bundle. -/
theorem _root_.TauCeti.VectorBundleOrientationCover.pathConnectedSpace_of_isEmpty [ConnectedSpace B]
    (hι : Fintype.card ι = finrank ℝ F) [IsEmpty (VectorBundleOrientation F E ι)] :
    PathConnectedSpace (VectorBundleOrientationCover F E ι) := by
  have : ConnectedSpace (VectorBundleOrientationCover F E ι) := by
    by_contra hc
    obtain ⟨o⟩ := (nonempty_iff_not_connectedSpace hι).2 hc
    exact isEmptyElim o
  have : LocallyPathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    (VectorBundleOrientationCover.isCoveringMap_proj hι).isLocalHomeomorph.locallyPathConnectedSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- A real vector bundle over a connected, locally path-connected base whose fundamental group
has no subgroup of index two is orientable, provided `ι` has cardinality the rank of the bundle. -/
theorem nonempty_of_forall_index_ne_two [ConnectedSpace B]
    (hι : Fintype.card ι = finrank ℝ F) (b : B)
    (hπ : ∀ G : Subgroup (FundamentalGroup B b), G.index ≠ 2) :
    Nonempty (VectorBundleOrientation F E ι) := by
  by_contra hno
  have := not_nonempty_iff.1 hno
  have := VectorBundleOrientationCover.pathConnectedSpace_of_isEmpty (F := F) (E := E) hι
  have hp := VectorBundleOrientationCover.isCoveringMap_proj (F := F) (E := E) hι
  obtain ⟨p, hp₀⟩ := VectorBundleOrientationCover.surjective_proj (F := F) (E := E) hι b
  have hcard := hp.card_fiber_eq_index ⟨p, hp₀⟩
  rw [Nat.card_coe_set_eq, VectorBundleOrientationCover.ncard_fiber hι] at hcard
  exact hπ _ hcard.symm

/-- A real vector bundle over a simply connected, locally path-connected base is orientable,
provided `ι` has cardinality the rank of the bundle. -/
theorem nonempty_of_simplyConnectedSpace [SimplyConnectedSpace B]
    (hι : Fintype.card ι = finrank ℝ F) : Nonempty (VectorBundleOrientation F E ι) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  apply nonempty_of_forall_index_ne_two hι b
  intro G hG
  have hindex : G.index = 1 := by
    rw [Subsingleton.elim G ⊤, Subgroup.index_top]
  omega

end TauCeti.VectorBundleOrientation
