/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Noetherianity under finite-type morphisms

A scheme of finite type over a Noetherian scheme is Noetherian. In particular, proper schemes
over a field are Noetherian, supplying the finiteness hypothesis in divisor and line-bundle
arguments without requiring a separate instance from the caller.

The underlying space of a locally Noetherian scheme is locally connected, since it is covered by
the Noetherian spaces of its affine opens. In particular its connected components are open.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A scheme of finite type over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f

/-- The underlying space of a locally Noetherian scheme is locally connected: every point has
arbitrarily small affine open neighbourhoods, whose underlying spaces are Noetherian and hence
locally connected. -/
instance locallyConnectedSpace_of_isLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := ⟨interior U, isOpen_interior⟩) (mem_interior_iff_mem_nhds.mpr hU)
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : TopologicalSpace.NoetherianSpace (W : Set X) := noetherianSpace_of_isAffineOpen W hW
  refine ⟨(↑) '' connectedComponent (⟨x, hxW⟩ : W), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact interior_subset (hWU y.2)
  · exact W.isOpen.isOpenMap_subtype_val _ isOpen_connectedComponent
  · exact ⟨_, mem_connectedComponent, rfl⟩
  · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

end TauCeti.AlgebraicGeometry
