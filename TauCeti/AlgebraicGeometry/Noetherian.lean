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

A locally Noetherian scheme is a locally connected topological space, since every point has a
Noetherian affine open neighbourhood and Noetherian spaces are locally connected. In particular
the connected components of a locally Noetherian scheme are open, so that a connected component
is an open subscheme.
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

/-- A locally Noetherian scheme is locally connected. In particular its connected components are
open and closed. -/
instance locallyConnectedSpace_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  -- A Noetherian affine open neighbourhood `W ⊆ U` of `x` is locally connected, so the connected
  -- component of `x` in `W` is an open connected neighbourhood of `x` inside `U`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr hU)
      isOpen_interior
  have := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have := noetherianSpace_of_isAffineOpen W hW
  have : LocallyConnectedSpace (W : Set X) := inferInstanceAs (LocallyConnectedSpace W)
  refine ⟨Subtype.val '' connectedComponent (⟨x, hxW⟩ : W), ?_,
    W.isOpen.isOpenMap_subtype_val _ isOpen_connectedComponent, ⟨⟨x, hxW⟩,
      mem_connectedComponent, rfl⟩, isConnected_connectedComponent.image _
        continuous_subtype_val.continuousOn⟩
  rintro _ ⟨y, -, rfl⟩
  exact interior_subset (hWU y.2)

end TauCeti.AlgebraicGeometry
