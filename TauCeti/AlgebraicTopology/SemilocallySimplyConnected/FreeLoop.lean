/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Subspace
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# Semilocal simple connectivity of the contractible free loops

The contractible free loops `𝓛₀Q` form a union of path components of the free loop space
`C(S¹, Q)` (`TauCeti.pathComponent_subset_contractibleLoops`), so they are semilocally simply
connected whenever `C(S¹, Q)` is
(`TauCeti.SemilocallySimplyConnectedSpace.subtype_of_pathComponent_subset`). This holds for any
space `Q`; for `Q` a manifold see `TauCeti.Geometry.Manifold.MappingSpace`.

## Main results

* `TauCeti.semilocallySimplyConnectedSpace_contractibleLoops`: `𝓛₀Q` is semilocally simply
  connected when `C(S¹, Q)` is.
-/

public section

namespace TauCeti

/-- The contractible free loops `𝓛₀Q` are semilocally simply connected when the free loop space
is: a null-homotopy of a loop of contractible free loops stays in `𝓛₀Q`, a union of path
components. -/
instance semilocallySimplyConnectedSpace_contractibleLoops {Q : Type*}
    [TopologicalSpace Q] [SemilocallySimplyConnectedSpace C(Circle, Q)] :
    SemilocallySimplyConnectedSpace (contractibleLoops Q) :=
  .subtype_of_pathComponent_subset fun _ ↦ pathComponent_subset_contractibleLoops

end TauCeti
