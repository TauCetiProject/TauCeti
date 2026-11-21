/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Adic
public import TauCeti.Topology.Algebra.Ring.Compact

/-!
# Compact local rings are profinite flat over themselves

A compact Hausdorff noetherian local ring `R` is profinite flat over itself
(`TauCeti.IsProfiniteFlat.self_of_isLocalRing`).
-/

public section

namespace TauCeti.IsProfiniteFlat

/-- A compact Hausdorff noetherian local ring is profinite flat over itself. -/
theorem self_of_isLocalRing (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R] :
    IsProfiniteFlat R R :=
  self_of_isAdic (IsLocalRing.isAdic_maximalIdeal R)

end TauCeti.IsProfiniteFlat
