/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Compact.Adic
public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic

/-!
# Adic properties of profinite flat modules

`TauCeti.IsProfiniteFlat.self_of_isAdic`: a compact Hausdorff `I`-adic ring is profinite flat.
-/

public section

namespace TauCeti.IsProfiniteFlat

/-- A compact Hausdorff commutative ring whose topology is `I`-adic is profinite flat over
itself. -/
theorem self_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R] [CompactSpace R] [T2Space R]
    {I : Ideal R} (hI : IsAdic I) : IsProfiniteFlat R R :=
  ⟨.self_of_isAdic hI, inferInstance⟩

end TauCeti.IsProfiniteFlat
