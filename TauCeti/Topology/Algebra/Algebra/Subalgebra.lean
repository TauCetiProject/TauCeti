/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra

/-!
# Subalgebras of a topological ring

A subalgebra of a topological ring, with the subspace topology, is a topological ring. Mathlib
records this for subrings (`Subring.instIsTopologicalRing`) and records only the semiring version
for subalgebras, so instance search does not find it for a subalgebra over a commutative ring.

## Main declarations

* `Subalgebra.instIsTopologicalRing`: a subalgebra of a topological ring is a topological ring.
-/

public section

namespace Subalgebra

/-- A subalgebra of a topological ring is a topological ring. -/
instance instIsTopologicalRing {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A] (S : Subalgebra R A) : IsTopologicalRing S :=
  inferInstanceAs (IsTopologicalRing S.toSubring)

end Subalgebra
