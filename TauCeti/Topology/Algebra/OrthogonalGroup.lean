/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Closedness of the matrix special orthogonal group

The matrix special orthogonal group is the closed carrier used when a concrete orthogonal matrix
group is given its Lie-group structure.  Its defining equations are the transpose-isometry
equation and the determinant-one equation; both are closed in the entrywise matrix topology.

## Main result

* `Matrix.isClosed_orthogonalGroup` and `Matrix.isClosed_specialOrthogonalGroup`:
  the matrix orthogonal and special orthogonal groups are closed over any `T₁` topological
  commutative ring.

The results are obtained by specializing the existing closedness results for the unitary and
special unitary groups to the trivial star structure on a commutative ring.
-/

public section

open Matrix Set

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [local instance] starRingOfComm

local instance instContinuousStar : ContinuousStar R := ⟨continuous_id⟩

/-- The matrix orthogonal group is closed in the entrywise matrix topology. -/
theorem isClosed_orthogonalGroup [T1Space R] :
    IsClosed (Matrix.orthogonalGroup n R : Set (Matrix n n R)) := by
  simpa only [Matrix.orthogonalGroup] using
    (isClosed_unitary (R := Matrix n n R))

/-- The matrix special orthogonal group is closed in the entrywise matrix topology. -/
theorem isClosed_specialOrthogonalGroup [T1Space R] :
    IsClosed (Matrix.specialOrthogonalGroup n R : Set (Matrix n n R)) := by
  simpa only [Matrix.specialOrthogonalGroup] using
    (TauCeti.Matrix.isClosed_specialUnitaryGroup (n := n) (𝕜 := R))

end Matrix
