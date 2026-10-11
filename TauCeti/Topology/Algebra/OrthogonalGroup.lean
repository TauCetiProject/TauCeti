/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Closedness of matrix orthogonal groups

The matrix orthogonal and special orthogonal groups are closed in the entrywise matrix topology.
The orthogonal group is cut out by the transpose-inverse equations, and the special orthogonal
group adds the determinant-one equation. Mathlib defines these groups as the unitary and special
unitary groups for the trivial scalar star operation, so their closedness follows from the
corresponding unitary results.

## Main result

* `TauCeti.Matrix.isClosed_orthogonalGroup` and `TauCeti.Matrix.isClosed_specialOrthogonalGroup`:
  the matrix orthogonal and special orthogonal groups are closed over any `T₁` topological
  commutative ring.

The closedness statements identify the topological input supplied by these carriers for later
constructions of Lie-group structures and continuity arguments on the corresponding subgroups.
-/

public section

namespace TauCeti.Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [local instance] starRingOfComm

local instance instContinuousStar {R : Type*} [CommSemiring R] [TopologicalSpace R] :
    ContinuousStar R := ⟨continuous_id⟩

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

end TauCeti.Matrix
