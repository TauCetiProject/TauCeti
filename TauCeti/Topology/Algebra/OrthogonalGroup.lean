/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Closedness of the matrix special orthogonal group

The matrix special orthogonal group is the closed carrier used when a concrete orthogonal matrix
group is given its Lie-group structure.  Its defining equations are the transpose-isometry
equation and the determinant-one equation; both are closed in the entrywise matrix topology.

## Main result

* `Matrix.isClosed_orthogonalGroup` and `Matrix.isClosed_specialOrthogonalGroup`:
  the matrix orthogonal and special orthogonal groups are closed over any `T₁` topological
  commutative ring.

The proof is stated directly with the transpose equation rather than routing through the unitary
group, whose topology uses a star operation and therefore does not apply to an arbitrary ring.
-/

public section

open Matrix Set

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The matrix orthogonal group is closed in the entrywise matrix topology. -/
theorem isClosed_orthogonalGroup [T1Space R] :
    IsClosed (Matrix.orthogonalGroup n R : Set (Matrix n n R)) := by
  have horth : (Matrix.orthogonalGroup n R : Set (Matrix n n R)) =
      (fun A : Matrix n n R => A.transpose * A) ⁻¹' ({1} : Set (Matrix n n R)) := by
    ext A
    simpa using (Matrix.mem_orthogonalGroup_iff' (n := n) (R := R) (A := A))
  rw [horth]
  exact isClosed_singleton.preimage ((continuous_id.matrix_transpose).mul continuous_id)

/-- The matrix special orthogonal group is closed in the entrywise matrix topology. -/
theorem isClosed_specialOrthogonalGroup [T1Space R] :
    IsClosed (Matrix.specialOrthogonalGroup n R : Set (Matrix n n R)) := by
  have hso : (Matrix.specialOrthogonalGroup n R : Set (Matrix n n R)) =
      (Matrix.orthogonalGroup n R : Set (Matrix n n R)) ∩ {A | A.det = 1} := by
    ext A
    simpa using Matrix.mem_specialOrthogonalGroup_iff
  have hdet_closed : IsClosed {A : Matrix n n R | A.det = 1} :=
    isClosed_singleton.preimage (Continuous.matrix_det continuous_id)
  rw [hso]
  exact isClosed_orthogonalGroup.inter hdet_closed

end Matrix
