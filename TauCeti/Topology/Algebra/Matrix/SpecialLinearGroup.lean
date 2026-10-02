/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The special linear group is closed in the general linear group

The image of `Matrix.SpecialLinearGroup.toGL : SL n R →* GL n R` is the kernel of the determinant
(`Matrix.SpecialLinearGroup.range_toGL_eq_ker_det`), the set of units whose underlying matrix has
determinant one. The determinant is a polynomial in the entries, so this set is closed in the
topology that `GL n R` inherits from the entrywise matrix topology. This is the closedness input
that makes the special linear group a closed subgroup of the general linear Lie group.

## Main results

* `Matrix.SpecialLinearGroup.isClosed_range_toGL`: the image of `SL n R` in `GL n R` is closed
  over any `T₁` topological commutative ring.
-/

public section

namespace Matrix.SpecialLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]

/-- The image of the special linear group in the general linear group is closed: it is the
preimage of `1` under the continuous map taking a unit to the determinant of its matrix. -/
theorem isClosed_range_toGL :
    IsClosed ((toGL : SpecialLinearGroup n R →* GL n R).range : Set (GL n R)) := by
  have hset : ((toGL : SpecialLinearGroup n R →* GL n R).range : Set (GL n R)) =
      (fun g : GL n R => (g : Matrix n n R).det) ⁻¹' {1} := by
    ext g
    simp [range_toGL_eq_ker_det, Units.ext_iff]
  rw [hset]
  exact isClosed_singleton.preimage Units.continuous_val.matrix_det

end Matrix.SpecialLinearGroup
