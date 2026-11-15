/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary

/-!
# Unitary upper triangular matrices are diagonal

Over a commutative star ring `R`, an invertible matrix that is both unitary and upper triangular
is diagonal: its inverse is its conjugate transpose, which is lower triangular, and is also upper
triangular as the inverse of an upper triangular matrix. So the unitary matrices lying in the upper
triangular subgroup of `GL ι R` are exactly the diagonal ones.

## Main results

* `TauCeti.isDiag_of_mem_unitarySubgroup_of_mem_upperTriangularGroup`: a unitary upper triangular
  invertible matrix is diagonal.
* `TauCeti.mem_comap_toUnits_upperTriangularGroup_iff`: a unitary matrix is upper triangular
  exactly when it is diagonal.
-/

public section

open Matrix

namespace TauCeti

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R] [StarRing R]

/-- **A unitary upper triangular matrix is diagonal.** Its inverse is its conjugate transpose,
which is lower triangular, and is upper triangular as the inverse of an upper triangular
matrix. -/
theorem isDiag_of_mem_unitarySubgroup_of_mem_upperTriangularGroup {g : GL ι R}
    (hK : g ∈ unitarySubgroup (GL ι R)) (hB : g ∈ upperTriangularGroup ι R) :
    (g : Matrix ι ι R).IsDiag := by
  have hinv := UpperTriangularGroup.mem_iff.1 (inv_mem hB)
  rw [coe_inv_eq_star_of_mem_unitarySubgroup hK] at hinv
  intro i j hij
  rcases hij.lt_or_gt with hij | hij
  · simpa using congrArg star (hinv hij)
  · exact UpperTriangularGroup.mem_iff.1 hB hij

/-- **A unitary matrix is upper triangular exactly when it is diagonal.** -/
theorem mem_comap_toUnits_upperTriangularGroup_iff {U : unitaryGroup ι R} :
    U ∈ (upperTriangularGroup ι R).comap Unitary.toUnits ↔ (U : Matrix ι ι R).IsDiag := by
  rw [Subgroup.mem_comap, UpperTriangularGroup.mem_iff, Unitary.val_toUnits_apply]
  refine ⟨fun h => ?_, fun h i j hij => h hij.ne'⟩
  have hK : Unitary.toUnits U ∈ unitarySubgroup (GL ι R) :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.2 (by simp)
  simpa using isDiag_of_mem_unitarySubgroup_of_mem_upperTriangularGroup hK
    (by simpa [UpperTriangularGroup.mem_iff] using h)

end TauCeti
