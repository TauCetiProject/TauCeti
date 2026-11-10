/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperTriangular
import TauCeti.Topology.Instances.Matrix

/-!
# Closedness of the positive upper-triangular group

Over real and complex normed fields, the upper-triangular matrices with positive real diagonal
form a closed subgroup inside the general linear group. Invertibility makes nonnegative real
diagonal entries strictly positive, so closedness follows from the existing upper-triangular
closedness instance and the closed set of matrices with nonnegative diagonal.

## Main results

* `TauCeti.isClosed_posUpperTriangularGroup`: the positive upper-triangular group is closed in GL.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for the positive upper-triangular matrix factor.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable (ι : Type*) [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [RCLike 𝕜]

/-- The positive upper-triangular group is closed in the general linear group. -/
instance isClosed_posUpperTriangularGroup :
    IsClosed (posUpperTriangularGroup ι 𝕜 : Set (GL ι 𝕜)) := by
  have heq : (posUpperTriangularGroup ι 𝕜 : Set (GL ι 𝕜)) =
      (upperTriangularGroup ι 𝕜 : Set (GL ι 𝕜)) ∩
      Units.val ⁻¹' {M : Matrix ι ι 𝕜 | ∀ i, 0 ≤ M i i} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe]
    rw [PosUpperTriangularGroup.mem_iff_nonneg, UpperTriangularGroup.mem_iff]
  rw [heq]
  exact (isClosed_upperTriangularGroup ι 𝕜).inter
    (Matrix.isClosed_setOfPred_nonneg_diag.preimage Units.continuous_val)

end TauCeti
