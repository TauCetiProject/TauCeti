/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

/-!
# The upper triangular subgroup of `GL ι R` is closed

For a commutative topological ring `R` whose points are closed, the upper triangular subgroup
`TauCeti.upperTriangularGroup ι R` is a closed subset of `GL ι R`, which carries the topology of
`Units`: it is the preimage, under the continuous coercion to matrices, of the vanishing locus of
the entries below the diagonal. So the quotient `GL ι R ⧸ upperTriangularGroup ι R` is Hausdorff
whenever `GL ι R` is a topological group.

## Main results

* `TauCeti.isClosed_upperTriangularGroup`: the instance that the upper triangular subgroup is
  closed.
-/

public section

open Matrix

namespace TauCeti

variable (ι R : Type*) [Fintype ι] [LinearOrder ι] [CommRing R] [TopologicalSpace R] [T1Space R]

/-- **The upper triangular subgroup of `GL ι R` is closed**: it is cut out by the vanishing of the
entries below the diagonal. -/
instance isClosed_upperTriangularGroup :
    IsClosed (upperTriangularGroup ι R : Set (GL ι R)) := by
  have h : (upperTriangularGroup ι R : Set (GL ι R)) =
      Units.val ⁻¹' ⋂ (i : ι) (j : ι) (_ : j < i), {M : Matrix ι ι R | M i j = 0} := by
    ext g
    simp [UpperTriangularGroup.mem_iff, BlockTriangular]
  rw [h]
  refine IsClosed.preimage Units.continuous_val
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
  exact isClosed_singleton.preimage (continuous_id.matrix_elem i j)

end TauCeti
