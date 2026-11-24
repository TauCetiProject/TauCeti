/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace as a coefficient of the characteristic polynomial

The trace of an endomorphism of a finite free module is minus the next coefficient of its
characteristic polynomial (`LinearMap.trace_eq_neg_charpoly_nextCoeff`), Mathlib's
`Matrix.trace_eq_neg_charpoly_nextCoeff` read in a basis.

## Main results

* `LinearMap.trace_eq_neg_charpoly_nextCoeff`: `trace f = -f.charpoly.nextCoeff`.
-/

public section

namespace LinearMap

/-- The trace of an endomorphism of a finite free module is minus the next coefficient of its
characteristic polynomial (Mathlib's `Matrix.trace_eq_neg_charpoly_nextCoeff`, read in a basis). -/
theorem trace_eq_neg_charpoly_nextCoeff {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : Module.End R M) :
    LinearMap.trace R M f = -f.charpoly.nextCoeff := by
  rw [LinearMap.trace_eq_matrix_trace R (Module.Free.chooseBasis R M),
    Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix]

end LinearMap
