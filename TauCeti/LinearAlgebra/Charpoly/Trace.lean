/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace as a coefficient of the characteristic polynomial

The trace of an endomorphism of a finite free module is minus the next coefficient of its
characteristic polynomial (`LinearMap.trace_eq_neg_charpoly_nextCoeff`), Mathlib's
`Matrix.trace_eq_neg_charpoly_nextCoeff` read in a basis. For finitely many endomorphisms `f i`
and multiplicities `c i`, the weighted sum `∑ i, c i • trace (f i)` is therefore minus the next
coefficient of `∏ i, (f i).charpoly ^ c i` (`LinearMap.sum_nsmul_trace_eq_neg_nextCoeff_prod`).

## Main results

* `LinearMap.trace_eq_neg_charpoly_nextCoeff`: `trace f = -f.charpoly.nextCoeff`.
* `LinearMap.sum_nsmul_trace_eq_neg_nextCoeff_prod`:
  `∑ i, c i • trace (f i) = -(∏ i, (f i).charpoly ^ c i).nextCoeff`.
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

/-- For finitely many endomorphisms `f i` of finite free modules and multiplicities `c i`, the
weighted trace `∑ i, c i • trace (f i)` is minus the next coefficient of
`∏ i, (f i).charpoly ^ c i`. -/
theorem sum_nsmul_trace_eq_neg_nextCoeff_prod {R ι : Type*} [CommRing R]
    [Fintype ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, Module.End R (M i))
    (c : ι → ℕ) :
    ∑ i, c i • LinearMap.trace R (M i) (f i) = -(∏ i, (f i).charpoly ^ c i).nextCoeff := by
  rw [Polynomial.Monic.nextCoeff_prod _ _ fun i _ => (charpoly_monic _).pow _,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(charpoly_monic _).nextCoeff_pow, trace_eq_neg_charpoly_nextCoeff, smul_neg]

end LinearMap
