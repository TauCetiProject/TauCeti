/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import TauCeti.LinearAlgebra.Matrix.Compound
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Traces on the exterior powers and the reversed characteristic polynomial

Let `f` be an endomorphism of a finite free module `M` over a commutative ring `R`. The traces of
the endomorphisms `⋀ʳ f` that `f` induces on the exterior powers of `M` are, up to sign, the
coefficients of the reversed characteristic polynomial `det (1 - t f)`:

`det (1 - t f) = ∑ᵣ (-1) ^ r tr (⋀ʳ f) tʳ`

(`LinearMap.trace_exteriorPower_map`). In a basis, the matrix of `⋀ʳ f` is the `r`-th compound
matrix of the matrix of `f`, whose trace is the sum of the `r × r` principal minors
(`Matrix.trace_compound`); these sums are the coefficients of `det (1 - t f)` up to the sign
`(-1) ^ r` (`Matrix.coeff_charpolyRev`). At `t = 1` this gives the alternating sum

`∑ᵣ (-1) ^ r tr (⋀ʳ f) = det (1 - f)`

(`LinearMap.sum_neg_one_pow_mul_trace_exteriorPower_map`). Since the homology of a torus is the
exterior algebra on its first homology, this alternating sum is the Lefschetz number of a self-map
of a torus which acts on homology through its exterior powers, such as a linear automorphism.

## Main results

* `LinearMap.neg_one_pow_mul_trace_exteriorPower_map`,
  `LinearMap.trace_exteriorPower_map`: `tr (⋀ʳ f) = (-1) ^ r [tʳ] det (1 - t f)`.
* `LinearMap.sum_neg_one_pow_mul_trace_exteriorPower_map`:
  `∑ᵣ (-1) ^ r tr (⋀ʳ f) = det (1 - f)`.

## References

* N. Bourbaki, *Algebra I, Chapters 1–3*, Chapter III, §8.
-/

public section

open Polynomial

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- **Signed traces on the exterior powers.** For an endomorphism `f` of a finite free module,
`(-1) ^ r` times the trace of `⋀ʳ f` is the coefficient of `tʳ` in `det (1 - t f)`. -/
theorem neg_one_pow_mul_trace_exteriorPower_map (f : M →ₗ[R] M) (r : ℕ) :
    (-1) ^ r * trace R (⋀[R]^r M) (exteriorPower.map r f) = f.charpoly.reverse.coeff r := by
  nontriviality R
  let b := Module.finBasis R M
  rw [trace_eq_matrix_trace R (b.exteriorPower r), b.toMatrix_exteriorPower_map_eq_compound b,
    ← charpoly_toMatrix f b, Matrix.reverse_charpoly, Matrix.coeff_charpolyRev,
    Matrix.trace_compound]

/-- **Traces on the exterior powers.** For an endomorphism `f` of a finite free module, the trace
of `⋀ʳ f` is `(-1) ^ r` times the coefficient of `tʳ` in `det (1 - t f)`. -/
theorem trace_exteriorPower_map (f : M →ₗ[R] M) (r : ℕ) :
    trace R (⋀[R]^r M) (exteriorPower.map r f) = (-1) ^ r * f.charpoly.reverse.coeff r := by
  simp [← neg_one_pow_mul_trace_exteriorPower_map, ← mul_assoc, ← mul_pow]

/-- **The alternating sum of the traces on the exterior powers.** For an endomorphism `f` of a
finite free module `M`, `∑ᵣ (-1) ^ r tr (⋀ʳ f) = det (1 - f)`, the sum running over the degrees
`r ≤ rank M` in which `⋀ʳ M` can be nonzero. -/
theorem sum_neg_one_pow_mul_trace_exteriorPower_map (f : M →ₗ[R] M) :
    ∑ r ∈ Finset.range (Module.finrank R M + 1),
        (-1) ^ r * trace R (⋀[R]^r M) (exteriorPower.map r f) = (id - f).det := by
  nontriviality R
  let b := Module.finBasis R M
  have hdeg : f.charpoly.reverse.natDegree < Module.finrank R M + 1 := by
    rw [← charpoly_toMatrix f b, Matrix.reverse_charpoly]
    simpa using Nat.lt_succ_of_le (Matrix.natDegree_charpolyRev_le (toMatrix b b f))
  simp_rw [neg_one_pow_mul_trace_exteriorPower_map]
  rw [← det_toMatrix b, map_sub, toMatrix_id, ← Matrix.eval_one_charpolyRev,
    ← Matrix.reverse_charpoly, charpoly_toMatrix, eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one]

end LinearMap
