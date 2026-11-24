/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents

/-!
# Linear combinations of orthogonal idempotents

For a family of orthogonal idempotents `e`, multiplying a combination `∑ i, a i * e i` by `e j`
extracts the coefficient `a j`. If the family is moreover complete and the ring is commutative,
powers of such a combination are computed coefficientwise. This is how powers are taken of an
element with a known decomposition along idempotents, such as a locally constant function on a
disconnected spectrum.

## Main results

* `OrthogonalIdempotents.sum_mul_mul`: `(∑ i, a i * e i) * e j = a j * e j`.
* `CompleteOrthogonalIdempotents.sum_sub_mul`: `∑ i, (a i - c) * e i = ∑ i, a i * e i - c`.
* `CompleteOrthogonalIdempotents.sum_mul_pow`: `(∑ i, a i * e i) ^ n = ∑ i, a i ^ n * e i`.
-/

public section

namespace OrthogonalIdempotents

variable {R ι : Type*} [Semiring R] [Fintype ι] {e : ι → R}

/-- Multiplying a combination `∑ i, a i * e i` of orthogonal idempotents by `e j` extracts the
coefficient `a j`. -/
theorem sum_mul_mul (he : OrthogonalIdempotents e) (a : ι → R) (j : ι) :
    (∑ i, a i * e i) * e j = a j * e j := by
  classical
  simp [Finset.sum_mul, mul_assoc, he.mul_eq]

end OrthogonalIdempotents

namespace CompleteOrthogonalIdempotents

/-- Shifting every coefficient of a combination of a complete family of orthogonal idempotents by
`c` shifts the combination by `c`: `∑ i, (a i - c) * e i = ∑ i, a i * e i - c`. -/
theorem sum_sub_mul {R ι : Type*} [Ring R] [Fintype ι] {e : ι → R}
    (he : CompleteOrthogonalIdempotents e) (a : ι → R) (c : R) :
    ∑ i, (a i - c) * e i = ∑ i, a i * e i - c := by
  simp [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, he.complete]

variable {R ι : Type*} [CommSemiring R] [Fintype ι] {e : ι → R}

/-- Powers of a combination of a complete family of orthogonal idempotents are computed
coefficientwise: `(∑ i, a i * e i) ^ n = ∑ i, a i ^ n * e i`. At `n = 0` this is completeness. -/
theorem sum_mul_pow (he : CompleteOrthogonalIdempotents e) (a : ι → R) (n : ℕ) :
    (∑ i, a i * e i) ^ n = ∑ i, a i ^ n * e i := by
  induction n with
  | zero => simp [he.complete]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, mul_comm (e j), he.toOrthogonalIdempotents.sum_mul_mul, ← mul_assoc, ← pow_succ]

end CompleteOrthogonalIdempotents
