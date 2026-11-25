/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum

import TauCeti.Algebra.Ring.FrobeniusLift
import TauCeti.Algebra.Ring.GeomSum

/-!
# The q-integers

For an element `q` of a semiring and a natural number `n`, the `q`-integer
`[n]_q = ∑ i ∈ range n, q ^ i` is the finite geometric sum (`TauCeti.QCrys.qInteger`). It is
defined as a sum rather than as the quotient `(q ^ n - 1) / (q - 1)`, which is meaningless at
`q = 1` and wherever `q - 1` is a zero divisor; the identity `[n]_q * (q - 1) = q ^ n - 1` holds in
every ring (`TauCeti.QCrys.qInteger_mul_sub_one`), and `[n]_1 = n`
(`TauCeti.QCrys.qInteger_one_left`).

If a ring endomorphism `φ` sends `q` to `q ^ p`, as the Frobenius lift of the `q`-de Rham prism
does, the product `[p]_q · φ([p]_q) ⋯ φ^(r - 1)([p]_q)` telescopes to `[p ^ r]_q`
(`TauCeti.QCrys.prod_pow_apply_qInteger`).

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Notation 16.1.
-/

public section

open Finset

namespace TauCeti

namespace QCrys

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S]

/-- The `q`-integer `[n]_q = ∑ i ∈ range n, q ^ i`, a finite geometric sum (Bhatt and Scholze,
*Prisms and prismatic cohomology*, Notation 16.1). -/
def qInteger (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

theorem qInteger_eq_sum (q : R) (n : ℕ) : qInteger q n = ∑ i ∈ range n, q ^ i :=
  (rfl)

@[simp]
theorem qInteger_zero (q : R) : qInteger q 0 = 0 :=
  sum_range_zero _

theorem qInteger_succ (q : R) (n : ℕ) : qInteger q (n + 1) = qInteger q n + q ^ n :=
  sum_range_succ _ _

/-- At `q = 1` the `q`-integer `[n]_1` is `n`. -/
@[simp]
theorem qInteger_one_left (n : ℕ) : qInteger (1 : R) n = n :=
  one_geom_sum n

/-- The `q`-integers are natural under ring homomorphisms. -/
@[simp]
theorem map_qInteger {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (q : R) (n : ℕ) :
    f (qInteger q n) = qInteger (f q) n := by
  simp [qInteger]

end Semiring

/-- If a ring endomorphism `φ` satisfies `φ(q) = q ^ p`, then
`[p]_q · φ([p]_q) ⋯ φ^(r - 1)([p]_q) = [p ^ r]_q`. -/
theorem prod_pow_apply_qInteger [CommSemiring R] {φ : R →+* R} {q : R} {p : ℕ}
    (hq : φ q = q ^ p) (r : ℕ) :
    ∏ s ∈ range r, (φ ^ s) (qInteger q p) = qInteger q (p ^ r) := by
  induction r with
  | zero => simp [qInteger]
  | succ r ih =>
    rw [prod_range_succ, ih, map_qInteger, pow_apply_of_apply_eq_pow hq, qInteger, qInteger,
      qInteger, pow_succ, geom_sum_range_mul]

/-- `[n]_q * (q - 1) = q ^ n - 1`, in every ring. -/
theorem qInteger_mul_sub_one [Ring R] (q : R) (n : ℕ) : qInteger q n * (q - 1) = q ^ n - 1 :=
  geom_sum_mul q n

end QCrys

end TauCeti
