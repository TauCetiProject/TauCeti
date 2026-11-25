/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Div

import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials of given degree

A ring homomorphism into a nontrivial semiring sends a monic polynomial of degree `n` to a
monic polynomial of degree `n`. Over a nontrivial ring, `X ^ n - a` is monic of degree `n` for
every `n ≠ 0`. Two monic polynomials of degree `n` differ by a polynomial of degree less than
`n`, and so does the remainder of any polynomial on division by a monic polynomial of degree `n`.
-/

public section

namespace Polynomial

variable {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]

/-- Mapping the coefficients into a nontrivial semiring preserves being monic of degree `n`. -/
theorem IsMonicOfDegree.map {p : R[X]} {n : ℕ} (hp : p.IsMonicOfDegree n) (f : R →+* S) :
    (p.map f).IsMonicOfDegree n :=
  ⟨(hp.monic.natDegree_map f).trans hp.natDegree_eq, hp.monic.map f⟩

/-- `X ^ n - a` is monic of degree `n` over a nontrivial ring, for every `n ≠ 0`. -/
theorem isMonicOfDegree_X_pow_sub_C {R : Type*} [Ring R] [Nontrivial R] {n : ℕ} (hn : n ≠ 0)
    (a : R) : (X ^ n - C a : R[X]).IsMonicOfDegree n :=
  (isMonicOfDegree_X_pow R n).sub (by rwa [natDegree_C, Nat.pos_iff_ne_zero])

/-- Two monic polynomials of degree `n` differ by a polynomial of degree less than `n`. Unlike
`Polynomial.IsMonicOfDegree.natDegree_sub_lt`, this also holds for `n = 0`. -/
theorem IsMonicOfDegree.degree_sub_lt {R : Type*} [Ring R] {p q : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (hq : q.IsMonicOfDegree n) : (p - q).degree < n :=
  (degree_lt_iff_coeff_zero _ _).mpr fun _ hm ↦ by rw [coeff_sub, hp.coeff_eq hq hm, sub_self]

/-- The remainder on division by a monic polynomial of degree `n` has degree less than `n`. -/
theorem IsMonicOfDegree.degree_modByMonic_lt {R : Type*} [Ring R] [Nontrivial R] {q : R[X]}
    {n : ℕ} (hq : q.IsMonicOfDegree n) (p : R[X]) : (p %ₘ q).degree < n := by
  simpa [degree_eq_natDegree hq.ne_zero, hq.natDegree_eq] using
    Polynomial.degree_modByMonic_lt p hq.monic

end Polynomial
