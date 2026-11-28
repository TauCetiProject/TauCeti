/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Iterated polynomial composition

`Polynomial.map_iterate_comp` commutes coefficient maps with iteration, and
`Polynomial.IsMonicOfDegree.iterate_comp` preserves monicity and raises the degree to the
iteration count. `Polynomial.iterate_comp_mul_X_succ` factors successive
iterates, `Polynomial.iterate_comp_X_pow` computes the iterates of a power of `X`, and
`Polynomial.derivative_iterate_comp_X_of_derivative_eq_C` computes their derivative for a
polynomial with constant derivative. We use Mathlib's `Polynomial.map_comp`,
`Polynomial.IsMonicOfDegree.comp`, and `Polynomial.derivative_comp`.
-/

public section

namespace Polynomial

variable {R : Type*}

/-- Coefficient maps commute with repeated composition. -/
@[simp] theorem map_iterate_comp {S : Type*} [Semiring R] [Semiring S]
    (p q : R[X]) (φ : R →+* S) (n : ℕ) :
    (p.comp^[n] q).map φ = (p.map φ).comp^[n] (q.map φ) :=
  (Function.Semiconj.iterate_right (map_comp φ p) n) q

/-- A monic polynomial of degree `d` iterates to a monic polynomial of degree `d ^ n`. -/
theorem IsMonicOfDegree.iterate_comp [Semiring R] [Nontrivial R] {p : R[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (n : ℕ) : (p.comp^[n] X).IsMonicOfDegree (d ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Function.iterate_zero_apply] using isMonicOfDegree_X R
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    by_cases hd : d = 0
    · have hp' : p = 1 := isMonicOfDegree_zero_iff.mp (hd ▸ hp)
      simp only [hd, hp', one_comp, zero_mul, isMonicOfDegree_zero_iff]
    · exact hp.comp (pow_ne_zero _ hd) ih

/-- For `p = g * X`, the next iterate is the composition of `g` with the preceding
iterate, times that preceding iterate. -/
theorem iterate_comp_mul_X_succ [Semiring R] (g : R[X]) (n : ℕ) :
    (g * X).comp^[n + 1] X = g.comp ((g * X).comp^[n] X) * (g * X).comp^[n] X := by
  rw [Function.iterate_succ_apply', mul_X_comp]

/-- The `n`-fold iterate of composition by `X ^ q` sends `p` to `p ^ (q ^ n)`. -/
@[simp] theorem iterate_comp_X_pow [Semiring R] (p : R[X]) (q n : ℕ) :
    (X ^ q : R[X]).comp^[n] p = p ^ (q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', X_pow_comp, ih, ← pow_mul, pow_succ]

variable [CommSemiring R]

/-- If `p' = C c`, the derivative of the `n`-fold iterate of `p` from `X` is `C (c ^ n)`. -/
theorem derivative_iterate_comp_X_of_derivative_eq_C {p : R[X]} {c : R}
    (h : p.derivative = C c) (n : ℕ) : derivative (p.comp^[n] X) = C (c ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', derivative_comp, h, C_comp, ih, ← C_mul, pow_succ]

end Polynomial
