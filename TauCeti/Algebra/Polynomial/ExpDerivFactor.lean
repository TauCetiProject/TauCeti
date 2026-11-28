/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import TauCeti.Algebra.Polynomial.Derivative

/-!
# The operator `(D + c) ^ m` on polynomials

For an element `c` of a commutative semiring `R` and `m : ℕ`, `Polynomial.expDerivFactor c m` is
the `R`-linear endomorphism `(D + c) ^ m` of `R[X]`, where `D` is the derivative. Its purpose is
the derivatives of exponential polynomials: by the product rule,
`d/dz (P (z) exp (c z)) = (P′ (z) + c P (z)) exp (c z)`, so the `m`-th derivative of
`P (z) exp (c z)` is `expDerivFactor c m P (z) exp (c z)`. In the auxiliary functions of Baker's
method the coefficients of these polynomials are the numbers whose sizes and norms are estimated.

The operator is characterized by `expDerivFactor c 0 P = P` and the recursion
`expDerivFactor c (m + 1) P = (expDerivFactor c m P)′ + c · expDerivFactor c m P`. Since `D`
and multiplication by `c` commute, the binomial theorem gives the closed form
`expDerivFactor c m P = ∑_{j ≤ m} (m choose j) c ^ (m - j) P⁽ʲ⁾`. The operator never raises the
degree, commutes with coefficient maps, and, for an ultrametric norm, multiplies a bound for the
coefficients by at most `max 1 ‖c‖` for each derivative, because multiplying by a natural number
does not increase an ultrametric norm.

The iterate of `q ↦ q′ + C δ * q` itself, over possibly noncommutative semirings, is studied in
`TauCeti.Algebra.Polynomial.Derivative`, where for `δ ≠ 0` over a semiring without zero divisors
it is shown to preserve the degree and to have trivial kernel;
`Polynomial.expDerivFactor_eq_iterate` identifies the two.

## Main definitions

* `Polynomial.expDerivFactor c m`: the linear map `(D + c) ^ m` on `R[X]`.

## Main results

* `Polynomial.expDerivFactor_zero`, `Polynomial.expDerivFactor_succ`: the recursion.
* `Polynomial.expDerivFactor_add`: `(D + c) ^ (m + n) = (D + c) ^ m ∘ (D + c) ^ n`.
* `Polynomial.expDerivFactor_eq_sum`: the binomial form
  `∑_{j ≤ m} (m choose j) c ^ (m - j) P⁽ʲ⁾`.
* `Polynomial.natDegree_expDerivFactor_le`: the degree does not grow.
* `Polynomial.map_expDerivFactor`: compatibility with ring homomorphisms of the coefficients.
* `Polynomial.norm_coeff_expDerivFactor_le`: over an ultrametric normed ring, coefficients
  bounded by `B` become coefficients bounded by `max 1 ‖c‖ ^ m * B`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2.
* M. Karatarakis, `Mathlib/NumberTheory/Transcendental/Baker/Padic/ExpSeries.lean` on the
  `baker-padic` branch of `mkaratarakis/mathlib4` (commit `65cdef5722`), which formalizes this
  operator as `derivAdd`.
-/

public section

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The linear map `(D + c) ^ m` on polynomials, where `D` is the derivative. The `m`-th
derivative of `P (z) exp (c z)` is `expDerivFactor c m P (z) exp (c z)`. -/
noncomputable def expDerivFactor (c : R) (m : ℕ) : R[X] →ₗ[R] R[X] :=
  (derivative + c • LinearMap.id) ^ m

/-- `expDerivFactor c m` is the `m`-th power of `D + c` as a linear endomorphism. -/
theorem expDerivFactor_def (c : R) (m : ℕ) :
    expDerivFactor c m = (derivative + c • LinearMap.id) ^ m :=
  (rfl)

/-- `(D + c) ^ 0` is the identity. -/
@[simp]
theorem expDerivFactor_zero (c : R) (P : R[X]) : expDerivFactor c 0 P = P := by
  simp [expDerivFactor]

/-- The recursion `(D + c) ^ (m + 1) P = D ((D + c) ^ m P) + c (D + c) ^ m P`. -/
theorem expDerivFactor_succ (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c (m + 1) P =
      derivative (expDerivFactor c m P) + C c * expDerivFactor c m P := by
  simp [expDerivFactor, pow_succ', smul_eq_C_mul]

/-- The recursion with the new factor applied first:
`(D + c) ^ (m + 1) P = (D + c) ^ m (P′ + c P)`. -/
theorem expDerivFactor_succ' (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c (m + 1) P = expDerivFactor c m (derivative P + C c * P) := by
  simp [expDerivFactor, pow_succ, smul_eq_C_mul]

/-- `(D + c) P = P′ + c P`. -/
@[simp]
theorem expDerivFactor_one (c : R) (P : R[X]) :
    expDerivFactor c 1 P = derivative P + C c * P := by
  simp [expDerivFactor_succ]

/-- `(D + c) ^ (m + n) = (D + c) ^ m ∘ (D + c) ^ n`. -/
theorem expDerivFactor_add (c : R) (m n : ℕ) (P : R[X]) :
    expDerivFactor c (m + n) P = expDerivFactor c m (expDerivFactor c n P) := by
  simp [expDerivFactor, pow_add]

/-- `expDerivFactor c m` is the `m`-th iterate of `q ↦ q′ + c q`. -/
theorem expDerivFactor_eq_iterate (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P = (fun q ↦ derivative q + C c * q)^[m] P := by
  induction m with
  | zero => simp
  | succ m ih => rw [expDerivFactor_succ, ih, Function.iterate_succ_apply']

/-- For `c = 0` the operator is the iterated derivative. -/
@[simp]
theorem expDerivFactor_zero_left (m : ℕ) (P : R[X]) :
    expDerivFactor (0 : R) m P = derivative^[m] P := by
  induction m with
  | zero => simp
  | succ m ih => simp [expDerivFactor_succ, ih, Function.iterate_succ_apply']

/-- On a constant the derivative contributes nothing: `(D + c) ^ m a = c ^ m a`. -/
@[simp]
theorem expDerivFactor_C (c a : R) (m : ℕ) : expDerivFactor c m (C a) = C (c ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [expDerivFactor_succ, ih, derivative_C]
    simp [pow_succ', mul_assoc]

/-- `(D + c) ^ m 1 = c ^ m`. -/
@[simp]
theorem expDerivFactor_apply_one (c : R) (m : ℕ) : expDerivFactor c m 1 = C (c ^ m) := by
  simpa using expDerivFactor_C c 1 m

/-- The operator commutes with the derivative. -/
theorem derivative_expDerivFactor (c : R) (m : ℕ) (P : R[X]) :
    derivative (expDerivFactor c m P) = expDerivFactor c m (derivative P) := by
  induction m with
  | zero => simp
  | succ m ih => simp [expDerivFactor_succ, ih]

/-- **The binomial form** `(D + c) ^ m P = ∑_{j ≤ m} (m choose j) c ^ (m - j) P⁽ʲ⁾`. -/
theorem expDerivFactor_eq_sum (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P =
      ∑ j ∈ range (m + 1), C ((m.choose j : R) * c ^ (m - j)) * derivative^[j] P := by
  have hc : Commute (derivative : R[X] →ₗ[R] R[X]) (c • LinearMap.id) :=
    (Commute.one_right _).smul_right c
  rw [expDerivFactor, hc.add_pow, LinearMap.sum_apply]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← Module.End.one_eq_id, smul_pow, one_pow]
  simp [pow_apply_eq_iterate, smul_eq_C_mul, nsmul_eq_mul]
  ring

/-- Explicit binomial expansion of `expDerivFactor c m (X ^ d)`, the polynomial factor of the
`m`-th derivative of `X ^ d exp(c X)`. -/
theorem expDerivFactor_X_pow (c : R) (m d : ℕ) :
    expDerivFactor c m (X ^ d) =
      ∑ j ∈ range (m + 1),
        C ((m.choose j : R) * c ^ (m - j) * d.descFactorial j) * X ^ (d - j) := by
  rw [expDerivFactor_eq_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul]

/-- The `i`-th coefficient of `(D + c) ^ m P`. -/
theorem coeff_expDerivFactor (c : R) (m : ℕ) (P : R[X]) (i : ℕ) :
    (expDerivFactor c m P).coeff i =
      ∑ j ∈ range (m + 1), (m.choose j : R) * c ^ (m - j) * (derivative^[j] P).coeff i := by
  rw [expDerivFactor_eq_sum, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul]

/-- Evaluating `(D + c) ^ m P` at `x` via the binomial expansion. -/
theorem eval_expDerivFactor (c : R) (m : ℕ) (P : R[X]) (x : R) :
    (expDerivFactor c m P).eval x =
      ∑ j ∈ range (m + 1), (m.choose j : R) * c ^ (m - j) * (derivative^[j] P).eval x := by
  rw [expDerivFactor_eq_sum, eval_finsetSum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eval_mul, eval_C]

/-- **The degree does not grow** under `(D + c) ^ m`. -/
theorem natDegree_expDerivFactor_le (c : R) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).natDegree ≤ P.natDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [expDerivFactor_succ]
    exact natDegree_add_le_of_degree_le ((natDegree_derivative_le _).trans (by omega))
      ((natDegree_C_mul_le _ _).trans ih)

/-- Applying `expDerivFactor c m` does not increase `degree`. -/
theorem degree_expDerivFactor_le (c : R) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).degree ≤ P.degree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · exact degree_le_natDegree.trans
      ((WithBot.coe_le_coe.mpr (natDegree_expDerivFactor_le c m P)).trans_eq
        (degree_eq_natDegree hP).symm)

/-- The coefficient of `expDerivFactor c m P` in degree `P.natDegree` is `c ^ m * P.leadingCoeff`:
each differentiation drops the top term below degree `P.natDegree`. -/
theorem coeff_expDerivFactor_natDegree (c : R) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).coeff P.natDegree = c ^ m * P.leadingCoeff := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzero : (expDerivFactor c m P).coeff (P.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt
        ((natDegree_expDerivFactor_le c m P).trans_lt (Nat.lt_succ_self _))
    rw [expDerivFactor_succ]
    simp [coeff_derivative, hzero, ih]
    ring

/-- `(D + c) ^ m` commutes with a ring homomorphism `f` of the coefficients, which sends `c` to
`f c`. -/
theorem map_expDerivFactor {S : Type*} [CommSemiring S] (f : R →+* S) (c : R) (m : ℕ)
    (P : R[X]) : (expDerivFactor c m P).map f = expDerivFactor (f c) m (P.map f) := by
  induction m with
  | zero => simp
  | succ m ih => simp [expDerivFactor_succ, ← ih, ← derivative_map]

section NoZeroDivisors

variable [NoZeroDivisors R] {c : R}

/-- Over a commutative semiring without zero divisors, `expDerivFactor c m` preserves the degree
of a polynomial whenever `c ≠ 0`. -/
@[simp]
theorem natDegree_expDerivFactor (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).natDegree = P.natDegree := by
  simpa only [expDerivFactor_eq_iterate] using
    natDegree_iterate_derivative_add_C_mul hc m (q := P)

/-- Over a commutative semiring without zero divisors, `expDerivFactor c m` has trivial kernel
whenever `c ≠ 0`. -/
@[simp]
theorem expDerivFactor_eq_zero_iff (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P = 0 ↔ P = 0 := by
  simpa only [expDerivFactor_eq_iterate] using
    iterate_derivative_add_C_mul_eq_zero_iff hc m (q := P)

/-- Over a commutative semiring without zero divisors, `expDerivFactor c m` scales the leading
coefficient by `c ^ m` whenever `c ≠ 0`. -/
@[simp]
theorem leadingCoeff_expDerivFactor (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).leadingCoeff = c ^ m * P.leadingCoeff := by
  rw [leadingCoeff, natDegree_expDerivFactor hc, coeff_expDerivFactor_natDegree]

end NoZeroDivisors

end CommSemiring

section Ultrametric

variable {K : Type*} [SeminormedCommRing K] [IsUltrametricDist K]

/-- **The coefficients of `(D + c) ^ m P` at an ultrametric absolute value.** If every
coefficient of `P` has norm at most `B`, then every coefficient of `(D + c) ^ m P` has norm at most
`max 1 ‖c‖ ^ m * B`: each derivative multiplies coefficients by natural numbers, which does not
increase their norms. -/
theorem norm_coeff_expDerivFactor_le (c : K) {P : K[X]} {B : ℝ} (hP : ∀ i, ‖P.coeff i‖ ≤ B)
    (m i : ℕ) : ‖(expDerivFactor c m P).coeff i‖ ≤ max 1 ‖c‖ ^ m * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hP 0)
  induction m generalizing i with
  | zero => simpa using hP i
  | succ m ih =>
    set A := max 1 ‖c‖ ^ m * B
    have hA : 0 ≤ A := mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) m) hB
    have hpow : max 1 ‖c‖ ^ (m + 1) * B = max 1 ‖c‖ * A := by ring
    rw [expDerivFactor_succ, coeff_add, coeff_derivative, coeff_C_mul, hpow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · -- the derivative multiplies the coefficient by the natural number `i + 1`
      calc ‖(expDerivFactor c m P).coeff (i + 1) * (i + 1)‖
          = ‖(i + 1) • (expDerivFactor c m P).coeff (i + 1)‖ := by
            congr 1
            push_cast [nsmul_eq_mul]
            ring
        _ ≤ A := (IsUltrametricDist.norm_nsmul_le _ _).trans (ih _)
        _ ≤ max 1 ‖c‖ * A := le_mul_of_one_le_left hA (le_max_left _ _)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul (le_max_right _ _) (ih i) (norm_nonneg _) (by positivity))

end Ultrametric

end Polynomial
