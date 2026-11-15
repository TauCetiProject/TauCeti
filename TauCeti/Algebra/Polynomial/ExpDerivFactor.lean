/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import TauCeti.Algebra.Polynomial.Derivative

/-!
# The shifted differential operator `(D + c) ^ m` on polynomials

Differentiating an exponential polynomial `P(X) exp(c X)` `m` times produces
`(expDerivFactor c m P)(X) exp(c X)`, where `Polynomial.expDerivFactor c m` is the `m`-th power of
the `R`-linear operator `D + c` (`Q ↦ Q' + c Q`) on `R[X]`. Because `D` and scalar multiplication
by `c` commute on `R[X]`, `(D + c) ^ m` expands binomially in the iterated derivatives of `P` and
never increases `natDegree`; when `R` has no zero divisors and `c ≠ 0`, it preserves `natDegree`
and has trivial kernel.

## Main definitions

* `Polynomial.expDerivFactor`: the `R`-linear endomorphism `(derivative + c • id) ^ m` on `R[X]`.

## Main results

* `Polynomial.expDerivFactor_succ_apply`, `Polynomial.expDerivFactor_apply_eq_iterate`: the
  stepwise recursion `Q ↦ Q' + C c * Q` and its `m`-fold iterate.
* `Polynomial.expDerivFactor_eq_sum`, `Polynomial.expDerivFactor_X_pow`: the binomial expansion
  `∑ j ∈ range (m + 1), C ((m.choose j : R) * c ^ (m - j)) * derivative^[j] P` and its
  specialization to monomials `X ^ d`.
* `Polynomial.natDegree_expDerivFactor_le`, `Polynomial.coeff_expDerivFactor_natDegree`:
  `(expDerivFactor c m P).natDegree ≤ P.natDegree`, with degree-`natDegree` coefficient
  `c ^ m * P.leadingCoeff`.
* `Polynomial.natDegree_expDerivFactor`, `Polynomial.expDerivFactor_eq_zero_iff`: when `R` has no
  zero divisors and `c ≠ 0`, `expDerivFactor c m` preserves `natDegree` and has trivial kernel.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* M. Karatarakis, `ExpSeries.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
-/

public section

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The `m`-th iterate `(D + c) ^ m` of the shifted derivative `Q ↦ Q' + c Q` on `R[X]`, as an
`R`-linear endomorphism. Under formal differentiation of power series, multiplying by `exp (c X)`
intertwines `d/dX` with `expDerivFactor c 1`. -/
noncomputable def expDerivFactor (c : R) (m : ℕ) : R[X] →ₗ[R] R[X] :=
  (derivative + c • LinearMap.id) ^ m

theorem expDerivFactor_def (c : R) (m : ℕ) :
    expDerivFactor c m = (derivative + c • LinearMap.id) ^ m :=
  (rfl)

@[simp]
theorem expDerivFactor_zero (c : R) : expDerivFactor c 0 = LinearMap.id :=
  (rfl)

theorem expDerivFactor_zero_apply (c : R) (P : R[X]) : expDerivFactor c 0 P = P :=
  (rfl)

theorem expDerivFactor_one (c : R) : expDerivFactor c 1 = derivative + c • LinearMap.id :=
  pow_one _

theorem expDerivFactor_one_apply (c : R) (P : R[X]) :
    expDerivFactor c 1 P = derivative P + C c * P := by
  simp [expDerivFactor_one, smul_eq_C_mul]

theorem expDerivFactor_succ (c : R) (m : ℕ) :
    expDerivFactor c (m + 1) = (derivative + c • LinearMap.id) ∘ₗ expDerivFactor c m :=
  pow_succ' _ m

theorem expDerivFactor_succ' (c : R) (m : ℕ) :
    expDerivFactor c (m + 1) = expDerivFactor c m ∘ₗ (derivative + c • LinearMap.id) :=
  pow_succ _ m

theorem expDerivFactor_succ_apply (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c (m + 1) P =
      derivative (expDerivFactor c m P) + C c * expDerivFactor c m P := by
  simp [expDerivFactor_succ, smul_eq_C_mul]

theorem expDerivFactor_succ_apply' (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c (m + 1) P = expDerivFactor c m (derivative P + C c * P) := by
  simp [expDerivFactor_succ', smul_eq_C_mul]

theorem expDerivFactor_add (c : R) (m n : ℕ) :
    expDerivFactor c (m + n) = expDerivFactor c m ∘ₗ expDerivFactor c n :=
  pow_add _ m n

theorem expDerivFactor_add_apply (c : R) (m n : ℕ) (P : R[X]) :
    expDerivFactor c (m + n) P = expDerivFactor c m (expDerivFactor c n P) := by
  rw [expDerivFactor_add]
  rfl

/-- Applying `expDerivFactor c m` agrees with iterating `Q ↦ Q' + C c * Q` `m` times. -/
theorem expDerivFactor_apply_eq_iterate (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P = (fun Q ↦ derivative Q + C c * Q)^[m] P := by
  induction m generalizing P with
  | zero => rfl
  | succ m ih => rw [expDerivFactor_succ_apply', Function.iterate_succ_apply, ih]

/-- At `c = 0`, `expDerivFactor 0 m` is the `m`-th iterated derivative. -/
@[simp]
theorem expDerivFactor_zero_left (m : ℕ) (P : R[X]) :
    expDerivFactor (0 : R) m P = derivative^[m] P := by
  simp [expDerivFactor_apply_eq_iterate]

/-- Differentiation commutes with `expDerivFactor c m`. -/
theorem commute_derivative_expDerivFactor (c : R) (m : ℕ) :
    Commute (derivative : R[X] →ₗ[R] R[X]) (expDerivFactor c m) := by
  refine Commute.pow_right (Commute.add_right (Commute.refl _) ?_) m
  ext P
  simp

theorem derivative_expDerivFactor (c : R) (m : ℕ) (P : R[X]) :
    derivative (expDerivFactor c m P) = expDerivFactor c m (derivative P) :=
  LinearMap.congr_fun (commute_derivative_expDerivFactor c m) P

@[simp]
theorem expDerivFactor_C (c a : R) (m : ℕ) :
    expDerivFactor c m (C a) = C (c ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih => rw [expDerivFactor_succ_apply, ih, derivative_C, zero_add, ← C_mul, pow_succ',
      mul_assoc]

@[simp]
theorem expDerivFactor_one_right (c : R) (m : ℕ) :
    expDerivFactor c m 1 = C (c ^ m) := by
  simpa using expDerivFactor_C c 1 m

@[simp]
theorem expDerivFactor_one_X (c : R) :
    expDerivFactor c 1 X = 1 + C c * X := by
  simp [expDerivFactor_one_apply]

/-- **Binomial form of `(D + c) ^ m`.** Since differentiation commutes with scalar multiplication by
`c`, `expDerivFactor c m P = ∑ j ≤ m, (m choose j) c ^ (m - j) P⁽ʲ⁾`. -/
theorem expDerivFactor_eq_sum (c : R) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P =
      ∑ j ∈ Finset.range (m + 1), C ((m.choose j : R) * c ^ (m - j)) * derivative^[j] P := by
  have hcomm : Commute (derivative : R[X] →ₗ[R] R[X]) (c • LinearMap.id) := by
    ext Q
    simp
  rw [expDerivFactor_def, hcomm.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mul_apply_eq_comp, natCast_apply_eq_smul, smul_pow, LinearMap.smul_apply]
  have hid : ((LinearMap.id : R[X] →ₗ[R] R[X]) ^ (m - j)) (m.choose j • P) = m.choose j • P := by
    simp
  rw [hid, map_smul, map_nsmul, _root_.pow_apply_eq_iterate, smul_eq_C_mul, nsmul_eq_mul,
    ← C_eq_natCast, ← mul_assoc, ← C_mul, mul_comm (c ^ (m - j))]

/-- Explicit binomial expansion of `expDerivFactor c m (X ^ d)`, the polynomial factor of the
`m`-th derivative of `X ^ d exp(c X)`. -/
theorem expDerivFactor_X_pow (c : R) (m d : ℕ) :
    expDerivFactor c m (X ^ d) =
      ∑ j ∈ Finset.range (m + 1),
        C ((m.choose j : R) * c ^ (m - j) * d.descFactorial j) * X ^ (d - j) := by
  rw [expDerivFactor_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul]

theorem coeff_expDerivFactor (c : R) (m : ℕ) (P : R[X]) (i : ℕ) :
    (expDerivFactor c m P).coeff i =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : R) * c ^ (m - j) * (derivative^[j] P).coeff i := by
  rw [expDerivFactor_eq_sum, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul]

theorem eval_expDerivFactor (c : R) (m : ℕ) (P : R[X]) (x : R) :
    (expDerivFactor c m P).eval x =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : R) * c ^ (m - j) * (derivative^[j] P).eval x := by
  rw [expDerivFactor_eq_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_mul, eval_C]

/-- `expDerivFactor` commutes with `Polynomial.map` along any ring homomorphism. -/
theorem map_expDerivFactor {S : Type*} [CommSemiring S] (f : R →+* S) (c : R) (m : ℕ)
    (P : R[X]) : (expDerivFactor c m P).map f = expDerivFactor (f c) m (P.map f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [expDerivFactor_succ_apply, expDerivFactor_succ_apply, Polynomial.map_add,
      Polynomial.map_mul, map_C, ← derivative_map, ih]

/-- Applying `expDerivFactor c m` does not increase `natDegree`. -/
theorem natDegree_expDerivFactor_le (c : R) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).natDegree ≤ P.natDegree := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [expDerivFactor_succ_apply]
    exact (natDegree_add_le _ _).trans <| max_le
      ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans ih))
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
    rw [expDerivFactor_succ_apply, coeff_add, coeff_derivative, hzero, zero_mul, zero_add,
      coeff_C_mul, ih, pow_succ', mul_assoc]

section NoZeroDivisors

variable [NoZeroDivisors R] {c : R}

/-- Over a commutative semiring without zero divisors, `expDerivFactor c m` preserves `natDegree`
whenever `c ≠ 0`. -/
@[simp]
theorem natDegree_expDerivFactor (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).natDegree = P.natDegree := by
  rw [expDerivFactor_apply_eq_iterate, natDegree_iterate_derivative_add_C_mul hc]

/-- Over a commutative semiring without zero divisors, `expDerivFactor c m` has trivial kernel
whenever `c ≠ 0`. -/
@[simp]
theorem expDerivFactor_eq_zero_iff (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    expDerivFactor c m P = 0 ↔ P = 0 := by
  rw [expDerivFactor_apply_eq_iterate, iterate_derivative_add_C_mul_eq_zero_iff hc]

@[simp]
theorem leadingCoeff_expDerivFactor (hc : c ≠ 0) (m : ℕ) (P : R[X]) :
    (expDerivFactor c m P).leadingCoeff = c ^ m * P.leadingCoeff := by
  rw [leadingCoeff, natDegree_expDerivFactor hc, coeff_expDerivFactor_natDegree]

end NoZeroDivisors

end CommSemiring

end Polynomial
