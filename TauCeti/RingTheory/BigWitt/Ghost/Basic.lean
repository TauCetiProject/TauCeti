/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.BigWitt.TruncationSet
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Big Witt ghost polynomials

The ghost polynomial at a positive index `n` is the sum of the `(n/d)`-th powers of the
coordinates at divisors `d` of `n`, each weighted by `d`. Every such exponent is positive, so the
same polynomial evaluates on nonunital coefficients. The summand `n • x n` controls the new
coordinate in the triangular reconstruction from ghosts.

See Hesselholt, *The big de Rham–Witt complex*, §1.
-/

public section

namespace TauCeti.BigWitt

/-- The big Witt ghost polynomial at `n` evaluated at `x`. Iterating multiplication starting
at the coordinate itself expresses each positive power without requiring a multiplicative unit.
At index zero the divisor sum is empty. -/
def ghostPolynomial {R : Type*} [NonUnitalSemiring R] (n : ℕ) (x : ℕ → R) : R :=
  ∑ d ∈ n.divisors, d • (· * x d)^[n / d - 1] (x d)

/-- The ghost evaluation on a nonunital semiring uses iterated multiplication and natural
scalar multiplication. -/
theorem ghostPolynomial_eq_sum_nsmul {R : Type*} [NonUnitalSemiring R] (n : ℕ) (x : ℕ → R) :
    ghostPolynomial n x = ∑ d ∈ n.divisors, d • (· * x d)^[n / d - 1] (x d) :=
  (rfl)

/-- The evaluation formula using ordinary powers over a unital semiring. -/
theorem ghostPolynomial_eq_sum {R : Type*} [Semiring R] (n : ℕ) (x : ℕ → R) :
    ghostPolynomial n x = ∑ d ∈ n.divisors, (d : R) * x d ^ (n / d) := by
  unfold ghostPolynomial
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hn : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
  have hquot := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd))
    (Nat.pos_of_mem_divisors hd)
  rw [nsmul_eq_mul, mul_right_iterate_apply_self, Nat.sub_add_cancel hquot]

/-- The index-`n` ghost depends only on coordinates at divisors of `n`. -/
theorem ghostPolynomial_congr {R : Type*} [NonUnitalSemiring R] {n : ℕ} {x y : ℕ → R}
    (h : ∀ d ∈ n.divisors, x d = y d) : ghostPolynomial n x = ghostPolynomial n y := by
  unfold ghostPolynomial
  exact Finset.sum_congr rfl fun d hd ↦ by rw [h d hd]

/-- At a truncation index the ghost only uses coordinates in that truncation set. -/
theorem ghostPolynomial_congr_of_mem {R : Type*} [NonUnitalSemiring R] {S : TruncationSet}
    {n : ℕ} {x y : ℕ → R} (hn : n ∈ S) (h : Set.EqOn x y S) :
    ghostPolynomial n x = ghostPolynomial n y :=
  ghostPolynomial_congr fun _ hd ↦ h (S.mem_of_dvd hn (Nat.dvd_of_mem_divisors hd))

/-- Ghost evaluation commutes with coefficient homomorphisms, including nonunital ones. -/
@[simp]
theorem map_ghostPolynomial {R A F : Type*} [NonUnitalSemiring R] [NonUnitalSemiring A]
    [FunLike F R A] [NonUnitalRingHomClass F R A] (f : F) (n : ℕ) (x : ℕ → R) :
    f (ghostPolynomial n x) = ghostPolynomial n (f ∘ x) := by
  rw [ghostPolynomial, ghostPolynomial, map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have h : Function.Semiconj f (· * x d) (· * f (x d)) := fun a ↦ map_mul f a (x d)
  rw [map_nsmul]
  exact congrArg (d • ·) (h.iterate_right (n / d - 1) (x d))

/-- The index-one ghost is the first coordinate, including over nonunital semirings. -/
@[simp]
theorem ghostPolynomial_one {R : Type*} [NonUnitalSemiring R] (x : ℕ → R) :
    ghostPolynomial 1 x = x 1 := by
  simp [ghostPolynomial, Nat.divisors_one]

/-- The divisor sum at index zero is empty. -/
@[simp]
theorem ghostPolynomial_zero {R : Type*} [NonUnitalSemiring R] (x : ℕ → R) :
    ghostPolynomial 0 x = 0 := by
  simp [ghostPolynomial, Nat.divisors_zero]

/-- At a nonzero index the contribution of the last coordinate is its natural multiple. -/
theorem ghostPolynomial_eq_sum_properDivisors_nsmul_add {R : Type*} [NonUnitalSemiring R]
    (n : ℕ) (x : ℕ → R) (hn : n ≠ 0) :
    ghostPolynomial n x =
      (∑ d ∈ n.properDivisors, d • (· * x d)^[n / d - 1] (x d)) + n • x n := by
  rw [ghostPolynomial_eq_sum_nsmul, ← Nat.insert_self_properDivisors hn,
    Finset.sum_insert Nat.self_notMem_properDivisors, Nat.div_self (Nat.pos_of_ne_zero hn)]
  simp [add_comm]

/-- The unital ghost is a sum over proper divisors plus the linear term in its last coordinate. -/
theorem ghostPolynomial_eq_sum_properDivisors_add {R : Type*} [Semiring R]
    (n : ℕ) (x : ℕ → R) (hn : n ≠ 0) :
    ghostPolynomial n x =
      (∑ d ∈ n.properDivisors, (d : R) * x d ^ (n / d)) + (n : R) * x n := by
  rw [ghostPolynomial_eq_sum, ← Nat.insert_self_properDivisors hn,
    Finset.sum_insert Nat.self_notMem_properDivisors, Nat.div_self (Nat.pos_of_ne_zero hn),
    pow_one, add_comm]

/-- Ghost equality determines coordinates on a truncation set when its indices act injectively. -/
theorem eqOn_of_ghostPolynomial_eq {R : Type*} [NonUnitalSemiring R] [IsLeftCancelAdd R]
    (S : TruncationSet) (hS : ∀ n ∈ S, Function.Injective (n • · : R → R))
    {x y : ℕ → R} (h : ∀ n ∈ S, ghostPolynomial n x = ghostPolynomial n y) :
    Set.EqOn x y S := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    apply hS n hn
    have hs : (∑ d ∈ n.properDivisors, d • (· * x d)^[n / d - 1] (x d)) =
        ∑ d ∈ n.properDivisors, d • (· * y d)^[n / d - 1] (y d) := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hd
      rw [ih d hlt (S.mem_of_dvd hn hdiv)]
    have hg := h n hn
    rw [ghostPolynomial_eq_sum_properDivisors_nsmul_add n x (S.pos hn).ne',
      ghostPolynomial_eq_sum_properDivisors_nsmul_add n y (S.pos hn).ne', hs] at hg
    exact add_left_cancel hg

/-- Torsion-freeness at the primes occurring in a truncation set suffices for ghost injectivity. -/
theorem eqOn_of_ghostPolynomial_eq_of_prime_nsmul_injective {R : Type*} [NonUnitalSemiring R]
    [IsLeftCancelAdd R] (S : TruncationSet)
    (hS : ∀ p, p.Prime → p ∈ S → Function.Injective (p • · : R → R))
    {x y : ℕ → R} (h : ∀ n ∈ S, ghostPolynomial n x = ghostPolynomial n y) :
    Set.EqOn x y S := by
  apply eqOn_of_ghostPolynomial_eq S _ h
  intro n hn
  have hreg : IsSMulRegular R n := by
    rw [Nat.prod_primeFactors_pow_factorization (S.pos hn).ne']
    apply Finset.prod_induction _ (IsSMulRegular R)
      (fun _ _ ha hb => ha.mul hb) (IsSMulRegular.one R)
    intro p hp
    exact IsSMulRegular.pow _
      (hS p (Nat.prime_of_mem_primeFactors hp) (S.mem_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)))
  unfold IsSMulRegular at hreg
  exact hreg

end TauCeti.BigWitt
