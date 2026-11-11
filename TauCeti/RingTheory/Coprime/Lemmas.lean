/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprimality of the products `a b (a + b)` and `a² + a b + b²`, and of prime powers

For coprime elements `a` and `b` of a commutative ring, the products `a b (a + b)` and
`a² + a b + b²` are coprime. Modulo `a`, `b` and `a + b` the second product is `b²`, `a²` and
`-a b`, each of them coprime to the respective modulus.

Up to the factors `16`, these products are the square root of the discriminant and the `c₄` of
the Frey–Hellegouarch curve `y² = x (x - a) (x + b)`, whose discriminant is `16 (a b (a + b))²` and
whose `c₄` is `16 (a² + a b + b²)`. So the coprimality says that away from `2` the Frey curve of a
coprime pair has good or multiplicative reduction everywhere.

Powers of distinct rational primes are pairwise coprime in any commutative ring, so divisibilities
`p ^ e p ∣ z` at finitely many distinct primes combine to `∏ p ∈ P, p ^ e p ∣ z`. Mathlib's
`Finset.prod_primes_dvd` gives only the squarefree product `∏ p ∈ P, p`.

## Main results

* `IsCoprime.mul_mul_add_sq_add_mul_add_sq`: if `a` and `b` are coprime, so are `a b (a + b)` and
  `a² + a b + b²`.
* `Finset.prod_primes_pow_dvd`: prime powers dividing `z` combine to their product.
-/

public section

variable {R : Type*} [CommRing R] {a b : R}

/-- **For coprime `a` and `b`, the products `a b (a + b)` and `a² + a b + b²` are coprime**:
modulo `a`, `b` and `a + b` the second is `b²`, `a²` and `-a b`. -/
theorem IsCoprime.mul_mul_add_sq_add_mul_add_sq (h : IsCoprime a b) :
    IsCoprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) := by
  refine IsCoprime.symm (IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_)
  · -- `a² + a b + b² ≡ b² (mod a)`
    rw [show a ^ 2 + a * b + b ^ 2 = b ^ 2 + a * (a + b) by ring, IsCoprime.add_mul_left_left_iff]
    exact h.symm.pow_left
  · -- `a² + a b + b² ≡ a² (mod b)`
    rw [show a ^ 2 + a * b + b ^ 2 = a ^ 2 + b * (a + b) by ring, IsCoprime.add_mul_left_left_iff]
    exact h.pow_left
  · -- `a² + a b + b² ≡ -a b (mod a + b)`
    rw [show a ^ 2 + a * b + b ^ 2 = -(a * b) + (a + b) * (a + b) by ring,
      IsCoprime.add_mul_left_left_iff, IsCoprime.neg_left_iff]
    refine IsCoprime.mul_left ?_ ?_
    · simpa [add_comm] using h.add_mul_left_right 1
    · simpa [add_comm] using h.symm.add_mul_left_right 1

/-- If `(p : R) ^ e p` divides `z` for each prime `p` in a finite set `P`, then so does the product
`∏ p ∈ P, (p : R) ^ e p`: distinct primes give pairwise coprime prime powers. -/
theorem Finset.prod_primes_pow_dvd {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) {z : R} (h : ∀ p ∈ P, (p : R) ^ e p ∣ z) :
    ∏ p ∈ P, (p : R) ^ e p ∣ z :=
  Finset.prod_dvd_of_coprime (fun p hp q hq hpq =>
    (((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq).cast).pow) h
