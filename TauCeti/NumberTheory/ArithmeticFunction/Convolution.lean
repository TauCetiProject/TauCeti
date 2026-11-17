/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite Dirichlet-convolution products of arithmetic functions

This file provides finite-product companions to Mathlib's binary convolution lemmas on
`ArithmeticFunction R`:

* a finite Dirichlet-convolution product of multiplicative arithmetic functions is multiplicative;
* evaluating a finite product `(∏ i ∈ s, f i) n` depends only on the values of the factors `f i`
  at the nonzero divisors of `n`, and in particular `(∏ i ∈ s, f i) (p ^ k)` depends only on the
  values at prime powers `p ^ j` with `j ≤ k`.

## Main results

* `ArithmeticFunction.IsMultiplicative.finset_prod`: a finite product of multiplicative arithmetic
  functions is multiplicative.
* `ArithmeticFunction.finset_prod_apply_congr_of_dvd`: congruence of a finite Dirichlet-convolution
  product at `n` when the factors agree on all nonzero divisors of `n`.
* `ArithmeticFunction.finset_prod_apply_prime_pow_congr`: specialization to prime powers `p ^ k`.
-/

public section

namespace ArithmeticFunction

variable {ι R : Type*} [CommSemiring R]

/-- A finite Dirichlet-convolution product of multiplicative arithmetic functions is
multiplicative. -/
theorem IsMultiplicative.finset_prod {s : Finset ι} {f : ι → ArithmeticFunction R}
    (hf : ∀ i ∈ s, (f i).IsMultiplicative) :
    (∏ i ∈ s, f i).IsMultiplicative := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact isMultiplicative_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The value of a finite Dirichlet-convolution product at `n` depends only on the values of its
factors at nonzero divisors of `n`. -/
theorem finset_prod_apply_congr_of_dvd {s : Finset ι} {f g : ι → ArithmeticFunction R} {n : ℕ}
    (h : ∀ i ∈ s, ∀ d : ℕ, d ≠ 0 → d ∣ n → f i d = g i d) :
    (∏ i ∈ s, f i) n = (∏ i ∈ s, g i) n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ArithmeticFunction.mul_apply,
      ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have ⟨hx1, _⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
    have h1 : f a x.1 = g a x.1 :=
      h a (Finset.mem_insert_self a s) x.1 hx1 ⟨x.2, hprod.symm⟩
    have h2 : (∏ i ∈ s, f i) x.2 = (∏ i ∈ s, g i) x.2 :=
      ih fun i hi d hd0 hdx ↦
        h i (Finset.mem_insert_of_mem hi) d hd0 (hdx.trans ⟨x.1, by rw [mul_comm, hprod]⟩)
    rw [h1, h2]

/-- The value of a finite Dirichlet-convolution product at a prime power `p ^ k` depends only on
the values of its factors at `p ^ j` for `j ≤ k`. -/
theorem finset_prod_apply_prime_pow_congr {s : Finset ι} {f g : ι → ArithmeticFunction R}
    {p k : ℕ} (hp : p.Prime)
    (h : ∀ i ∈ s, ∀ j ≤ k, f i (p ^ j) = g i (p ^ j)) :
    (∏ i ∈ s, f i) (p ^ k) = (∏ i ∈ s, g i) (p ^ k) := by
  refine finset_prod_apply_congr_of_dvd fun i hi d _ hdvd ↦ ?_
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact h i hi j hj

end ArithmeticFunction
