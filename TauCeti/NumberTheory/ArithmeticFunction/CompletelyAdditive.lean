/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Additive

/-!
# Completely additive arithmetic functions and powers of additive functions

`ArithmeticFunction.IsCompletelyAdditive f` says that `f 1 = 0` and `f (m * n) = f m + f n` for
all positive `m` and `n`. The value at one is part of the definition, since `f 1 = f 1 + f 1` does
not force `f 1 = 0` in an additive monoid without cancellation. The positive-input guards are
needed because the value at zero is zero in Mathlib's `ArithmeticFunction`. A completely additive
function is additive, satisfies `f (n ^ k) = k • f n` for positive `n`, and is determined by its
values at primes through the factorization formula
`f n = ∑ p ∈ n.primeFactors, n.factorization p • f p`. Mathlib's `Ω` is completely additive.

`ArithmeticFunction.powOfAdditive k f`, the arithmetic function with value `k ^ f n` at every
positive `n`, is defined in `TauCeti.NumberTheory.ArithmeticFunction.Additive`, where it is shown
to be multiplicative when `f` is additive, together with the case `n ↦ k ^ ω n`. Here it is
multiplicative on all pairs of inputs when `f` is completely additive, as for `n ↦ k ^ Ω n`; the
statement as a completely multiplicative function is
`ArithmeticFunction.IsCompletelyAdditive.isCompletelyMultiplicative_powOfAdditive` in
`TauCeti.NumberTheory.ArithmeticFunction.CompletelyMultiplicative`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 1.
-/

public section

namespace ArithmeticFunction

/-- A completely additive arithmetic function has value zero at one and adds on all positive
products. -/
structure IsCompletelyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) :
    Prop where
  /-- The value at one vanishes. -/
  map_one : f 1 = 0
  /-- Values add on positive products. -/
  map_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

attribute [simp] IsCompletelyAdditive.map_one

namespace IsCompletelyAdditive

variable {A : Type*}

/-- A completely additive function is additive. -/
theorem isAdditive [Zero A] [Add A] {f : ArithmeticFunction A} (hf : IsCompletelyAdditive f) :
    IsAdditive f where
  map_one := hf.map_one
  map_mul hm hn _ := hf.map_mul hm hn

/-- A completely additive function sends a positive power `n ^ k` to `k • f n`. -/
theorem map_pow [AddMonoid A] {f : ArithmeticFunction A} (hf : IsCompletelyAdditive f) {n : ℕ}
    (hn : n ≠ 0) (k : ℕ) : f (n ^ k) = k • f n := by
  induction k with
  | zero => simp [hf]
  | succ k ih => rw [pow_succ, hf.map_mul (pow_ne_zero k hn) hn, ih, succ_nsmul]

/-- A completely additive function sends a product of positive factors to the sum of its values
on the factors. -/
theorem map_prod {ι : Type*} [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsCompletelyAdditive f) (g : ι → ℕ) (s : Finset ι) (hg : ∀ i ∈ s, g i ≠ 0) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, g j ≠ 0 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      hf.map_mul (hg i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.2 hs), ih hs]

/-- **Factorization formula**: a completely additive function is the sum of its values at the
prime factors of its argument, weighted by their multiplicities. At `n = 0` and `n = 1` both
sides vanish. -/
theorem apply_eq_sum_primeFactors [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsCompletelyAdditive f) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, n.factorization p • f p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  rw [hf.map_prod _ _ fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero]
  exact Finset.sum_congr rfl fun p hp => hf.map_pow (Nat.prime_of_mem_primeFactors hp).ne_zero _

/-- Two completely additive functions are equal if and only if they agree at every prime. -/
theorem eq_iff_eq_on_primes [AddCommMonoid A] {f g : ArithmeticFunction A}
    (hf : IsCompletelyAdditive f) (hg : IsCompletelyAdditive g) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h p _ => h ▸ rfl, fun h => ?_⟩
  ext n
  rw [hf.apply_eq_sum_primeFactors, hg.apply_eq_sum_primeFactors]
  exact Finset.sum_congr rfl fun p hp => by rw [h p (Nat.prime_of_mem_primeFactors hp)]

/-- The pointwise sum of completely additive functions is completely additive. -/
theorem add [AddCommMonoid A] {f g : ArithmeticFunction A} (hf : IsCompletelyAdditive f)
    (hg : IsCompletelyAdditive g) : IsCompletelyAdditive (f + g) where
  map_one := by simp [hf, hg]
  map_mul hm hn := by simp [hf.map_mul hm hn, hg.map_mul hm hn, add_add_add_comm]

/-- Casting a natural-valued completely additive function preserves complete additivity. -/
theorem natCast [AddMonoidWithOne A] {f : ArithmeticFunction ℕ} (hf : IsCompletelyAdditive f) :
    IsCompletelyAdditive (f : ArithmeticFunction A) where
  map_one := by simp [hf]
  map_mul hm hn := by simp [hf.map_mul hm hn]

end IsCompletelyAdditive

/-- The zero arithmetic function is completely additive. -/
theorem isCompletelyAdditive_zero {A : Type*} [AddZeroClass A] :
    IsCompletelyAdditive (0 : ArithmeticFunction A) where
  map_one := by simp
  map_mul _ _ := by simp

/-- Mathlib's `Ω`, the number of prime factors counted with multiplicity, is completely
additive. -/
theorem isCompletelyAdditive_cardFactors : IsCompletelyAdditive cardFactors where
  map_one := cardFactors_one
  map_mul := cardFactors_mul

section powOfAdditive

variable {R : Type*} [MonoidWithZero R]

/-- Powers along a completely additive function are multiplicative on all pairs of inputs, with
no coprimality hypothesis. -/
theorem IsCompletelyAdditive.powOfAdditive_mul {f : ArithmeticFunction ℕ}
    (hf : IsCompletelyAdditive f) (k : R) (m n : ℕ) :
    powOfAdditive k f (m * n) = powOfAdditive k f m * powOfAdditive k f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, hf.map_mul hm hn, pow_add]

end powOfAdditive

end ArithmeticFunction
