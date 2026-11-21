/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Additive arithmetic functions and normalization

`ArithmeticFunction.IsAdditiveOnCoprime` is the positive coprime-product law alone. It does not
require the value at one to vanish: with a noncancellative target, that value may be a nonzero
additive idempotent. `ArithmeticFunction.IsAdditive` includes the normalization at one. With the
usual additive zero laws, left cancellation makes the two conditions agree. The predicates need
only zero and addition; no associativity or commutativity is imposed.

Both predicates use Mathlib's `ArithmeticFunction`, so the value at zero is zero. The weak coprime
law retains positive-input guards. For `AddZeroClass` targets, its instance at zero and one would
force normalization, and an unrestricted complete product-to-sum law at zero would force every
value to zero.
The weak relation and the motivating exponentiation consequence come from Arend Mellendijk's
PNT+ Iwaniec–Kowalski Chapter 1 formalization.

`ArithmeticFunction.IsAdditive.isMultiplicative_of_eq_monoidHom` sends a normalized additive
function through a monoid homomorphism from `Multiplicative A`. Its conclusion uses Mathlib's
multiplicative predicate, including the cases of zero inputs. Natural powers are a specialization
through Mathlib's `powersHom`: `ArithmeticFunction.powOfAdditive k f` has value `k ^ f n` at every
positive `n`, for `k` in a monoid with zero and a natural-valued `f`, and
`IsAdditive.isMultiplicative_powOfAdditive` shows it is multiplicative when `f` is additive.
In particular `n ↦ k ^ ω n` is multiplicative, and for a commutative base it is Mathlib's
`prodPrimeFactors` of the constant function `k`.

Complete additivity is in `TauCeti.NumberTheory.ArithmeticFunction.CompletelyAdditive`.

An additive function with values in an additive commutative monoid is determined by its values at
prime powers: `ArithmeticFunction.IsAdditive.apply_eq_sum_primeFactors` writes `f n` as the sum of
`f (p ^ n.factorization p)` over the prime factors `p` of `n`. A strongly additive function
(`ArithmeticFunction.IsStronglyAdditive`) also takes the value `f p` at each prime power `p ^ k`
with `k ≠ 0`, so `f n` is the sum of `f p` over the distinct prime factors of `n`
(`ArithmeticFunction.IsStronglyAdditive.apply_eq_sum_primeFactors`). Mathlib's `ω` is strongly
additive and Mathlib's `Ω` is additive; both remain so after casting.

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, J. Aust. Math. Soc. **94** (2013), Appendix A, Lemmas A.2 and A.3.
-/

public section

namespace ArithmeticFunction

/-- The additive law on positive coprime inputs, without normalization at one. -/
structure IsAdditiveOnCoprime {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop where
  /-- Values add on positive coprime products. -/
  map_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n

/-- A normalized additive arithmetic function has value zero at one and adds on positive
coprime products. -/
structure IsAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditiveOnCoprime f where
  /-- The value at one vanishes. -/
  map_one : f 1 = 0

attribute [simp] IsAdditive.map_one

/-- Left cancellation forces the value at one to vanish, so the coprime-product law is normalized.
No associativity or commutativity of addition is needed. -/
theorem IsAdditiveOnCoprime.isAdditive {A : Type*} [AddZeroClass A] [IsLeftCancelAdd A]
    {f : ArithmeticFunction A} (hf : IsAdditiveOnCoprime f) : IsAdditive f := by
  refine ⟨hf, ?_⟩
  have h : f 1 + 0 = f 1 + f 1 := by
    simpa using hf.map_mul one_ne_zero one_ne_zero (Nat.coprime_one_left 1)
  exact (add_left_cancel h).symm

/-- Applying a monoid homomorphism to the positive values of a normalized additive function
produces a multiplicative arithmetic function. The output's zero value is already part of its
arithmetic-function carrier. -/
theorem IsAdditive.isMultiplicative_of_eq_monoidHom {A R : Type*} [AddZeroClass A]
    [MonoidWithZero R] {f : ArithmeticFunction A} (hf : IsAdditive f)
    (φ : Multiplicative A →* R) {g : ArithmeticFunction R}
    (hg : ∀ n : ℕ, n ≠ 0 → g n = φ (Multiplicative.ofAdd (f n))) :
    g.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, ?_⟩
  · simpa [hf.map_one] using hg 1 one_ne_zero
  intro m n hm hn hmn
  rw [hg (m * n) (mul_ne_zero hm hn), hf.map_mul hm hn hmn,
    ofAdd_add, map_mul, hg m hm, hg n hn]

namespace IsAdditive

variable {A : Type*}

/-- An additive function adds on every coprime product. Positivity is not needed: if one factor is
zero, coprimality forces the other to be one, and both sides vanish, since the law at `1 * 1`
gives `0 = 0 + 0`. -/
theorem map_mul_of_coprime [Zero A] [Add A] {f : ArithmeticFunction A} (hf : IsAdditive f)
    {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m + f n := by
  have h0 : (0 : A) = 0 + 0 := by
    simpa [hf.map_one] using hf.map_mul one_ne_zero one_ne_zero (Nat.coprime_one_left 1)
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [(Nat.coprime_zero_left _).1 h, hf.map_one] using h0
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [(Nat.coprime_zero_right _).1 h, hf.map_one] using h0
  exact hf.map_mul hm hn h

open scoped Function in
/-- An additive function sends a product of pairwise coprime factors to the sum of its values on
the factors. -/
theorem map_prod {ι : Type*} [AddCommMonoid A] {f : ArithmeticFunction A} (hf : IsAdditive f)
    (g : ι → ℕ) (s : Finset ι) (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert _ _ has ih =>
    rw [Finset.coe_insert, Set.pairwise_insert_of_symm] at hs
    rw [Finset.prod_insert has, Finset.sum_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.Coprime.prod_right fun i hi => hs.2 _ hi (hi.ne_of_notMem has).symm

/-- **Prime-power representation**: an additive function is the sum of its values at the
prime-power parts of its argument. At `n = 0` and `n = 1` both sides vanish. -/
theorem apply_eq_sum_primeFactors [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsAdditive f) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  exact hf.map_prod _ _ fun p hp q hq hpq =>
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq |>.pow _ _

/-- The pointwise sum of additive functions is additive. -/
theorem add [AddCommMonoid A] {f g : ArithmeticFunction A} (hf : IsAdditive f)
    (hg : IsAdditive g) : IsAdditive (f + g) where
  map_one := by simp [hf, hg]
  map_mul hm hn h := by simp [hf.map_mul hm hn h, hg.map_mul hm hn h, add_add_add_comm]

/-- Casting a natural-valued additive function preserves additivity. -/
theorem natCast [AddMonoidWithOne A] {f : ArithmeticFunction ℕ} (hf : IsAdditive f) :
    IsAdditive (f : ArithmeticFunction A) where
  map_one := by simp [hf]
  map_mul hm hn h := by simp [hf.map_mul hm hn h]

end IsAdditive

/-- The zero arithmetic function is additive. -/
theorem isAdditive_zero {A : Type*} [AddZeroClass A] : IsAdditive (0 : ArithmeticFunction A) where
  map_one := rfl
  map_mul _ _ _ := by simp

/-- Mathlib's `Ω`, the number of prime factors counted with multiplicity, is additive. -/
theorem isAdditive_cardFactors : IsAdditive cardFactors where
  map_one := cardFactors_one
  map_mul hm hn _ := cardFactors_mul hm hn

/-- A strongly additive arithmetic function is additive and takes the same value at every positive
power of a prime as at the prime itself. -/
structure IsStronglyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditive f where
  /-- The value at a positive prime power is the value at the prime. -/
  map_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

namespace IsStronglyAdditive

variable {A : Type*}

/-- **Distinct-prime representation**: a strongly additive function is the sum of its values at
the distinct prime factors of its argument. At `n = 0` and `n = 1` both sides vanish. -/
theorem apply_eq_sum_primeFactors [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsStronglyAdditive f) (n : ℕ) : f n = ∑ p ∈ n.primeFactors, f p := by
  rw [hf.toIsAdditive.apply_eq_sum_primeFactors]
  refine Finset.sum_congr rfl fun p hp => hf.map_prime_pow (Nat.prime_of_mem_primeFactors hp) ?_
  rw [← Finsupp.mem_support_iff, Nat.support_factorization]
  exact hp

/-- The pointwise sum of strongly additive functions is strongly additive. -/
theorem add [AddCommMonoid A] {f g : ArithmeticFunction A} (hf : IsStronglyAdditive f)
    (hg : IsStronglyAdditive g) : IsStronglyAdditive (f + g) where
  toIsAdditive := hf.toIsAdditive.add hg.toIsAdditive
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]

/-- Casting a natural-valued strongly additive function preserves strong additivity. -/
theorem natCast [AddMonoidWithOne A] {f : ArithmeticFunction ℕ} (hf : IsStronglyAdditive f) :
    IsStronglyAdditive (f : ArithmeticFunction A) where
  toIsAdditive := hf.toIsAdditive.natCast
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk]

end IsStronglyAdditive

/-- The zero arithmetic function is strongly additive. -/
theorem isStronglyAdditive_zero {A : Type*} [AddZeroClass A] :
    IsStronglyAdditive (0 : ArithmeticFunction A) where
  toIsAdditive := isAdditive_zero
  map_prime_pow _ _ := rfl

/-- Mathlib's `ω`, the number of distinct prime factors, is strongly additive. -/
theorem isStronglyAdditive_cardDistinctFactors : IsStronglyAdditive cardDistinctFactors where
  map_one := cardDistinctFactors_one
  map_mul _ _ h := cardDistinctFactors_mul h
  map_prime_pow hp hk := by
    rw [cardDistinctFactors_apply_prime_pow hp hk, cardDistinctFactors_apply_prime hp]

section powOfAdditive

variable {R : Type*} [MonoidWithZero R]

/-- The arithmetic function with value `k ^ f n` at every positive `n`. Its value at zero is zero,
as for every arithmetic function, rather than `k ^ f 0 = 1`. -/
def powOfAdditive (k : R) (f : ArithmeticFunction ℕ) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else k ^ f n
  map_zero' := ite_eq_left rfl

@[simp]
theorem powOfAdditive_apply (k : R) (f : ArithmeticFunction ℕ) {n : ℕ} (hn : n ≠ 0) :
    powOfAdditive k f n = k ^ f n :=
  ite_eq_right hn

theorem powOfAdditive_apply_zero (k : R) (f : ArithmeticFunction ℕ) : powOfAdditive k f 0 = 0 :=
  map_zero

theorem powOfAdditive_apply_one (k : R) {f : ArithmeticFunction ℕ} (hf : f 1 = 0) :
    powOfAdditive k f 1 = 1 := by
  simp [hf]

/-- Powers along an additive function form a multiplicative arithmetic function. -/
theorem IsAdditive.isMultiplicative_powOfAdditive {f : ArithmeticFunction ℕ} (hf : IsAdditive f)
    (k : R) : (powOfAdditive k f).IsMultiplicative :=
  hf.isMultiplicative_of_eq_monoidHom (powersHom R k) fun n hn => by simp [hn]

/-- The arithmetic function `n ↦ k ^ ω n` is multiplicative. -/
theorem isMultiplicative_powOfAdditive_cardDistinctFactors (k : R) :
    (powOfAdditive k cardDistinctFactors).IsMultiplicative :=
  isStronglyAdditive_cardDistinctFactors.toIsAdditive.isMultiplicative_powOfAdditive k

/-- The arithmetic function `n ↦ k ^ ω n` is Mathlib's product over prime factors of the constant
function `k`, for a commutative base. -/
theorem powOfAdditive_cardDistinctFactors_eq_prodPrimeFactors {S : Type*} [CommMonoidWithZero S]
    (k : S) : powOfAdditive k cardDistinctFactors = prodPrimeFactors fun _ => k := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, prodPrimeFactors_apply hn, cardDistinctFactors_eq_card_primeFactors]

end powOfAdditive

end ArithmeticFunction
