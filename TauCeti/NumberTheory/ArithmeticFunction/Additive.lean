/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Basic.Real.Basic

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

With the normalization at one, the coprime law also holds when a factor is zero
(`ArithmeticFunction.IsAdditive.map_mul_of_coprime`), so additive functions turn pairwise coprime
finite products into sums (`ArithmeticFunction.IsAdditive.map_prod`). Mathlib's
`Nat.multiplicative_factorization'`, applied through `Multiplicative A`, gives the prime-power
representation
`f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`
(`ArithmeticFunction.IsAdditive.apply_eq_sum_primeFactors_pow`), which holds at zero as an empty
sum.

`ArithmeticFunction.IsStronglyAdditive` adds the clause `f (p ^ k) = f p` for primes `p` and
`k ≠ 0`. A strongly additive function is the distinct-prime sum
`f n = ∑ p ∈ n.primeFactors, f p`
(`ArithmeticFunction.IsStronglyAdditive.apply_eq_sum_primeFactors`).
Native `ω` is strongly additive and native `Ω` is additive but not strongly additive. Casting a
natural-valued function into an additive monoid with one preserves additivity and strong
additivity, so the real casts of `ω` and `Ω` inherit these properties.

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on
  unit fractions*, J. Aust. Math. Soc. 94 (2013), 50–105, Appendix A, Lemmas A.2 and A.3
  (additive and strongly additive functions).

The induction in `ArithmeticFunction.IsAdditive.map_prod` follows Mathlib's
`ArithmeticFunction.IsMultiplicative.map_prod`.
-/

public section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

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
  IsAdditive.isMultiplicative_powOfAdditive
    { map_one := cardDistinctFactors_one, map_mul := fun _ _ h => cardDistinctFactors_mul h } k

/-- The arithmetic function `n ↦ k ^ ω n` is Mathlib's product over prime factors of the constant
function `k`, for a commutative base. -/
theorem powOfAdditive_cardDistinctFactors_eq_prodPrimeFactors {S : Type*} [CommMonoidWithZero S]
    (k : S) : powOfAdditive k cardDistinctFactors = prodPrimeFactors fun _ => k := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, prodPrimeFactors_apply hn, cardDistinctFactors_eq_card_primeFactors]

end powOfAdditive

section AddZeroClass

variable {A : Type*} [AddZeroClass A] {f : ArithmeticFunction A}

/-- The zero arithmetic function is additive. -/
theorem isAdditive_zero : IsAdditive (0 : ArithmeticFunction A) :=
  ⟨⟨fun _ _ _ => by simp⟩, by simp⟩

/-- An additive function adds on every coprime product. The positivity guards of the defining
law are unnecessary: a coprime product with a zero factor is `0 * 1` or `1 * 0`, and both sides
vanish there. -/
theorem IsAdditive.map_mul_of_coprime (hf : IsAdditive f) {m n : ℕ} (h : m.Coprime n) :
    f (m * n) = f m + f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [(Nat.coprime_zero_left _).1 h, hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [(Nat.coprime_zero_right _).1 h, hf.map_one]
  exact hf.map_mul hm hn h

end AddZeroClass

section AddCommMonoid

variable {A : Type*} [AddCommMonoid A] {f g : ArithmeticFunction A}

/-- The pointwise sum of two functions satisfying the coprime-product law satisfies it. -/
theorem IsAdditiveOnCoprime.add (hf : IsAdditiveOnCoprime f) (hg : IsAdditiveOnCoprime g) :
    IsAdditiveOnCoprime (f + g) where
  map_mul hm hn hmn := by
    simp only [add_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn, add_add_add_comm]

/-- The pointwise sum of two additive functions is additive. -/
theorem IsAdditive.add (hf : IsAdditive f) (hg : IsAdditive g) : IsAdditive (f + g) :=
  ⟨hf.toIsAdditiveOnCoprime.add hg.toIsAdditiveOnCoprime, by simp [hf.map_one, hg.map_one]⟩

open Function in
/-- An additive function sends a product of pairwise coprime natural numbers to the sum of its
values at the factors. -/
theorem IsAdditive.map_prod {ι : Type*} (g : ι → ℕ) (hf : IsAdditive f) (s : Finset ι)
    (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert _ _ has ih =>
    rw [Finset.coe_insert, Set.pairwise_insert_of_symm] at hs
    rw [Finset.prod_insert has, Finset.sum_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.Coprime.prod_right fun i hi => hs.2 _ hi (ne_of_mem_of_not_mem hi has).symm

/-- **Prime-power representation**: an additive function is the sum of its values at the prime
powers exactly dividing the input. At `n = 0` and `n = 1` both sides vanish. -/
theorem IsAdditive.apply_eq_sum_primeFactors_pow (hf : IsAdditive f) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  have := Nat.multiplicative_factorization' (n := n) (β := Multiplicative A)
    (fun n => Multiplicative.ofAdd (f n)) (fun x y h => by simp [hf.map_mul_of_coprime h])
    (by simp) (by simp [hf.map_one])
  simpa [Finsupp.prod, Nat.support_factorization] using congrArg Multiplicative.toAdd this

end AddCommMonoid

/-- Casting a natural-valued additive function into an additive monoid with one, such as `ℝ`,
preserves additivity. -/
theorem IsAdditive.natCast {R : Type*} [AddMonoidWithOne R] {f : ArithmeticFunction ℕ}
    (hf : IsAdditive f) : IsAdditive (f : ArithmeticFunction R) :=
  ⟨⟨fun hm hn hmn => by simp [hf.map_mul hm hn hmn]⟩, by simp [hf.map_one]⟩

/-- Native `ω`, the number of distinct prime factors, is additive. -/
theorem isAdditive_cardDistinctFactors : IsAdditive ω :=
  ⟨⟨fun _ _ h => cardDistinctFactors_mul h⟩, cardDistinctFactors_one⟩

/-- Native `Ω`, the number of prime factors counted with multiplicity, is additive. -/
theorem isAdditive_cardFactors : IsAdditive Ω :=
  ⟨⟨fun hm hn _ => cardFactors_mul hm hn⟩, cardFactors_one⟩

/-- A strongly additive arithmetic function is additive and takes the same value at every
positive power of a prime as at the prime itself. -/
structure IsStronglyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditive f where
  /-- The value at a positive prime power is the value at the prime. -/
  map_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

section StronglyAdditive

variable {A : Type*}

/-- The zero arithmetic function is strongly additive. -/
theorem isStronglyAdditive_zero [AddZeroClass A] : IsStronglyAdditive (0 : ArithmeticFunction A) :=
  ⟨isAdditive_zero, fun _ _ => by simp⟩

/-- The pointwise sum of two strongly additive functions is strongly additive. -/
theorem IsStronglyAdditive.add [AddCommMonoid A] {f g : ArithmeticFunction A}
    (hf : IsStronglyAdditive f) (hg : IsStronglyAdditive g) : IsStronglyAdditive (f + g) :=
  ⟨hf.toIsAdditive.add hg.toIsAdditive, fun hp hk => by
    simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]⟩

/-- **Distinct-prime representation**: a strongly additive function is the sum of its values at
the distinct prime divisors of the input. At `n = 0` and `n = 1` both sides vanish. -/
theorem IsStronglyAdditive.apply_eq_sum_primeFactors [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsStronglyAdditive f) (n : ℕ) : f n = ∑ p ∈ n.primeFactors, f p := by
  rw [hf.toIsAdditive.apply_eq_sum_primeFactors_pow]
  refine Finset.sum_congr rfl fun p hp => hf.map_prime_pow (Nat.prime_of_mem_primeFactors hp) ?_
  exact (Finsupp.mem_support_iff.1 (Nat.support_factorization n ▸ hp))

/-- Casting a natural-valued strongly additive function into an additive monoid with one, such as
`ℝ`, preserves strong additivity. -/
theorem IsStronglyAdditive.natCast {R : Type*} [AddMonoidWithOne R] {f : ArithmeticFunction ℕ}
    (hf : IsStronglyAdditive f) : IsStronglyAdditive (f : ArithmeticFunction R) :=
  ⟨hf.toIsAdditive.natCast, fun hp hk => by simp [hf.map_prime_pow hp hk]⟩

end StronglyAdditive

/-- Native `ω` is strongly additive: every positive prime power has exactly one prime factor. -/
theorem isStronglyAdditive_cardDistinctFactors : IsStronglyAdditive ω :=
  ⟨isAdditive_cardDistinctFactors, fun hp hk => by
    rw [cardDistinctFactors_apply_prime_pow hp hk, cardDistinctFactors_apply_prime hp]⟩

/-! ### Examples -/

/-- The real casts of `ω` and `Ω` are additive. -/
example : IsAdditive (ω : ArithmeticFunction ℝ) ∧ IsAdditive (Ω : ArithmeticFunction ℝ) :=
  ⟨isAdditive_cardDistinctFactors.natCast, isAdditive_cardFactors.natCast⟩

/-- The real cast of `ω` is strongly additive. -/
example : IsStronglyAdditive (ω : ArithmeticFunction ℝ) :=
  isStronglyAdditive_cardDistinctFactors.natCast

/-- `Ω` is not strongly additive: `Ω 4 = 2` while `Ω 2 = 1`. -/
example : ¬ IsStronglyAdditive Ω := fun h => by
  have h4 := h.map_prime_pow Nat.prime_two (k := 2) two_ne_zero
  rw [cardFactors_apply_prime_pow Nat.prime_two, cardFactors_apply_prime Nat.prime_two] at h4
  omega

/-- The convolution unit takes the value `1` at `1`, so it is not additive. -/
example : ¬ IsAdditive (1 : ArithmeticFunction ℝ) := fun h => by
  simpa using h.map_one

/-- Over `ℕ∞`, the function equal to `⊤` at every positive input satisfies the coprime law, since
`⊤ = ⊤ + ⊤`, but it is not additive because its value at one is `⊤`. -/
example : ∃ f : ArithmeticFunction ℕ∞, IsAdditiveOnCoprime f ∧ ¬ IsAdditive f := by
  refine ⟨⟨fun n => if n = 0 then 0 else ⊤, by simp⟩, ⟨fun hm hn _ => ?_⟩, fun h => ?_⟩
  · simp [hm, hn]
  · simpa using h.map_one

end ArithmeticFunction
