/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Additive and strongly additive arithmetic functions

`ArithmeticFunction.IsAdditiveOnCoprime` is the positive coprime-product law alone. It does not
require the value at one to vanish: with a noncancellative target, that value may be a nonzero
additive idempotent. `ArithmeticFunction.IsAdditive` includes the normalization at one. With the
usual additive zero laws, left cancellation makes the two conditions agree
(`ArithmeticFunction.IsAdditiveOnCoprime.isAdditive`,
`ArithmeticFunction.isAdditive_iff_isAdditiveOnCoprime`). The predicates need only zero and
addition; no associativity or commutativity is imposed.

Both predicates use Mathlib's `ArithmeticFunction`, so the value at zero is zero. The weak coprime
law retains positive-input guards. For `AddZeroClass` targets, its instance at zero and one would
force normalization, and an unrestricted complete product-to-sum law at zero would force every
value to zero. The weak relation and the motivating exponentiation consequence come from Arend
Mellendijk's PNT+ Iwaniec–Kowalski Chapter 1 formalization.

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
finite products into sums (`ArithmeticFunction.IsAdditive.map_prod`) and are uniquely determined by
their values at positive prime powers (`ArithmeticFunction.IsAdditive.eq_iff_eq_on_prime_powers`).
Mathlib's `Nat.multiplicative_factorization'`, applied through `Multiplicative A`, gives the
prime-power representation
`f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`
(`ArithmeticFunction.IsAdditive.apply_eq_sum_primeFactors_pow`), which holds at zero as an empty
sum and yields `f (x.lcm y) + f (x.gcd y) = f x + f y`
(`ArithmeticFunction.IsAdditive.lcm_apply_add_gcd_apply`).

`ArithmeticFunction.IsStronglyAdditive` adds the clause `f (p ^ k) = f p` for primes `p` and
`k ≠ 0`. A strongly additive function is the distinct-prime sum
`f n = ∑ p ∈ n.primeFactors, f p`
(`ArithmeticFunction.IsStronglyAdditive.apply_eq_sum_primeFactors`) and is uniquely determined by
its values on primes (`ArithmeticFunction.IsStronglyAdditive.eq_iff_eq_on_primes`). Native `ω` is
strongly additive and native `Ω` is additive but not strongly additive. Both predicates are closed
under post-composition with additive monoid homomorphisms (`of_eq_addMonoidHom`), scalar
multiplication (`smul`), `ℕ`- and `ℤ`-casts (`natCast`, `intCast`), pointwise sums (`add`,
`isAdditive_sum`, `isStronglyAdditive_sum`), negation (`neg`), and subtraction (`sub`).

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on
  unit fractions*, J. Aust. Math. Soc. 94 (2013), 50–105, Appendix A, Lemmas A.2 and A.3
  (additive and strongly additive functions).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §1.2.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.1.
* Arend Mellendijk, Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*,
  `PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean` (Apache-2.0, revision
  `127b50e33f6033e2147921167a117af96d9ba4ea`), from which the weak coprime-product relation and the
  motivating exponentiation consequence originate.
* `Mathlib.NumberTheory.ArithmeticFunction.Defs` (`ArithmeticFunction.IsMultiplicative`), from
  whose `iff_ne_zero`, `map_prod`, `map_prod_of_prime`, `map_prod_of_subset_primeFactors`,
  `eq_iff_eq_on_prime_powers`, `lcm_apply_mul_gcd_apply`, and `map_div_of_coprime` the corresponding
  `IsAdditive` lemmas are adapted.
-/

public section

open Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace ArithmeticFunction

/-! ### Additive arithmetic functions -/

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

attribute [simp, grind =] IsAdditive.map_one

/-- Left cancellation forces the value at one to vanish, so the coprime-product law is normalized.
No associativity or commutativity of addition is needed. -/
theorem IsAdditiveOnCoprime.isAdditive {A : Type*} [AddZeroClass A] [IsLeftCancelAdd A]
    {f : ArithmeticFunction A} (hf : IsAdditiveOnCoprime f) : IsAdditive f := by
  refine ⟨hf, ?_⟩
  have h : f 1 + 0 = f 1 + f 1 := by
    simpa using hf.map_mul one_ne_zero one_ne_zero (Nat.coprime_one_left 1)
  exact (add_left_cancel h).symm

/-- Under left-cancellative addition with zero laws, `IsAdditive` and `IsAdditiveOnCoprime`
coincide. -/
theorem isAdditive_iff_isAdditiveOnCoprime {A : Type*} [AddZeroClass A] [IsLeftCancelAdd A]
    {f : ArithmeticFunction A} : f.IsAdditive ↔ f.IsAdditiveOnCoprime :=
  ⟨fun hf ↦ hf.toIsAdditiveOnCoprime, IsAdditiveOnCoprime.isAdditive⟩

/-- In a codomain with left-cancellative addition, the coprime product law on nonzero inputs
already forces `f 1 = 0` via `f 1 = f (1 * 1) = f 1 + f 1`. -/
theorem isAdditive_iff_of_isLeftCancelAdd {A : Type*} [AddZeroClass A] [IsLeftCancelAdd A]
    {f : ArithmeticFunction A} :
    f.IsAdditive ↔ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ hf.map_mul, fun h ↦ IsAdditiveOnCoprime.isAdditive ⟨h⟩⟩

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

section ZeroAdd

variable {A : Type*} [Zero A] [Add A] {f : ArithmeticFunction A}

/-- Characterization of `IsAdditive` as a conjunction of vanishing at `1` and coprime additivity
on nonzero inputs. -/
theorem IsAdditive.iff_ne_zero :
    f.IsAdditive ↔
      f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, hf.map_mul⟩, fun ⟨h1, hmul⟩ ↦ ⟨⟨hmul⟩, h1⟩⟩

/-- Two additive arithmetic functions are equal if and only if they agree at every prime power
`p ^ k` with `p` prime and `k ≠ 0`. -/
theorem IsAdditive.eq_iff_eq_on_prime_powers {g : ArithmeticFunction A} (hf : f.IsAdditive)
    (hg : g.IsAdditive) :
    f = g ↔ ∀ p k : ℕ, p.Prime → k ≠ 0 → f (p ^ k) = g (p ^ k) := by
  refine ⟨fun h _ _ _ _ ↦ h ▸ rfl, fun h ↦ ext fun n ↦ ?_⟩
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => rw [hf.map_one, hg.map_one]
  | prime_pow p k hp hk => exact h p k hp hk.ne'
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
    have hb0 : b ≠ 0 := (zero_lt_one.trans hb).ne'
    rw [hf.map_mul ha0 hb0 hab, hg.map_mul ha0 hb0 hab, iha, ihb]

end ZeroAdd

section AddZeroClass

variable {A : Type*} [AddZeroClass A] {f : ArithmeticFunction A}

/-- The zero arithmetic function is additive. -/
@[simp, grind .]
theorem isAdditive_zero : IsAdditive (0 : ArithmeticFunction A) :=
  ⟨⟨fun _ _ _ => by simp⟩, by simp⟩

/-- An additive function adds on every coprime product. The positivity guards of the defining
law are unnecessary: a coprime product with a zero factor is `0 * 1` or `1 * 0`, and both sides
vanish there. -/
@[grind =]
theorem IsAdditive.map_mul_of_coprime (hf : IsAdditive f) {m n : ℕ} (h : m.Coprime n) :
    f (m * n) = f m + f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [(Nat.coprime_zero_left _).1 h, hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [(Nat.coprime_zero_right _).1 h, hf.map_one]
  exact hf.map_mul hm hn h

/-- Characterization of `IsAdditive` using coprimality on all of `ℕ`, matching the shape of
`ArithmeticFunction.IsMultiplicative`. -/
theorem IsAdditive.iff_coprime :
    f.IsAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, fun hmn ↦ hf.map_mul_of_coprime hmn⟩,
    fun ⟨h1, h⟩ ↦ ⟨⟨fun _ _ hmn ↦ h hmn⟩, h1⟩⟩

/-- Post-composing an additive arithmetic function on nonzero inputs with an additive monoid
homomorphism preserves additivity. -/
theorem IsAdditive.of_eq_addMonoidHom {S F : Type*} [AddZeroClass S] [FunLike F A S]
    [AddMonoidHomClass F A S] (hf : f.IsAdditive) (φ : F) {g : ArithmeticFunction S}
    (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsAdditive where
  map_mul {m n} hm hn hmn := by
    rw [hg (m * n) (mul_ne_zero hm hn), hg m hm, hg n hn, hf.map_mul hm hn hmn, _root_.map_add φ]
  map_one := by rw [hg 1 one_ne_zero, hf.map_one, _root_.map_zero φ]

/-- Pointwise scalar multiplication by a distributive action preserves additivity. -/
@[grind ←]
theorem IsAdditive.smul {S : Type*} [DistribSMul S A] (hf : f.IsAdditive) (c : S) :
    (c • f).IsAdditive where
  map_mul hm hn hmn := by simp [hf.map_mul hm hn hmn, smul_add]
  map_one := by simp [hf.map_one]

end AddZeroClass

section AddCommMonoid

variable {A : Type*} [AddCommMonoid A] {f g : ArithmeticFunction A}

/-- The pointwise sum of two functions satisfying the coprime-product law satisfies it. -/
theorem IsAdditiveOnCoprime.add (hf : IsAdditiveOnCoprime f) (hg : IsAdditiveOnCoprime g) :
    IsAdditiveOnCoprime (f + g) where
  map_mul hm hn hmn := by
    simp only [add_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn, add_add_add_comm]

/-- The pointwise sum of two additive functions is additive. -/
@[grind ←]
theorem IsAdditive.add (hf : IsAdditive f) (hg : IsAdditive g) : IsAdditive (f + g) :=
  ⟨hf.toIsAdditiveOnCoprime.add hg.toIsAdditiveOnCoprime, by simp [hf.map_one, hg.map_one]⟩

/-- A finite pointwise sum of additive arithmetic functions is additive. -/
theorem isAdditive_sum {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction A)
    (hf : ∀ i ∈ s, (f i).IsAdditive) : (∑ i ∈ s, f i).IsAdditive :=
  Finset.sum_induction f IsAdditive (fun _ _ ↦ .add) isAdditive_zero hf

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

/-- An additive function converts a product of distinct primes into the sum of its values at those
primes. -/
theorem IsAdditive.map_prod_of_prime (hf : f.IsAdditive) (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod id t fun _ hx _ hy hxy ↦ (Nat.coprime_primes (ht _ hx) (ht _ hy)).mpr hxy

/-- An additive function converts a product over any subset of `n.primeFactors` into the sum of its
values. -/
theorem IsAdditive.map_prod_of_subset_primeFactors (hf : f.IsAdditive) (n : ℕ) (t : Finset ℕ)
    (ht : t ⊆ n.primeFactors) : f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod_of_prime t fun _ hp ↦ Nat.prime_of_mem_primeFactors (ht hp)

/-- On a squarefree natural number `n`, an additive function sums over `n.primeFactors` (note that
`Squarefree 0` is false and `Squarefree 1` gives the empty sum `f 1 = 0`). -/
theorem IsAdditive.apply_eq_sum_primeFactors_of_squarefree (hf : f.IsAdditive) {n : ℕ}
    (hn : Squarefree n) : f n = ∑ p ∈ n.primeFactors, f p := by
  rw [← hf.map_prod_of_subset_primeFactors n n.primeFactors Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hn]

/-- **Prime-power representation**: an additive function is the sum of its values at the prime
powers exactly dividing the input. At `n = 0` and `n = 1` both sides vanish. -/
theorem IsAdditive.apply_eq_sum_primeFactors_pow (hf : IsAdditive f) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  have := Nat.multiplicative_factorization' (n := n) (β := Multiplicative A)
    (fun n => Multiplicative.ofAdd (f n)) (fun x y h => by simp [hf.map_mul_of_coprime h])
    (by simp) (by simp [hf.map_one])
  simpa [Finsupp.prod, Nat.support_factorization] using congrArg Multiplicative.toAdd this

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply`: for
every `x, y : ℕ`, `f (x.lcm y) + f (x.gcd y) = f x + f y`. -/
theorem IsAdditive.lcm_apply_add_gcd_apply (hf : f.IsAdditive) (x y : ℕ) :
    f (x.lcm y) + f (x.gcd y) = f x + f y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hzero : ∀ p : ℕ, f (p ^ 0) = 0 := fun p ↦ by rw [pow_zero, hf.map_one]
  set s := x.primeFactors ∪ y.primeFactors
  have hexpand : ∀ {m : ℕ}, (∀ p ∈ m.primeFactors, p ∈ s) →
      f m = ∑ p ∈ s, f (p ^ m.factorization p) := fun {m} hsub ↦ by
    rw [hf.apply_eq_sum_primeFactors_pow]
    exact sum_subset hsub fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp (Nat.support_factorization m ▸ hp), hzero]
  rw [hexpand (by simp [s, Nat.factorization_lcm hx hy, ← Nat.support_factorization]),
    hexpand (fun p hp ↦ mem_union_left _
      (Nat.primeFactors_mono (Nat.gcd_dvd_left x y) hx hp)),
    hexpand (fun _ hp ↦ mem_union_left _ hp),
    hexpand (fun _ hp ↦ mem_union_right _ hp),
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  rcases le_total (x.factorization p) (y.factorization p) with h | h <;>
    simp [Nat.factorization_lcm hx hy, Nat.factorization_gcd hx hy, h, add_comm]

end AddCommMonoid

/-- Casting a natural-valued additive function into an additive monoid with one, such as `ℝ`,
preserves additivity. -/
@[grind ←]
theorem IsAdditive.natCast {R : Type*} [AddMonoidWithOne R] {f : ArithmeticFunction ℕ}
    (hf : IsAdditive f) : IsAdditive (f : ArithmeticFunction R) :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ by simp

/-- Coercing a `ℤ`-valued additive arithmetic function into an `AddGroupWithOne` preserves
additivity. -/
@[grind ←]
theorem IsAdditive.intCast {R : Type*} [AddGroupWithOne R] {f : ArithmeticFunction ℤ}
    (hf : f.IsAdditive) : (f : ArithmeticFunction R).IsAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ by simp

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.map_div_of_coprime`: if `d ∣ m`
and `m / d` is coprime to `d`, then `f (m / d) = f m - f d`. -/
theorem IsAdditive.map_div_of_coprime {R : Type*} [AddGroup R] {f : ArithmeticFunction R}
    (hf : f.IsAdditive) {m d : ℕ} (hdm : d ∣ m) (hc : (m / d).Coprime d) :
    f (m / d) = f m - f d :=
  eq_sub_of_add_eq <| by rw [← hf.map_mul_of_coprime hc, Nat.div_mul_cancel hdm]

/-- Pointwise negation preserves additivity. -/
@[grind ←]
theorem IsAdditive.neg {R : Type*} [SubtractionMonoid R] {f : ArithmeticFunction R}
    (hf : f.IsAdditive) : (-f).IsAdditive where
  map_mul hm hn hmn := by
    rw [neg_apply, mul_comm, hf.map_mul hn hm hmn.symm, neg_add_rev, neg_apply, neg_apply]
  map_one := by simp [hf.map_one]

/-- Pointwise subtraction preserves additivity. -/
@[grind ←]
theorem IsAdditive.sub {R : Type*} [SubtractionCommMonoid R] {f g : ArithmeticFunction R}
    (hf : f.IsAdditive) (hg : g.IsAdditive) : (f - g).IsAdditive where
  map_mul hm hn hmn := by
    simp only [sub_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_one := by simp [hf.map_one, hg.map_one]

/-- Native `ω`, the number of distinct prime factors, is additive. -/
@[simp, grind .]
theorem isAdditive_cardDistinctFactors : IsAdditive ω :=
  ⟨⟨fun _ _ h => cardDistinctFactors_mul h⟩, cardDistinctFactors_one⟩

/-- Native `Ω`, the number of prime factors counted with multiplicity, is additive. -/
@[simp, grind .]
theorem isAdditive_cardFactors : IsAdditive Ω :=
  ⟨⟨fun hm hn _ => cardFactors_mul hm hn⟩, cardFactors_one⟩

/-! ### Strongly additive arithmetic functions -/

/-- A strongly additive arithmetic function is additive and takes the same value at every
positive power of a prime as at the prime itself. -/
structure IsStronglyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditive f where
  /-- The value at a positive prime power is the value at the prime. -/
  map_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

attribute [grind =] IsStronglyAdditive.map_prime_pow
attribute [grind →] IsStronglyAdditive.toIsAdditive

section StronglyAdditive

variable {A : Type*}

/-- Unfolding characterization of `ArithmeticFunction.IsStronglyAdditive`. -/
theorem IsStronglyAdditive.iff_ne_zero [Zero A] [Add A] {f : ArithmeticFunction A} :
    f.IsStronglyAdditive ↔ f.IsAdditive ∧ ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p :=
  ⟨fun hf ↦ ⟨hf.toIsAdditive, hf.map_prime_pow⟩, fun ⟨hadd, hpow⟩ ↦ ⟨hadd, hpow⟩⟩

/-- Two strongly additive arithmetic functions are equal if and only if they agree on all primes. -/
theorem IsStronglyAdditive.eq_iff_eq_on_primes [Zero A] [Add A] {f g : ArithmeticFunction A}
    (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ (hf.toIsAdditive.eq_iff_eq_on_prime_powers
    hg.toIsAdditive).mpr fun p k hp hk ↦ ?_⟩
  rw [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk, h p hp]

/-- The zero arithmetic function is strongly additive. -/
@[simp, grind .]
theorem isStronglyAdditive_zero [AddZeroClass A] : IsStronglyAdditive (0 : ArithmeticFunction A) :=
  ⟨isAdditive_zero, fun _ _ => by simp⟩

/-- Post-composing a strongly additive arithmetic function on nonzero inputs with an additive
monoid homomorphism preserves strong additivity. -/
theorem IsStronglyAdditive.of_eq_addMonoidHom {S F : Type*} [AddZeroClass A] [AddZeroClass S]
    [FunLike F A S] [AddMonoidHomClass F A S] {f : ArithmeticFunction A}
    (hf : f.IsStronglyAdditive) (φ : F) {g : ArithmeticFunction S}
    (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.of_eq_addMonoidHom φ hg
  map_prime_pow {p k} hp hk := by
    rw [hg (p ^ k) (pow_ne_zero k hp.ne_zero), hg p hp.ne_zero, hf.map_prime_pow hp hk]

/-- Pointwise scalar multiplication by a distributive action preserves strong additivity. -/
@[grind ←]
theorem IsStronglyAdditive.smul {S : Type*} [AddZeroClass A] [DistribSMul S A]
    {f : ArithmeticFunction A} (hf : f.IsStronglyAdditive) (c : S) :
    (c • f).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.smul c
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk]

/-- The pointwise sum of two strongly additive functions is strongly additive. -/
@[grind ←]
theorem IsStronglyAdditive.add [AddCommMonoid A] {f g : ArithmeticFunction A}
    (hf : IsStronglyAdditive f) (hg : IsStronglyAdditive g) : IsStronglyAdditive (f + g) :=
  ⟨hf.toIsAdditive.add hg.toIsAdditive, fun hp hk => by
    simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]⟩

/-- A finite pointwise sum of strongly additive arithmetic functions is strongly additive. -/
theorem isStronglyAdditive_sum [AddCommMonoid A] {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction A) (hf : ∀ i ∈ s, (f i).IsStronglyAdditive) :
    (∑ i ∈ s, f i).IsStronglyAdditive :=
  Finset.sum_induction f IsStronglyAdditive (fun _ _ ↦ .add) isStronglyAdditive_zero hf

/-- **Distinct-prime representation**: a strongly additive function is the sum of its values at
the distinct prime divisors of the input. At `n = 0` and `n = 1` both sides vanish. -/
theorem IsStronglyAdditive.apply_eq_sum_primeFactors [AddCommMonoid A] {f : ArithmeticFunction A}
    (hf : IsStronglyAdditive f) (n : ℕ) : f n = ∑ p ∈ n.primeFactors, f p := by
  rw [hf.toIsAdditive.apply_eq_sum_primeFactors_pow]
  refine Finset.sum_congr rfl fun p hp => hf.map_prime_pow (Nat.prime_of_mem_primeFactors hp) ?_
  exact (Finsupp.mem_support_iff.1 (Nat.support_factorization n ▸ hp))

/-- Casting a natural-valued strongly additive function into an additive monoid with one, such as
`ℝ`, preserves strong additivity. -/
@[grind ←]
theorem IsStronglyAdditive.natCast {R : Type*} [AddMonoidWithOne R] {f : ArithmeticFunction ℕ}
    (hf : IsStronglyAdditive f) : IsStronglyAdditive (f : ArithmeticFunction R) :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ by simp

/-- Coercing a `ℤ`-valued strongly additive arithmetic function into an `AddGroupWithOne`
preserves strong additivity. -/
@[grind ←]
theorem IsStronglyAdditive.intCast {R : Type*} [AddGroupWithOne R] {f : ArithmeticFunction ℤ}
    (hf : f.IsStronglyAdditive) : (f : ArithmeticFunction R).IsStronglyAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ by simp

/-- Pointwise negation preserves strong additivity. -/
@[grind ←]
theorem IsStronglyAdditive.neg [SubtractionMonoid A] {f : ArithmeticFunction A}
    (hf : f.IsStronglyAdditive) : (-f).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.neg
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk]

/-- Pointwise subtraction preserves strong additivity. -/
@[grind ←]
theorem IsStronglyAdditive.sub [SubtractionCommMonoid A] {f g : ArithmeticFunction A}
    (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) : (f - g).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.sub hg.toIsAdditive
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]

end StronglyAdditive

/-- Native `ω` is strongly additive: every positive prime power has exactly one prime factor. -/
@[simp, grind .]
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
