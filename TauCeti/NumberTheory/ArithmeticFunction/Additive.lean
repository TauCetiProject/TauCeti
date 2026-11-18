/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Additive, strongly additive, and completely additive arithmetic functions

`ArithmeticFunction.IsAdditiveOnCoprime` is the positive coprime-product law alone. It does not
require the value at one to vanish: with a noncancellative target, that value may be a nonzero
additive idempotent (for instance, in `ℕ∞`, the indicator sending positive integers to `⊤`).
`ArithmeticFunction.IsAdditive` includes the normalization `f 1 = 0`. With the usual additive zero
laws, left cancellation makes the two conditions agree
(`ArithmeticFunction.IsAdditiveOnCoprime.isAdditive`,
`ArithmeticFunction.isAdditive_iff_isAdditiveOnCoprime`). All predicates need only zero and
addition; no associativity or commutativity is imposed.

All four predicates use Mathlib's `ArithmeticFunction`, so the value at zero is zero. The weak
coprime law retains positive-input guards. For `AddZeroClass` targets, its instance at zero and one
would force normalization, and an unrestricted complete product-to-sum law at zero would force every
value to zero. However, since `0.Coprime n` holds only at `n = 1` where both `f 0` and `f 1` vanish,
coprime additivity of a normalized additive function automatically extends to all coprime pairs in
`ℕ` (`ArithmeticFunction.IsAdditive.map_mul_of_coprime`), and all prime-factorization expansions
hold unconditionally for every `n : ℕ` (including `n = 0` and `n = 1`).

`ArithmeticFunction.IsAdditive.isMultiplicative_of_eq_monoidHom` sends a normalized additive
function through a monoid homomorphism from `Multiplicative A`. Its conclusion uses Mathlib's
multiplicative predicate, including the cases of zero inputs. Natural powers are a specialization
through Mathlib's `powersHom`; the output's value at zero is supplied by its arithmetic carrier.

Two strengthenings of `ArithmeticFunction.IsAdditive` appear throughout probabilistic and analytic
number theory:

* **Strong additivity** (`ArithmeticFunction.IsStronglyAdditive`): `f` is additive and
  `f (p ^ k) = f p` for every prime `p` and nonzero exponent `k`, modeled on
  `ω = cardDistinctFactors`.
* **Complete additivity** (`ArithmeticFunction.IsCompletelyAdditive`): `f 1 = 0` and
  `f (m * n) = f m + f n` for all nonzero `m` and `n` without coprimality, modeled on
  `Ω = cardFactors`. Over an `AddZeroClass` target, a completely additive function corresponds to
  a unital monoid homomorphism `PNat →* Multiplicative A`, while retaining `ArithmeticFunction`'s
  zero-totalized carrier.

## Main definitions

* `ArithmeticFunction.IsAdditiveOnCoprime`: unnormalized additive arithmetic functions (coprime
  additivity on nonzero inputs).
* `ArithmeticFunction.IsAdditive`: normalized additive arithmetic functions (`f 1 = 0` and coprime
  additivity on nonzero inputs).
* `ArithmeticFunction.IsStronglyAdditive`: strongly additive arithmetic functions (`IsAdditive` and
  `f (p ^ k) = f p` for prime `p` and `k ≠ 0`).
* `ArithmeticFunction.IsCompletelyAdditive`: completely additive arithmetic functions (`f 1 = 0`
  and `f (m * n) = f m + f n` on all nonzero inputs).

## Main results

* `ArithmeticFunction.IsAdditiveOnCoprime.isAdditive`: under `[AddZeroClass A] [IsLeftCancelAdd A]`,
  `IsAdditiveOnCoprime f` implies `IsAdditive f`.
* `ArithmeticFunction.IsAdditive.isMultiplicative_of_eq_monoidHom`: composing a normalized additive
  function with a monoid homomorphism from `Multiplicative A` yields a multiplicative arithmetic
  function.
* `ArithmeticFunction.IsAdditive.sum_primeFactors_pow_factorization`: for additive `f` and every
  `n : ℕ`, `f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`.
* `ArithmeticFunction.IsAdditive.eq_iff_eq_on_prime_powers`: two additive functions are equal if
  and only if they agree on all prime powers `p ^ k` with `k ≠ 0`.
* `ArithmeticFunction.IsAdditive.lcm_apply_add_gcd_apply`: `f (x.lcm y) + f (x.gcd y) = f x + f y`.
* `ArithmeticFunction.IsStronglyAdditive.sum_primeFactors`,
  `ArithmeticFunction.IsStronglyAdditive.eq_iff_eq_on_primes`: distinct-prime expansion
  `f n = ∑ p ∈ n.primeFactors, f p` and determination by prime values for strongly additive
  functions.
* `ArithmeticFunction.IsCompletelyAdditive.map_pow`,
  `ArithmeticFunction.IsCompletelyAdditive.sum_primeFactors`,
  `ArithmeticFunction.IsCompletelyAdditive.eq_iff_eq_on_primes`: power law `f (n ^ k) = k • f n`,
  multiplicity-weighted prime expansion `f n = ∑ p ∈ n.primeFactors, n.factorization p • f p`, and
  determination by prime values for completely additive functions.
* `ArithmeticFunction.isStronglyAdditive_cardDistinctFactors`,
  `ArithmeticFunction.isCompletelyAdditive_cardFactors`: strong additivity of `ω` and complete
  additivity of `Ω`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §1.2.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.1.
* Arend Mellendijk, Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*,
  `PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean` (Apache-2.0, revision
  `127b50e33f6033e2147921167a117af96d9ba4ea`), from which the weak coprime-product relation and the
  motivating exponentiation consequence originate.
* `Mathlib.NumberTheory.ArithmeticFunction.Defs` (`ArithmeticFunction.IsMultiplicative`), from
  whose `iff_ne_zero`, `map_prod`, `map_prod_of_prime`, `map_prod_of_subset_primeFactors`,
  `prod_primeFactors`, `eq_iff_eq_on_prime_powers`, `lcm_apply_mul_gcd_apply`, and
  `map_div_of_coprime` the corresponding `IsAdditive` lemmas are adapted.
-/

public section

open Finset

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

variable {R S : Type*}

/-- Under left-cancellative addition with zero laws, `IsAdditive` and `IsAdditiveOnCoprime`
coincide. -/
theorem isAdditive_iff_isAdditiveOnCoprime [AddZeroClass R] [IsLeftCancelAdd R]
    {f : ArithmeticFunction R} : f.IsAdditive ↔ f.IsAdditiveOnCoprime :=
  ⟨fun hf ↦ hf.toIsAdditiveOnCoprime, IsAdditiveOnCoprime.isAdditive⟩

/-- In a codomain with left-cancellative addition, the coprime product law on nonzero inputs
already forces `f 1 = 0` via `f 1 = f (1 * 1) = f 1 + f 1`. -/
theorem isAdditive_iff_of_isLeftCancelAdd [AddZeroClass R] [IsLeftCancelAdd R]
    {f : ArithmeticFunction R} :
    f.IsAdditive ↔ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ hf.map_mul, fun h ↦ IsAdditiveOnCoprime.isAdditive ⟨h⟩⟩

namespace IsAdditive

section ZeroAdd

variable [Zero R] [Add R] {f : ArithmeticFunction R}

/-- Characterization of `IsAdditive` as a conjunction of vanishing at `1` and coprime additivity
on nonzero inputs. -/
theorem iff_ne_zero :
    f.IsAdditive ↔
      f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, hf.map_mul⟩, fun ⟨h1, hmul⟩ ↦ ⟨⟨hmul⟩, h1⟩⟩

/-- Two additive arithmetic functions are equal if and only if they agree at every prime power
`p ^ k` with `p` prime and `k ≠ 0`. -/
theorem eq_iff_eq_on_prime_powers {g : ArithmeticFunction R} (hf : f.IsAdditive)
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

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- Additivity extends to all coprime pairs in `ℕ`: if one factor is `0`, coprimality forces the
other to be `1`, and both `f 0` and `f 1` vanish. Stated with `m.gcd n = 1` (definitionally
`m.Coprime n`) to match `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime` and `simp` normal
form. -/
@[simp, grind =]
theorem map_mul_of_coprime (hf : f.IsAdditive) {m n : ℕ} (hmn : m.gcd n = 1) :
    f (m * n) = f m + f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · obtain rfl : n = 1 := Nat.coprime_zero_left n |>.mp hmn
    simp [hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : m = 1 := Nat.coprime_zero_right m |>.mp hmn
    simp [hf.map_one]
  exact hf.map_mul hm hn hmn

/-- Characterization of `IsAdditive` using coprimality on all of `ℕ`, matching the shape of
`ArithmeticFunction.IsMultiplicative`. -/
theorem iff_coprime :
    f.IsAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, fun hmn ↦ hf.map_mul_of_coprime hmn⟩,
    fun ⟨h1, h⟩ ↦ ⟨⟨fun _ _ hmn ↦ h hmn⟩, h1⟩⟩

/-- Post-composing an additive arithmetic function on nonzero inputs with an additive monoid
homomorphism preserves additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] {F : Type*} [FunLike F R S] [AddMonoidHomClass F R S]
    (hf : f.IsAdditive) (φ : F) {g : ArithmeticFunction S} (hg : ∀ n ≠ 0, g n = φ (f n)) :
    g.IsAdditive where
  map_mul {m n} hm hn hmn := by
    rw [hg (m * n) (mul_ne_zero hm hn), hg m hm, hg n hn, hf.map_mul hm hn hmn, _root_.map_add φ]
  map_one := by rw [hg 1 one_ne_zero, hf.map_one, _root_.map_zero φ]

/-- Pointwise scalar multiplication by a distributive action preserves additivity. -/
@[grind ←]
theorem smul [DistribSMul S R] (hf : f.IsAdditive) (c : S) : (c • f).IsAdditive where
  map_mul hm hn hmn := by simp [hf.map_mul hm hn hmn, smul_add]
  map_one := by simp [hf.map_one]

end AddZeroClass

/-- Coercing an `ℕ`-valued additive arithmetic function into an `AddMonoidWithOne` preserves
additivity. -/
@[grind ←]
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (f : ArithmeticFunction R).IsAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ by simp

/-- Coercing a `ℤ`-valued additive arithmetic function into an `AddGroupWithOne` preserves
additivity. -/
@[grind ←]
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsAdditive) :
    (f : ArithmeticFunction R).IsAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ by simp

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two additive arithmetic functions is additive. -/
@[grind ←]
theorem add (hf : f.IsAdditive) (hg : g.IsAdditive) : (f + g).IsAdditive where
  map_mul hm hn hmn := by
    simp only [add_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn]
    exact add_add_add_comm _ _ _ _
  map_one := by simp [hf.map_one, hg.map_one]

open scoped Function in
/-- An additive function converts the product of a pairwise coprime finite family into the sum of
its values. -/
theorem map_prod {ι : Type*} (g : ι → ℕ) (hf : f.IsAdditive) (s : Finset ι)
    (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert a s has ih =>
    rw [coe_insert, Set.pairwise_insert_of_symm] at hs
    rw [prod_insert has, sum_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.Coprime.prod_right fun i hi ↦ hs.2 i hi (ne_of_mem_of_not_mem hi has).symm

/-- An additive function converts a product of distinct primes into the sum of its values at those
primes. -/
theorem map_prod_of_prime (hf : f.IsAdditive) (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod id t fun _ hx _ hy hxy ↦ (Nat.coprime_primes (ht _ hx) (ht _ hy)).mpr hxy

/-- An additive function converts a product over any subset of `n.primeFactors` into the sum of its
values. -/
theorem map_prod_of_subset_primeFactors (hf : f.IsAdditive) (n : ℕ) (t : Finset ℕ)
    (ht : t ⊆ n.primeFactors) : f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod_of_prime t fun _ hp ↦ Nat.prime_of_mem_primeFactors (ht hp)

/-- On a squarefree natural number `n`, an additive function sums over `n.primeFactors` (note that
`Squarefree 0` is false and `Squarefree 1` gives the empty sum `f 1 = 0`). -/
theorem sum_primeFactors_of_squarefree (hf : f.IsAdditive) {n : ℕ} (hn : Squarefree n) :
    f n = ∑ p ∈ n.primeFactors, f p := by
  rw [← hf.map_prod_of_subset_primeFactors n n.primeFactors Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hn]

/-- **Prime-power representation of an additive arithmetic function.** For every `n : ℕ` (including
`0` and `1`), `f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`. -/
theorem sum_primeFactors_pow_factorization (hf : f.IsAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmult := Nat.multiplicative_factorization (fun m ↦ Multiplicative.ofAdd (f m))
    (fun _ _ hmn ↦ by simp [hf.map_mul_of_coprime hmn]) (by simp [hf.map_one]) hn
  simpa [Finsupp.prod, Nat.support_factorization] using congrArg Multiplicative.toAdd hmult

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply`: for
every `x, y : ℕ`, `f (x.lcm y) + f (x.gcd y) = f x + f y`. -/
theorem lcm_apply_add_gcd_apply (hf : f.IsAdditive) (x y : ℕ) :
    f (x.lcm y) + f (x.gcd y) = f x + f y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hzero : ∀ p : ℕ, f (p ^ 0) = 0 := fun p ↦ by rw [pow_zero, hf.map_one]
  set s := x.primeFactors ∪ y.primeFactors
  have hexpand : ∀ {m : ℕ}, (∀ p ∈ m.primeFactors, p ∈ s) →
      f m = ∑ p ∈ s, f (p ^ m.factorization p) := fun {m} hsub ↦ by
    rw [hf.sum_primeFactors_pow_factorization]
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

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.map_div_of_coprime`: if `d ∣ m`
and `m / d` is coprime to `d`, then `f (m / d) = f m - f d`. -/
theorem map_div_of_coprime [AddGroup R] {f : ArithmeticFunction R} (hf : f.IsAdditive)
    {m d : ℕ} (hdm : d ∣ m) (hc : (m / d).Coprime d) : f (m / d) = f m - f d :=
  eq_sub_of_add_eq <| by rw [← hf.map_mul_of_coprime hc, Nat.div_mul_cancel hdm]

/-- Pointwise negation preserves additivity. -/
@[grind ←]
theorem neg [SubtractionMonoid R] {f : ArithmeticFunction R} (hf : f.IsAdditive) :
    (-f).IsAdditive where
  map_mul hm hn hmn := by
    rw [neg_apply, mul_comm, hf.map_mul hn hm hmn.symm, neg_add_rev, neg_apply, neg_apply]
  map_one := by simp [hf.map_one]

/-- Pointwise subtraction preserves additivity. -/
@[grind ←]
theorem sub [SubtractionCommMonoid R] {f g : ArithmeticFunction R} (hf : f.IsAdditive)
    (hg : g.IsAdditive) : (f - g).IsAdditive where
  map_mul hm hn hmn := by
    simp only [sub_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_one := by simp [hf.map_one, hg.map_one]

end IsAdditive

/-- The zero arithmetic function is additive. -/
@[simp, grind .]
theorem isAdditive_zero [AddZeroClass R] : (0 : ArithmeticFunction R).IsAdditive where
  map_mul _ _ _ := by simp
  map_one := by simp

/-- A finite pointwise sum of additive arithmetic functions is additive. -/
theorem isAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction R)
    (hf : ∀ i ∈ s, (f i).IsAdditive) : (∑ i ∈ s, f i).IsAdditive :=
  Finset.sum_induction f IsAdditive (fun _ _ ↦ .add) isAdditive_zero hf

/-! ### Strongly additive arithmetic functions -/

/-- An arithmetic function `f` is **strongly additive** if it is additive and `f (p ^ k) = f p`
for every prime `p` and nonzero exponent `k`. -/
structure IsStronglyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditive f where
  /-- At every positive power of a prime `p`, a strongly additive function takes the value `f p`. -/
  map_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

attribute [simp, grind =] IsStronglyAdditive.map_prime_pow
attribute [grind →] IsStronglyAdditive.toIsAdditive

namespace IsStronglyAdditive

section ZeroAdd

variable [Zero R] [Add R] {f : ArithmeticFunction R}

/-- Unfolding characterization of `ArithmeticFunction.IsStronglyAdditive`. -/
theorem iff_ne_zero :
    f.IsStronglyAdditive ↔ f.IsAdditive ∧ ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p :=
  ⟨fun hf ↦ ⟨hf.toIsAdditive, hf.map_prime_pow⟩, fun ⟨hadd, hpow⟩ ↦ ⟨hadd, hpow⟩⟩

/-- Two strongly additive arithmetic functions are equal if and only if they agree on all primes. -/
theorem eq_iff_eq_on_primes {g : ArithmeticFunction R} (hf : f.IsStronglyAdditive)
    (hg : g.IsStronglyAdditive) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ (hf.toIsAdditive.eq_iff_eq_on_prime_powers
    hg.toIsAdditive).mpr fun p k hp hk ↦ ?_⟩
  rw [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk, h p hp]

end ZeroAdd

section AddZeroClass

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- Post-composing a strongly additive arithmetic function on nonzero inputs with an additive
monoid homomorphism preserves strong additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] {F : Type*} [FunLike F R S] [AddMonoidHomClass F R S]
    (hf : f.IsStronglyAdditive) (φ : F) {g : ArithmeticFunction S}
    (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.of_eq_addMonoidHom φ hg
  map_prime_pow {p k} hp hk := by
    rw [hg (p ^ k) (pow_ne_zero k hp.ne_zero), hg p hp.ne_zero, hf.map_prime_pow hp hk]

/-- Pointwise scalar multiplication by a distributive action preserves strong additivity. -/
@[grind ←]
theorem smul [DistribSMul S R] (hf : f.IsStronglyAdditive) (c : S) :
    (c • f).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.smul c
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk]

end AddZeroClass

/-- Coercing an `ℕ`-valued strongly additive arithmetic function into an `AddMonoidWithOne`
preserves strong additivity. -/
@[grind ←]
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsStronglyAdditive) :
    (f : ArithmeticFunction R).IsStronglyAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ by simp

/-- Coercing a `ℤ`-valued strongly additive arithmetic function into an `AddGroupWithOne`
preserves strong additivity. -/
@[grind ←]
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsStronglyAdditive) :
    (f : ArithmeticFunction R).IsStronglyAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ by simp

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two strongly additive arithmetic functions is strongly additive. -/
@[grind ←]
theorem add (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) :
    (f + g).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.add hg.toIsAdditive
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]

/-- **Distinct-prime representation of a strongly additive function.** For every `n : ℕ`
(including `0` and `1`), `f n = ∑ p ∈ n.primeFactors, f p`. -/
theorem sum_primeFactors (hf : f.IsStronglyAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f p := by
  rw [hf.toIsAdditive.sum_primeFactors_pow_factorization]
  refine sum_congr rfl fun p hp ↦ hf.map_prime_pow (Nat.prime_of_mem_primeFactors hp) ?_
  exact Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp)

end AddCommMonoid

/-- Pointwise negation preserves strong additivity. -/
@[grind ←]
theorem neg [SubtractionMonoid R] {f : ArithmeticFunction R} (hf : f.IsStronglyAdditive) :
    (-f).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.neg
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk]

/-- Pointwise subtraction preserves strong additivity. -/
@[grind ←]
theorem sub [SubtractionCommMonoid R] {f g : ArithmeticFunction R} (hf : f.IsStronglyAdditive)
    (hg : g.IsStronglyAdditive) : (f - g).IsStronglyAdditive where
  toIsAdditive := hf.toIsAdditive.sub hg.toIsAdditive
  map_prime_pow hp hk := by simp [hf.map_prime_pow hp hk, hg.map_prime_pow hp hk]

end IsStronglyAdditive

/-- The zero arithmetic function is strongly additive. -/
@[simp, grind .]
theorem isStronglyAdditive_zero [AddZeroClass R] :
    (0 : ArithmeticFunction R).IsStronglyAdditive where
  toIsAdditive := isAdditive_zero
  map_prime_pow _ _ := by simp

/-- A finite pointwise sum of strongly additive arithmetic functions is strongly additive. -/
theorem isStronglyAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction R) (hf : ∀ i ∈ s, (f i).IsStronglyAdditive) :
    (∑ i ∈ s, f i).IsStronglyAdditive :=
  Finset.sum_induction f IsStronglyAdditive (fun _ _ ↦ .add) isStronglyAdditive_zero hf

/-- The distinct-prime-factor counting function `ω = cardDistinctFactors` is strongly additive. -/
@[simp, grind .]
theorem isStronglyAdditive_cardDistinctFactors : cardDistinctFactors.IsStronglyAdditive where
  map_mul _ _ hmn := cardDistinctFactors_mul hmn
  map_one := cardDistinctFactors_one
  map_prime_pow hp hk := (cardDistinctFactors_apply_prime_pow hp hk).trans
    (cardDistinctFactors_apply_prime hp).symm

/-- The distinct-prime-factor counting function `ω = cardDistinctFactors` is additive. -/
@[simp, grind .]
theorem isAdditive_cardDistinctFactors : cardDistinctFactors.IsAdditive :=
  isStronglyAdditive_cardDistinctFactors.toIsAdditive

/-! ### Completely additive arithmetic functions -/

/-- An arithmetic function `f` is **completely additive** if `f 1 = 0` and `f (m * n) = f m + f n`
for all nonzero natural numbers `m` and `n`. -/
structure IsCompletelyAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop where
  /-- The value at one vanishes. -/
  map_one : f 1 = 0
  /-- Values add on all positive products. -/
  map_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

attribute [simp, grind =] IsCompletelyAdditive.map_one
attribute [simp, grind =] IsCompletelyAdditive.map_mul

/-- In a codomain with left-cancellative addition, `f (m * n) = f m + f n` on nonzero inputs
already forces `f 1 = 0`. -/
theorem isCompletelyAdditive_iff_of_isLeftCancelAdd [AddZeroClass R] [IsLeftCancelAdd R]
    {f : ArithmeticFunction R} :
    f.IsCompletelyAdditive ↔ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n :=
  ⟨fun hf ↦ hf.map_mul, fun h ↦ by
    have h1 : f 1 + 0 = f 1 + f 1 := by simpa using h one_ne_zero one_ne_zero
    exact ⟨(add_left_cancel h1).symm, h⟩⟩

namespace IsCompletelyAdditive

section ZeroAdd

variable [Zero R] [Add R] {f : ArithmeticFunction R}

/-- Every completely additive arithmetic function is additive. -/
@[grind →]
theorem isAdditive (hf : f.IsCompletelyAdditive) : f.IsAdditive where
  map_mul hm hn _ := hf.map_mul hm hn
  map_one := hf.map_one

/-- Characterization of `IsCompletelyAdditive` as a conjunction of vanishing at `1` and additivity
on nonzero inputs. -/
theorem iff_ne_zero :
    f.IsCompletelyAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, hf.map_mul⟩, fun ⟨h1, hmul⟩ ↦ ⟨h1, hmul⟩⟩

/-- Two completely additive arithmetic functions are equal if and only if they agree on all
primes. -/
theorem eq_iff_eq_on_primes {g : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    (hg : g.IsCompletelyAdditive) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ ext fun n ↦ ?_⟩
  induction n using Nat.recOnMul with
  | zero => simp
  | one => rw [hf.map_one, hg.map_one]
  | prime p hp => exact h p hp
  | mul a b iha ihb =>
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    rw [hf.map_mul ha hb, hg.map_mul ha hb, iha, ihb]

end ZeroAdd

section AddZeroClass

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- Post-composing a completely additive arithmetic function on nonzero inputs with an additive
monoid homomorphism preserves complete additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] {F : Type*} [FunLike F R S] [AddMonoidHomClass F R S]
    (hf : f.IsCompletelyAdditive) (φ : F) {g : ArithmeticFunction S}
    (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsCompletelyAdditive where
  map_one := by rw [hg 1 one_ne_zero, hf.map_one, _root_.map_zero φ]
  map_mul {m n} hm hn := by
    rw [hg (m * n) (mul_ne_zero hm hn), hg m hm, hg n hn, hf.map_mul hm hn, _root_.map_add φ]

/-- Pointwise scalar multiplication by a distributive action preserves complete additivity. -/
@[grind ←]
theorem smul [DistribSMul S R] (hf : f.IsCompletelyAdditive) (c : S) :
    (c • f).IsCompletelyAdditive where
  map_one := by simp [hf.map_one]
  map_mul hm hn := by simp [hf.map_mul hm hn, smul_add]

end AddZeroClass

/-- Coercing an `ℕ`-valued completely additive arithmetic function into an `AddMonoidWithOne`
preserves complete additivity. -/
@[grind ←]
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsCompletelyAdditive) :
    (f : ArithmeticFunction R).IsCompletelyAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ by simp

/-- Coercing a `ℤ`-valued completely additive arithmetic function into an `AddGroupWithOne`
preserves complete additivity. -/
@[grind ←]
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsCompletelyAdditive) :
    (f : ArithmeticFunction R).IsCompletelyAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ by simp

/-- Power law for completely additive functions: `f (n ^ k) = k • f n` for every `n, k : ℕ`
(including `n = 0`, where both sides vanish for `k = 0` via `f 1 = 0` and for `k > 0` via
`f 0 = 0`). -/
@[simp, grind =]
theorem map_pow [AddMonoid R] {f : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    (n k : ℕ) : f (n ^ k) = k • f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases k <;> simp [hf.map_one]
  induction k with
  | zero => simp [hf.map_one]
  | succ k ih => rw [pow_succ, hf.map_mul (pow_ne_zero k hn) hn, ih, succ_nsmul]

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two completely additive arithmetic functions is completely additive. -/
@[grind ←]
theorem add (hf : f.IsCompletelyAdditive) (hg : g.IsCompletelyAdditive) :
    (f + g).IsCompletelyAdditive where
  map_one := by simp [hf.map_one, hg.map_one]
  map_mul hm hn := by
    simp only [add_apply, hf.map_mul hm hn, hg.map_mul hm hn]
    exact add_add_add_comm _ _ _ _

/-- A completely additive function converts any finite product of nonzero naturals into the sum of
its values. -/
theorem map_prod {ι : Type*} (g : ι → ℕ) (hf : f.IsCompletelyAdditive) (s : Finset ι)
    (hs : ∀ i ∈ s, g i ≠ 0) : f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert a s has ih =>
    have ha : g a ≠ 0 := hs a (mem_insert_self a s)
    have hs' : ∀ i ∈ s, g i ≠ 0 := fun i hi ↦ hs i (mem_insert_of_mem hi)
    rw [prod_insert has, sum_insert has, hf.map_mul ha (prod_ne_zero_iff.mpr hs'), ih hs']

/-- **Factorization formula for a completely additive function.** For every `n : ℕ` (including `0`
and `1`), `f n = ∑ p ∈ n.primeFactors, n.factorization p • f p`. -/
theorem sum_primeFactors (hf : f.IsCompletelyAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, n.factorization p • f p := by
  rw [hf.isAdditive.sum_primeFactors_pow_factorization]
  exact sum_congr rfl fun p _ ↦ hf.map_pow p (n.factorization p)

end AddCommMonoid

/-- For a completely additive function taking values in an additive group, `f (m / d) = f m - f d`
whenever `d ∣ m` and `m ≠ 0` (at `m = 0`, `f (0 / 2) = 0` whereas `f 0 - f 2 = -f 2`). -/
theorem map_div [AddGroup R] {f : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    {m d : ℕ} (hdm : d ∣ m) (hm : m ≠ 0) : f (m / d) = f m - f d := by
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hdm
  have hmd : m / d ≠ 0 := fun h ↦ hm (by rw [← Nat.div_mul_cancel hdm, h, zero_mul])
  exact eq_sub_of_add_eq <| by rw [← hf.map_mul hmd hd, Nat.div_mul_cancel hdm]

/-- Pointwise negation preserves complete additivity. -/
@[grind ←]
theorem neg [SubtractionMonoid R] {f : ArithmeticFunction R} (hf : f.IsCompletelyAdditive) :
    (-f).IsCompletelyAdditive where
  map_one := by simp [hf.map_one]
  map_mul hm hn := by
    rw [neg_apply, mul_comm, hf.map_mul hn hm, neg_add_rev, neg_apply, neg_apply]

/-- Pointwise subtraction preserves complete additivity. -/
@[grind ←]
theorem sub [SubtractionCommMonoid R] {f g : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    (hg : g.IsCompletelyAdditive) : (f - g).IsCompletelyAdditive where
  map_one := by simp [hf.map_one, hg.map_one]
  map_mul hm hn := by
    simp only [sub_apply, hf.map_mul hm hn, hg.map_mul hm hn]
    exact (sub_add_sub_comm _ _ _ _).symm

end IsCompletelyAdditive

/-- The zero arithmetic function is completely additive. -/
@[simp, grind .]
theorem isCompletelyAdditive_zero [AddZeroClass R] :
    (0 : ArithmeticFunction R).IsCompletelyAdditive where
  map_one := by simp
  map_mul _ _ := by simp

/-- A finite pointwise sum of completely additive arithmetic functions is completely additive. -/
theorem isCompletelyAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction R) (hf : ∀ i ∈ s, (f i).IsCompletelyAdditive) :
    (∑ i ∈ s, f i).IsCompletelyAdditive :=
  Finset.sum_induction f IsCompletelyAdditive (fun _ _ ↦ .add) isCompletelyAdditive_zero hf

/-- The total-prime-factor counting function `Ω = cardFactors` is completely additive. -/
@[simp, grind .]
theorem isCompletelyAdditive_cardFactors : cardFactors.IsCompletelyAdditive where
  map_one := cardFactors_one
  map_mul hm hn := cardFactors_mul hm hn

/-- The total-prime-factor counting function `Ω = cardFactors` is additive. -/
@[simp, grind .]
theorem isAdditive_cardFactors : cardFactors.IsAdditive :=
  isCompletelyAdditive_cardFactors.isAdditive

end ArithmeticFunction
