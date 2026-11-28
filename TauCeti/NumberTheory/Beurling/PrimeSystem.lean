/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.IntervalCases
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Beurling prime systems

A *Beurling prime system* is a nondecreasing sequence of real numbers `1 < p 0 ≤ p 1 ≤ ⋯` tending
to infinity, the *generalized primes*. Its *generalized integers* are the finitely supported
exponent vectors `a : ℕ →₀ ℕ`, with norm `∏ⱼ p j ^ a j`. Equal real values are kept apart: two
indices with the same generalized prime are two primes, and two exponent vectors with the same
norm are two integers. The counting functions are

* `π_P(x)`, the number of indices `j` with `p j ≤ x`, and
* `N_P(x)`, the number of exponent vectors of norm at most `x`.

Both are finite: only finitely many generalized primes are at most `x`, and since `p 0 > 1` every
exponent of a vector of norm at most `x` is bounded.

## Main definitions

* `TauCeti.BeurlingPrimeSystem`: a Beurling prime system.
* `TauCeti.BeurlingPrimeSystem.primeCount`: the prime-counting function `π_P`.
* `TauCeti.BeurlingPrimeSystem.integerNorm`: the norm of an exponent vector.
* `TauCeti.BeurlingPrimeSystem.integerCount`: the integer-counting function `N_P`.
* `TauCeti.BeurlingPrimeSystem.ofPrimes`: the ordinary primes as a Beurling prime system.

## Main results

* `TauCeti.BeurlingPrimeSystem.integerNorm_add`: the norm is multiplicative.
* `TauCeti.BeurlingPrimeSystem.one_le_integerNorm`: every norm is at least `1`.
* `TauCeti.BeurlingPrimeSystem.finite_setOf_p_le`,
  `TauCeti.BeurlingPrimeSystem.finite_setOf_integerNorm_le`: the sets counted by `π_P(x)` and
  `N_P(x)` are finite.
* `TauCeti.BeurlingPrimeSystem.primeCount_le_integerCount`: `π_P(x) ≤ N_P(x)`.
* `TauCeti.BeurlingPrimeSystem.integerCount_eq_one_of_lt`: `N_P(x) = 1` for `1 ≤ x < p 0`.
* `TauCeti.BeurlingPrimeSystem.primeCount_ofPrimes`,
  `TauCeti.BeurlingPrimeSystem.integerCount_ofPrimes`: for the system `ofPrimes` of the ordinary
  primes, `π_P(x) = π(⌊x⌋₊)` and `N_P(x) = ⌊x⌋₊`.

## References

* A. Beurling, *Analyse de la loi asymptotique de la distribution des nombres premiers
  généralisés. I*, Acta Math. 68 (1937), 255–291.
* G. Debruyne, J. Vindas, *On general prime number theorems with remainder*, in *Generalized
  Functions and Fourier Analysis*, Oper. Theory Adv. Appl. 260, Springer (2017), 79–94, §1.
-/

public section

open Filter

namespace TauCeti

/-- A discrete *Beurling prime system*: a nondecreasing sequence `p` of real numbers greater than
`1` that tends to infinity. Repeated values are allowed and count as different generalized
primes. -/
@[ext]
structure BeurlingPrimeSystem where
  /-- The generalized primes `p 0 ≤ p 1 ≤ ⋯`. -/
  p : ℕ → ℝ
  /-- Every generalized prime is greater than `1`. -/
  one_lt : ∀ j, 1 < p j
  /-- The generalized primes are listed in nondecreasing order. -/
  mono : Monotone p
  /-- The generalized primes tend to infinity. -/
  tendsto : Tendsto p atTop atTop

namespace BeurlingPrimeSystem

variable (P : BeurlingPrimeSystem)

/-- The generalized primes are positive. -/
theorem p_pos (j : ℕ) : 0 < P.p j := zero_lt_one.trans (P.one_lt j)

/-- Only finitely many generalized primes are at most `x`. -/
theorem finite_setOf_p_le (x : ℝ) : {j | P.p j ≤ x}.Finite := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (P.tendsto.eventually_gt_atTop x)
  refine (Set.finite_lt_nat J).subset fun j hj ↦ ?_
  by_contra h
  exact (hJ j (not_lt.1 h)).not_ge hj

/-! ### The norm of a generalized integer -/

/-- The norm `∏ⱼ p j ^ a j` of the generalized integer with exponent vector `a`. -/
noncomputable def integerNorm (a : ℕ →₀ ℕ) : ℝ :=
  a.prod fun j k ↦ P.p j ^ k

/-- The defining formula of the norm. -/
theorem integerNorm_def (a : ℕ →₀ ℕ) : P.integerNorm a = a.prod fun j k ↦ P.p j ^ k := (rfl)

/-- The zero exponent vector has norm `1`. -/
@[simp]
theorem integerNorm_zero : P.integerNorm 0 = 1 := by
  rw [integerNorm_def, Finsupp.prod_zero_index]

/-- The norm is multiplicative: adding exponent vectors multiplies norms. -/
theorem integerNorm_add (a b : ℕ →₀ ℕ) :
    P.integerNorm (a + b) = P.integerNorm a * P.integerNorm b := by
  rw [integerNorm_def, integerNorm_def, integerNorm_def]
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

/-- The norm of the vector with exponent `k` at the index `j` is `p j ^ k`. -/
@[simp]
theorem integerNorm_single (j k : ℕ) : P.integerNorm (Finsupp.single j k) = P.p j ^ k := by
  rw [integerNorm_def]
  exact Finsupp.prod_single_index (pow_zero _)

/-- Every generalized integer has norm at least `1`. -/
theorem one_le_integerNorm (a : ℕ →₀ ℕ) : 1 ≤ P.integerNorm a := by
  rw [integerNorm_def]
  exact Finset.one_le_prod₀ fun j _ ↦ one_le_pow₀ (P.one_lt j).le

/-- Every generalized integer has positive norm. -/
theorem integerNorm_pos (a : ℕ →₀ ℕ) : 0 < P.integerNorm a :=
  zero_lt_one.trans_le (P.one_le_integerNorm a)

/-- Splitting off the index `j`: the norm of `a` is `p j ^ a j` times the norm of `a` with the
exponent at `j` removed. -/
theorem integerNorm_eq_pow_mul_erase (a : ℕ →₀ ℕ) (j : ℕ) :
    P.integerNorm a = P.p j ^ a j * P.integerNorm (a.erase j) := by
  rw [← integerNorm_single, ← integerNorm_add, Finsupp.single_add_erase]

/-- Each prime power `p j ^ a j` occurring in a generalized integer is at most its norm. -/
theorem p_pow_le_integerNorm (a : ℕ →₀ ℕ) (j : ℕ) : P.p j ^ a j ≤ P.integerNorm a := by
  rw [P.integerNorm_eq_pow_mul_erase a j]
  exact le_mul_of_one_le_right (pow_pos (P.p_pos j) _).le (P.one_le_integerNorm _)

/-- A generalized prime occurring in a generalized integer is at most its norm. -/
theorem p_le_integerNorm {a : ℕ →₀ ℕ} {j : ℕ} (h : a j ≠ 0) : P.p j ≤ P.integerNorm a :=
  (le_self_pow₀ (P.one_lt j).le h).trans (P.p_pow_le_integerNorm a j)

/-- Only finitely many generalized integers have norm at most `x`: their exponent vectors are
supported on the finitely many indices `j` with `p j ≤ x`, and every exponent `k` satisfies
`p 0 ^ k ≤ x`. -/
theorem finite_setOf_integerNorm_le (x : ℝ) : {a | P.integerNorm a ≤ x}.Finite := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (P.tendsto.eventually_gt_atTop x)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (P.one_lt 0)
  refine ((Finset.range J).finsupp fun _ ↦ Finset.range n).finite_toSet.subset fun a ha ↦ ?_
  have hle : ∀ j, P.p j ^ a j ≤ x := fun j ↦ (P.p_pow_le_integerNorm a j).trans ha
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  refine ⟨fun j hj ↦ ?_, fun j _ ↦ ?_⟩
  · rw [Finset.mem_range]
    by_contra h
    linarith [(P.p_le_integerNorm (Finsupp.mem_support_iff.1 hj)).trans ha, hJ j (not_lt.1 h)]
  · rw [Finset.mem_range]
    by_contra h
    have h1 : P.p 0 ^ n ≤ P.p j ^ a j :=
      (pow_le_pow_right₀ (P.one_lt 0).le (not_lt.1 h)).trans
        (pow_le_pow_left₀ (P.p_pos 0).le (P.mono (Nat.zero_le j)) _)
    linarith [hle j]

/-! ### The counting functions -/

/-- The prime-counting function `π_P(x)` of a Beurling prime system: the number of indices `j`
with `p j ≤ x`, so that repeated generalized primes are counted with multiplicity. -/
noncomputable def primeCount (x : ℝ) : ℕ :=
  Nat.card {j : ℕ // P.p j ≤ x}

/-- The defining formula of `π_P`. -/
theorem primeCount_def (x : ℝ) : P.primeCount x = Nat.card {j : ℕ // P.p j ≤ x} := (rfl)

/-- `π_P(x)` as the cardinality of a set of indices. -/
theorem primeCount_eq_ncard (x : ℝ) : P.primeCount x = {j | P.p j ≤ x}.ncard := by
  rw [primeCount_def, Set.ncard_ofPred]

/-- The integer-counting function `N_P(x)` of a Beurling prime system: the number of exponent
vectors of norm at most `x`, so that different vectors of equal norm are counted separately. -/
noncomputable def integerCount (x : ℝ) : ℕ :=
  Nat.card {a : ℕ →₀ ℕ // P.integerNorm a ≤ x}

/-- The defining formula of `N_P`. -/
theorem integerCount_def (x : ℝ) :
    P.integerCount x = Nat.card {a : ℕ →₀ ℕ // P.integerNorm a ≤ x} := (rfl)

/-- `N_P(x)` as the cardinality of a set of exponent vectors. -/
theorem integerCount_eq_ncard (x : ℝ) :
    P.integerCount x = {a | P.integerNorm a ≤ x}.ncard := by
  rw [integerCount_def, Set.ncard_ofPred]

/-- `π_P` is nondecreasing. -/
theorem primeCount_mono : Monotone P.primeCount := fun x y hxy ↦ by
  rw [primeCount_eq_ncard, primeCount_eq_ncard]
  exact Set.ncard_le_ncard (fun j hj ↦ le_trans hj hxy) (P.finite_setOf_p_le y)

/-- `N_P` is nondecreasing. -/
theorem integerCount_mono : Monotone P.integerCount := fun x y hxy ↦ by
  rw [integerCount_eq_ncard, integerCount_eq_ncard]
  exact Set.ncard_le_ncard (fun a ha ↦ le_trans ha hxy) (P.finite_setOf_integerNorm_le y)

/-- There are no generalized primes below `p 0`. -/
theorem primeCount_eq_zero_of_lt {x : ℝ} (hx : x < P.p 0) : P.primeCount x = 0 := by
  rw [primeCount_eq_ncard, Set.ncard_eq_zero (P.finite_setOf_p_le x),
    Set.eq_empty_iff_forall_notMem]
  exact fun j hj ↦ (hx.trans_le (P.mono (Nat.zero_le j))).not_ge hj

/-- There are no generalized integers of norm less than `1`. -/
theorem integerCount_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) : P.integerCount x = 0 := by
  rw [integerCount_eq_ncard, Set.ncard_eq_zero (P.finite_setOf_integerNorm_le x),
    Set.eq_empty_iff_forall_notMem]
  exact fun a ha ↦ (hx.trans_le (P.one_le_integerNorm a)).not_ge ha

/-- Below the first generalized prime the only generalized integer is the unit. -/
theorem integerCount_eq_one_of_lt {x : ℝ} (h1 : 1 ≤ x) (hx : x < P.p 0) : P.integerCount x = 1 := by
  have hset : {a | P.integerNorm a ≤ x} = {0} := by
    ext a
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun ha ↦ ?_, fun ha ↦ by rw [ha, integerNorm_zero]; exact h1⟩
    by_contra h0
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 h0
    linarith [P.p_le_integerNorm hj, P.mono (Nat.zero_le j)]
  rw [integerCount_eq_ncard, hset, Set.ncard_singleton]

/-- Each generalized prime is a generalized integer: `π_P(x) ≤ N_P(x)`. -/
theorem primeCount_le_integerCount (x : ℝ) : P.primeCount x ≤ P.integerCount x := by
  rw [primeCount_eq_ncard, integerCount_eq_ncard]
  refine Set.ncard_le_ncard_of_injOn (fun j ↦ Finsupp.single j 1) (fun j hj ↦ ?_)
    (fun i _ j _ hij ↦ Finsupp.single_left_injective one_ne_zero hij)
    (P.finite_setOf_integerNorm_le x)
  rw [Set.mem_ofPred_eq, integerNorm_single, pow_one]
  exact hj

/-- The unit has norm `1`, so `N_P(x)` is positive for `x ≥ 1`. -/
theorem integerCount_pos {x : ℝ} (hx : 1 ≤ x) : 0 < P.integerCount x := by
  rw [integerCount_eq_ncard, Set.ncard_pos (P.finite_setOf_integerNorm_le x)]
  exact ⟨0, by rw [Set.mem_ofPred_eq, integerNorm_zero]; exact hx⟩

/-! ### The ordinary primes -/

/-- The ordinary primes `2, 3, 5, …` form a Beurling prime system. -/
noncomputable def ofPrimes : BeurlingPrimeSystem where
  p j := Nat.nth Nat.Prime j
  one_lt j := by exact_mod_cast (Nat.prime_nth_prime j).one_lt
  mono := Nat.mono_cast.comp (Nat.nth_monotone Nat.infinite_setOfPred_prime)
  tendsto := tendsto_natCast_atTop_atTop.comp
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- The generalized primes of `ofPrimes` are the ordinary primes in increasing order. -/
@[simp]
theorem ofPrimes_p (j : ℕ) : ofPrimes.p j = Nat.nth Nat.Prime j := (rfl)

/-- For the ordinary primes, `π_P` is the usual prime-counting function. -/
@[simp]
theorem primeCount_ofPrimes (x : ℝ) : ofPrimes.primeCount x = Nat.primeCounting ⌊x⌋₊ := by
  have hset : {j | ofPrimes.p j ≤ x} = ↑(Finset.range (Nat.primeCounting ⌊x⌋₊)) := by
    ext j
    rw [Set.mem_ofPred_eq, ofPrimes_p, Finset.coe_range, Set.mem_Iio, Nat.primeCounting,
      Nat.primeCounting', Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime, Nat.lt_add_one_iff,
      Nat.le_floor_iff' (Nat.prime_nth_prime j).ne_zero]
  rw [primeCount_eq_ncard, hset, Set.ncard_coe_finset, Finset.card_range]

/-- For the ordinary primes, the norm of an exponent vector is the natural number with that prime
factorization. -/
theorem integerNorm_ofPrimes (a : ℕ →₀ ℕ) :
    ofPrimes.integerNorm a = ((a.mapDomain (Nat.nth Nat.Prime)).prod (· ^ ·) : ℕ) := by
  rw [integerNorm_def,
    Finsupp.prod_mapDomain_index_inj (Nat.nth_injective Nat.infinite_setOfPred_prime),
    Nat.cast_finsuppProd]
  simp only [ofPrimes_p, Nat.cast_pow]

/-- For the ordinary primes, the generalized integers are the positive integers, by unique
factorization: `N_P(x) = ⌊x⌋₊`. -/
@[simp]
theorem integerCount_ofPrimes (x : ℝ) : ofPrimes.integerCount x = ⌊x⌋₊ := by
  have hinj := Nat.nth_injective Nat.infinite_setOfPred_prime
  have hprime (a : ℕ →₀ ℕ) : ∀ q ∈ (a.mapDomain (Nat.nth Nat.Prime)).support, q.Prime := by
    intro q hq
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
    exact Nat.prime_nth_prime j
  -- The natural-number norm is injective, and its image is the positive integers.
  have hφ : Function.Injective fun a : ℕ →₀ ℕ ↦ (a.mapDomain (Nat.nth Nat.Prime)).prod (· ^ ·) :=
    fun a b hab ↦ Finsupp.mapDomain_injective hinj <| by
      have h := congrArg Nat.factorization hab
      rwa [Nat.factorization_prod_pow_eq_self (hprime a),
        Nat.factorization_prod_pow_eq_self (hprime b)] at h
  have himage : (fun a : ℕ →₀ ℕ ↦ (a.mapDomain (Nat.nth Nat.Prime)).prod (· ^ ·)) ''
      {a | ofPrimes.integerNorm a ≤ x} = ↑(Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    rw [Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Set.mem_ofPred_eq, integerNorm_ofPrimes] at ha
      refine ⟨Nat.pos_of_ne_zero (Finsupp.prod_ne_zero_iff.2 fun q hq ↦ ?_), Nat.le_floor ha⟩
      exact pow_ne_zero _ (hprime a q hq).ne_zero
    · rintro ⟨hn1, hnx⟩
      have hn0 : n ≠ 0 := by omega
      have hsupp : (↑n.factorization.support : Set ℕ) ⊆ Set.range (Nat.nth Nat.Prime) := by
        intro q hq
        exact ⟨Nat.count Nat.Prime q, Nat.nth_count (Nat.prime_of_mem_primeFactors hq)⟩
      have hback : ((n.factorization.comapDomain (Nat.nth Nat.Prime) hinj.injOn).mapDomain
          (Nat.nth Nat.Prime)).prod (· ^ ·) = n := by
        rw [Finsupp.mapDomain_comapDomain _ hinj _ hsupp, Nat.prod_factorization_pow_eq_self hn0]
      refine ⟨n.factorization.comapDomain (Nat.nth Nat.Prime) hinj.injOn, ?_, hback⟩
      rw [Set.mem_ofPred_eq, integerNorm_ofPrimes, hback]
      exact (Nat.le_floor_iff' hn0).1 hnx
  rw [integerCount_eq_ncard, ← Set.ncard_image_of_injective _ hφ, himage, Set.ncard_coe_finset,
    Nat.card_Icc, Nat.add_sub_cancel]

/-! ### Examples -/

example : P.integerCount 0 = 0 := P.integerCount_eq_zero_of_lt_one zero_lt_one

example : P.primeCount 0 = 0 := P.primeCount_eq_zero_of_lt (P.p_pos 0)

example : P.integerCount 1 = 1 := P.integerCount_eq_one_of_lt le_rfl (P.one_lt 0)

/-- Two indices with the same generalized prime `2` are counted twice by `π_P`. -/
example (h0 : P.p 0 = 2) (h1 : P.p 1 = 2) (h2 : 2 < P.p 2) : P.primeCount 2 = 2 := by
  have hset : {j | P.p j ≤ 2} = ↑({0, 1} : Finset ℕ) := by
    ext j
    rw [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    refine ⟨fun hj ↦ ?_, fun hj ↦ ?_⟩
    · by_contra h
      have hj2 : 2 ≤ j := by omega
      linarith [P.mono hj2]
    · rcases hj with rfl | rfl
      · exact h0.le
      · exact h1.le
  rw [primeCount_eq_ncard, hset, Set.ncard_coe_finset, Finset.card_pair zero_ne_one]

/-- With `p 0 = p 1 = 2 < p 2` there are three generalized integers of norm at most `2`: the unit
and the two generalized primes equal to `2`, which are different generalized integers. -/
example (h0 : P.p 0 = 2) (h1 : P.p 1 = 2) (h2 : 2 < P.p 2) : P.integerCount 2 = 3 := by
  have hset : {a | P.integerNorm a ≤ 2} =
      ↑({0, Finsupp.single 0 1, Finsupp.single 1 1} : Finset (ℕ →₀ ℕ)) := by
    ext a
    rw [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
    · -- Exponents at indices `j ≥ 2` vanish; those at `0` and `1` add up to at most `1`.
      have hbig : ∀ j, 2 ≤ j → a j = 0 := fun j hj ↦ by
        by_contra h
        linarith [P.p_le_integerNorm h, P.mono hj]
      have hsmall : a 0 + a 1 ≤ 1 := by
        have h := P.integerNorm_eq_pow_mul_erase a 0
        have h' := P.p_pow_le_integerNorm (a.erase 0) 1
        rw [Finsupp.erase_ne one_ne_zero, h1] at h'
        rw [h0] at h
        have hpow : (2 : ℝ) ^ (a 0 + a 1) ≤ 2 ^ 1 := by
          rw [pow_add, pow_one]
          nlinarith [pow_pos (zero_lt_two' ℝ) (a 0)]
        exact (pow_le_pow_iff_right₀ one_lt_two).1 hpow
      have hrepr : a = Finsupp.single 0 (a 0) + Finsupp.single 1 (a 1) := by
        ext j
        rcases Nat.lt_or_ge j 2 with hj | hj
        · interval_cases j <;> simp
        · have hj0 : j ≠ 0 := by omega
          have hj1 : j ≠ 1 := by omega
          simp [hbig j hj, hj0, hj1]
      have hcases : (a 0 = 0 ∧ a 1 = 0) ∨ (a 0 = 1 ∧ a 1 = 0) ∨ (a 0 = 0 ∧ a 1 = 1) := by omega
      rw [hrepr]
      rcases hcases with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩ <;> simp [ha0, ha1]
    · rcases ha with rfl | rfl | rfl
      · rw [integerNorm_zero]
        exact one_le_two
      · rw [integerNorm_single, pow_one, h0]
      · rw [integerNorm_single, pow_one, h1]
  have hne : (Finsupp.single 0 1 : ℕ →₀ ℕ) ≠ Finsupp.single 1 1 := fun h ↦ by
    have := congrArg (fun f : ℕ →₀ ℕ ↦ f 0) h
    simp at this
  have hzero : (0 : ℕ →₀ ℕ) ∉ ({Finsupp.single 0 1, Finsupp.single 1 1} : Finset (ℕ →₀ ℕ)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
  rw [integerCount_eq_ncard, hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem hzero,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

end BeurlingPrimeSystem

end TauCeti
