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
* `TauCeti.BeurlingPrimeSystem.lt_primeCount_iff`: `j < π_P(x)` exactly when `p j ≤ x`.
* `TauCeti.BeurlingPrimeSystem.primeCount_eq_zero_iff`,
  `TauCeti.BeurlingPrimeSystem.integerCount_eq_zero_iff`,
  `TauCeti.BeurlingPrimeSystem.integerCount_eq_one_iff`: `π_P(x) = 0` exactly for `x < p 0`,
  `N_P(x) = 0` exactly for `x < 1`, and `N_P(x) = 1` exactly for `1 ≤ x < p 0`.
* `TauCeti.BeurlingPrimeSystem.ofPrimesIntegerEquiv`,
  `TauCeti.BeurlingPrimeSystem.integerNorm_ofPrimes`: for the ordinary primes, the exponent
  vectors correspond to the positive natural numbers, and the norm is that natural number.
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

/-- The norm of a generalized integer is `1` exactly for the unit. -/
@[simp]
theorem integerNorm_eq_one_iff {a : ℕ →₀ ℕ} : P.integerNorm a = 1 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, integerNorm_zero]⟩
  by_contra h0
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 h0
  exact (P.one_lt j).not_ge ((P.p_le_integerNorm hj).trans h.le)

/-- A generalized integer of norm at most `x` is supported on the indices `j` with `p j ≤ x`. -/
theorem support_subset_of_integerNorm_le {a : ℕ →₀ ℕ} {x : ℝ} (ha : P.integerNorm a ≤ x) :
    (a.support : Set ℕ) ⊆ {j | P.p j ≤ x} := fun _ hj ↦
  (P.p_le_integerNorm (Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hj))).trans ha

/-- Only finitely many generalized integers have norm at most `x`: their exponent vectors are
supported on the finitely many indices `j` with `p j ≤ x`, and every exponent `k` satisfies
`p 0 ^ k ≤ x`. -/
theorem finite_setOf_integerNorm_le (x : ℝ) : {a | P.integerNorm a ≤ x}.Finite := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (P.one_lt 0)
  refine ((P.finite_setOf_p_le x).toFinset.finsupp fun _ ↦ Finset.range n).finite_toSet.subset
    fun a ha ↦ ?_
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  refine ⟨fun j hj ↦ (P.finite_setOf_p_le x).mem_toFinset.2
    (P.support_subset_of_integerNorm_le ha (Finset.mem_coe.2 hj)), fun j _ ↦ ?_⟩
  rw [Finset.mem_range]
  by_contra h
  have h1 : P.p 0 ^ n ≤ P.p j ^ a j :=
    (pow_le_pow_right₀ (P.one_lt 0).le (not_lt.1 h)).trans
      (pow_le_pow_left₀ (P.p_pos 0).le (P.mono (Nat.zero_le j)) _)
  linarith [(P.p_pow_le_integerNorm a j).trans ha]

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

/-- `j < π_P(x)` exactly when the generalized prime `p j` is at most `x`: the indices counted by
`π_P(x)` form an initial segment of the natural numbers. -/
theorem lt_primeCount_iff {j : ℕ} {x : ℝ} : j < P.primeCount x ↔ P.p j ≤ x := by
  rw [primeCount_eq_ncard]
  refine ⟨fun h ↦ ?_, fun hj ↦ ?_⟩
  · by_contra hj
    have hsub : {i | P.p i ≤ x} ⊆ ↑(Finset.range j) := fun i hi ↦ by
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hij
      exact hj ((P.mono (not_lt.1 hij)).trans hi)
    have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at hcard
    exact h.not_ge hcard
  · have hsub : ↑(Finset.range (j + 1)) ⊆ {i | P.p i ≤ x} := fun i hi ↦ by
      rw [Finset.coe_range, Set.mem_Iio, Nat.lt_add_one_iff] at hi
      exact (P.mono hi).trans hj
    have hcard := Set.ncard_le_ncard hsub (P.finite_setOf_p_le x)
    rw [Set.ncard_coe_finset, Finset.card_range] at hcard
    exact Nat.add_one_le_iff.1 hcard

/-- `π_P(x) = 0` exactly when `x` is below the first generalized prime. -/
@[simp]
theorem primeCount_eq_zero_iff {x : ℝ} : P.primeCount x = 0 ↔ x < P.p 0 := by
  rw [← not_le, ← P.lt_primeCount_iff, Nat.pos_iff_ne_zero, not_not]

/-- `π_P(0) = 0`. -/
@[simp]
theorem primeCount_zero : P.primeCount 0 = 0 := P.primeCount_eq_zero_iff.2 (P.p_pos 0)

/-- `N_P(x) = 0` exactly when `x < 1`: the unit has norm `1`, and no norm is smaller. -/
@[simp]
theorem integerCount_eq_zero_iff {x : ℝ} : P.integerCount x = 0 ↔ x < 1 := by
  rw [integerCount_eq_ncard, Set.ncard_eq_zero (P.finite_setOf_integerNorm_le x),
    Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h ↦ ?_, fun hx a ha ↦ (hx.trans_le (P.one_le_integerNorm a)).not_ge ha⟩
  by_contra hx
  refine h 0 ?_
  rw [Set.mem_ofPred_eq, integerNorm_zero]
  exact not_lt.1 hx

/-- `N_P(0) = 0`. -/
@[simp]
theorem integerCount_zero : P.integerCount 0 = 0 := P.integerCount_eq_zero_iff.2 zero_lt_one

/-- `N_P(x) = 1` exactly for `1 ≤ x < p 0`: below the first generalized prime the only generalized
integer is the unit, and from `p 0` on the vector with exponent `1` at the index `0` is a
second one. -/
@[simp]
theorem integerCount_eq_one_iff {x : ℝ} : P.integerCount x = 1 ↔ 1 ≤ x ∧ x < P.p 0 := by
  rw [integerCount_eq_ncard, Set.ncard_eq_one]
  refine ⟨fun ⟨b, hb⟩ ↦ ?_, fun ⟨h1, hx⟩ ↦ ⟨0, ?_⟩⟩
  · have h1 : 1 ≤ x := by
      by_contra hx
      have h0 := P.integerCount_eq_zero_iff.2 (not_le.1 hx)
      rw [integerCount_eq_ncard, hb, Set.ncard_singleton] at h0
      exact one_ne_zero h0
    refine ⟨h1, lt_of_not_ge fun hp ↦ ?_⟩
    have hz : (0 : ℕ →₀ ℕ) ∈ {a | P.integerNorm a ≤ x} := by
      rw [Set.mem_ofPred_eq, integerNorm_zero]
      exact h1
    have hs : Finsupp.single 0 1 ∈ {a | P.integerNorm a ≤ x} := by
      rw [Set.mem_ofPred_eq, integerNorm_single, pow_one]
      exact hp
    rw [hb, Set.mem_singleton_iff] at hz hs
    exact Finsupp.single_ne_zero.2 one_ne_zero (hs.trans hz.symm)
  · ext a
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun ha ↦ ?_, fun ha ↦ by rw [ha, integerNorm_zero]; exact h1⟩
    by_contra h0
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 h0
    exact (hx.trans_le ((P.mono (Nat.zero_le j)).trans (P.p_le_integerNorm hj))).not_ge ha

/-- `N_P(1) = 1`. -/
@[simp]
theorem integerCount_one : P.integerCount 1 = 1 :=
  P.integerCount_eq_one_iff.2 ⟨le_rfl, P.one_lt 0⟩

/-- Each generalized prime is a generalized integer: `π_P(x) ≤ N_P(x)`. -/
theorem primeCount_le_integerCount (x : ℝ) : P.primeCount x ≤ P.integerCount x := by
  rw [primeCount_eq_ncard, integerCount_eq_ncard]
  refine Set.ncard_le_ncard_of_injOn (fun j ↦ Finsupp.single j 1) (fun j hj ↦ ?_)
    (fun i _ j _ hij ↦ Finsupp.single_left_injective one_ne_zero hij)
    (P.finite_setOf_integerNorm_le x)
  rw [Set.mem_ofPred_eq, integerNorm_single, pow_one]
  exact hj

/-- The unit has norm `1`, so `N_P(x)` is positive for `x ≥ 1`. -/
theorem integerCount_pos {x : ℝ} (hx : 1 ≤ x) : 0 < P.integerCount x :=
  Nat.pos_of_ne_zero fun h ↦ (P.integerCount_eq_zero_iff.1 h).not_ge hx

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
  refine eq_of_forall_lt_iff fun j ↦ ?_
  have hrank : j < Nat.primeCounting ⌊x⌋₊ ↔ Nat.nth Nat.Prime j ≤ ⌊x⌋₊ := by
    rw [Nat.primeCounting, Nat.primeCounting',
      Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime, Nat.lt_add_one_iff]
  rw [lt_primeCount_iff, ofPrimes_p, hrank, Nat.le_floor_iff' (Nat.prime_nth_prime j).ne_zero]

/-- Reindexing along the increasing enumeration of the primes identifies the exponent vectors
`ℕ →₀ ℕ` with the finitely supported functions supported on primes. -/
private noncomputable def mapDomainNthPrimeEquiv :
    (ℕ →₀ ℕ) ≃ {f : ℕ →₀ ℕ // ∀ q ∈ f.support, q.Prime} where
  toFun a := ⟨a.mapDomain (Nat.nth Nat.Prime), fun q hq ↦ by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
    exact Nat.prime_nth_prime j⟩
  invFun f := f.val.comapDomain (Nat.nth Nat.Prime)
    (Nat.nth_injective Nat.infinite_setOfPred_prime).injOn
  left_inv a := Finsupp.comapDomain_mapDomain _
    (Nat.nth_injective Nat.infinite_setOfPred_prime) a
  right_inv f := Subtype.ext <| Finsupp.mapDomain_comapDomain _
    (Nat.nth_injective Nat.infinite_setOfPred_prime) _ fun q hq ↦
      ⟨Nat.count Nat.Prime q, Nat.nth_count (f.property q hq)⟩

/-- **Unique factorization for the ordinary primes.** The generalized integers of `ofPrimes`
correspond to the positive natural numbers: the exponent vector `a` goes to
`∏ⱼ (j-th prime) ^ a j`. -/
noncomputable def ofPrimesIntegerEquiv : (ℕ →₀ ℕ) ≃ ℕ+ :=
  mapDomainNthPrimeEquiv.trans Nat.factorizationEquiv.symm

/-- The positive natural number of an exponent vector is the product of the prime powers. -/
theorem coe_ofPrimesIntegerEquiv (a : ℕ →₀ ℕ) :
    (ofPrimesIntegerEquiv a : ℕ) = (a.mapDomain (Nat.nth Nat.Prime)).prod (· ^ ·) := (rfl)

/-- For the ordinary primes, the norm of an exponent vector is the positive natural number with
that prime factorization. -/
theorem integerNorm_ofPrimes (a : ℕ →₀ ℕ) :
    ofPrimes.integerNorm a = (ofPrimesIntegerEquiv a : ℕ) := by
  rw [coe_ofPrimesIntegerEquiv, integerNorm_def,
    Finsupp.prod_mapDomain_index_inj (Nat.nth_injective Nat.infinite_setOfPred_prime),
    Nat.cast_finsuppProd]
  simp only [ofPrimes_p, Nat.cast_pow]

/-- For the ordinary primes, the generalized integers are the positive integers, by unique
factorization: `N_P(x) = ⌊x⌋₊`. -/
@[simp]
theorem integerCount_ofPrimes (x : ℝ) : ofPrimes.integerCount x = ⌊x⌋₊ := by
  have himage : (fun a : ℕ →₀ ℕ ↦ (ofPrimesIntegerEquiv a : ℕ)) ''
      {a | ofPrimes.integerNorm a ≤ x} = ↑(Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    rw [Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Set.mem_ofPred_eq, integerNorm_ofPrimes] at ha
      exact ⟨(ofPrimesIntegerEquiv a).pos, Nat.le_floor ha⟩
    · rintro ⟨hn1, hnx⟩
      obtain ⟨m, rfl⟩ : ∃ m : ℕ+, (m : ℕ) = n := ⟨⟨n, hn1⟩, rfl⟩
      refine ⟨ofPrimesIntegerEquiv.symm m, ?_, by rw [Equiv.apply_symm_apply]⟩
      rw [Set.mem_ofPred_eq, integerNorm_ofPrimes, Equiv.apply_symm_apply]
      exact (Nat.le_floor_iff' m.ne_zero).1 hnx
  have hinj : Function.Injective fun a : ℕ →₀ ℕ ↦ (ofPrimesIntegerEquiv a : ℕ) :=
    fun a b h ↦ ofPrimesIntegerEquiv.injective (PNat.eq h)
  rw [integerCount_eq_ncard, ← Set.ncard_image_of_injective _ hinj, himage,
    Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]

/-! ### Examples -/

/-- If `p 1 = 2 < p 2`, then `π_P(2) = 2`: the indices `0` and `1` are counted separately, also
when `p 0 = p 1 = 2` is a repeated generalized prime. -/
example (h1 : P.p 1 = 2) (h2 : 2 < P.p 2) : P.primeCount 2 = 2 := by
  refine eq_of_forall_lt_iff fun j ↦ ?_
  rw [P.lt_primeCount_iff]
  refine ⟨fun hj ↦ ?_, fun hj ↦ (P.mono (Nat.lt_add_one_iff.1 hj)).trans h1.le⟩
  by_contra h
  linarith [P.mono (not_lt.1 h)]

/-- With `p 0 = p 1 = 2 < p 2` there are three generalized integers of norm at most `2`: the unit
and the two generalized primes equal to `2`, which are different generalized integers. -/
example (h0 : P.p 0 = 2) (h1 : P.p 1 = 2) (h2 : 2 < P.p 2) : P.integerCount 2 = 3 := by
  have hset : {a | P.integerNorm a ≤ 2} =
      ↑({0, Finsupp.single 0 1, Finsupp.single 1 1} : Finset (ℕ →₀ ℕ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
    · -- Exponents at indices `j ≥ 2` vanish; those at `0` and `1` add up to at most `1`.
      have hbig : ∀ j, 2 ≤ j → a j = 0 := fun j hj ↦ by
        by_contra h
        have hj2 : P.p j ≤ 2 := P.support_subset_of_integerNorm_le ha
          (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 h))
        linarith [P.mono hj]
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
