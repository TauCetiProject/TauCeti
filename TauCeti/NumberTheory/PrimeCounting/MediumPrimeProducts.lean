/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bertrand
public import TauCeti.Data.Nat.Squarefree

/-!
# Products of distinct primes in `[x / 2, x]`

For a real `x` and a natural number `m`, this file defines the finite set `N_m(x)` of products of
`m` distinct primes from the closed interval `[x / 2, x]`, following Bary-Soroker, Koukoulopoulos
and Kozma, *Irreducibility of random polynomials: general measures*, Invent. Math. (2023), §3.6,
where it appears immediately before equation (3.4). Unique factorization identifies `N_m(x)` with
the `m`-element subsets of the primes in `[x / 2, x]`, which gives its cardinality as a binomial
coefficient.

## Main definitions

* `TauCeti.mediumPrimes x`: the finite set of primes `p` with `x / 2 ≤ p ≤ x`.
* `TauCeti.mediumPrimeProducts x m`: the finite set of products of `m` distinct elements of
  `TauCeti.mediumPrimes x`.

## Main results

* `TauCeti.mediumPrimes_nonempty_iff`: there is a prime in `[x / 2, x]` exactly when `2 ≤ x`.
* `TauCeti.mem_mediumPrimeProducts_iff_primeFactors`: `n ∈ N_m(x)` exactly when `n` is squarefree
  with `m` prime factors, all of them in `[x / 2, x]`.
* `TauCeti.card_mediumPrimeProducts`: `#N_m(x)` is the binomial coefficient of the number of
  primes in `[x / 2, x]` and `m`.
* `TauCeti.pow_le_of_mem_mediumPrimeProducts`, `TauCeti.le_pow_of_mem_mediumPrimeProducts`: every
  `n ∈ N_m(x)` satisfies `(x / 2) ^ m ≤ n ≤ x ^ m`.
-/

public section

open Finset Nat
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace TauCeti

variable {x : ℝ} {m n p : ℕ}

/-! ### Primes in `[x / 2, x]` -/

/-- The finite set of primes in the closed real interval `[x / 2, x]`. -/
noncomputable def mediumPrimes (x : ℝ) : Finset ℕ :=
  {p ∈ Icc ⌈x / 2⌉₊ ⌊x⌋₊ | p.Prime}

/-- The primes in `[x / 2, x]` are the primes between `⌈x / 2⌉₊` and `⌊x⌋₊`. -/
theorem mediumPrimes_def (x : ℝ) : mediumPrimes x = {p ∈ Icc ⌈x / 2⌉₊ ⌊x⌋₊ | p.Prime} := (rfl)

/-- Membership in `TauCeti.mediumPrimes x` is primality together with `x / 2 ≤ p ≤ x`, for every
real `x`. -/
@[simp]
theorem mem_mediumPrimes : p ∈ mediumPrimes x ↔ p.Prime ∧ x / 2 ≤ p ∧ (p : ℝ) ≤ x := by
  rw [mediumPrimes_def, mem_filter, mem_Icc, ceil_le, and_comm]
  exact and_congr_right fun hp ↦ and_congr_right fun _ ↦ le_floor_iff' hp.ne_zero

/-- The elements of `TauCeti.mediumPrimes x` are prime. -/
theorem prime_of_mem_mediumPrimes (hp : p ∈ mediumPrimes x) : p.Prime :=
  (mem_mediumPrimes.mp hp).1

/-- At a natural number `N`, the primes in `[N / 2, N]` are those between `(N + 1) / 2` (natural
division) and `N`. -/
theorem mediumPrimes_natCast (N : ℕ) :
    mediumPrimes (N : ℝ) = {p ∈ Icc ((N + 1) / 2) N | p.Prime} := by
  ext p
  have h : (N : ℝ) / 2 ≤ p ↔ (N + 1) / 2 ≤ p := by
    rw [div_le_iff₀ two_pos]
    norm_cast
    omega
  rw [mem_mediumPrimes, mem_filter, mem_Icc, h, cast_le, and_comm]

/-- There is a prime in `[x / 2, x]` exactly when `2 ≤ x`, by Bertrand's postulate. -/
theorem mediumPrimes_nonempty_iff : (mediumPrimes x).Nonempty ↔ 2 ≤ x := by
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_mediumPrimes] at hp
    exact le_trans (by exact_mod_cast hp.1.two_le) hp.2.2
  · intro hx
    have hx0 : 0 ≤ x / 2 := by linarith
    have hfloor : ⌊x / 2⌋₊ ≠ 0 := (floor_pos.mpr (by linarith)).ne'
    obtain ⟨p, hp, hlt, hle⟩ := exists_prime_lt_and_le_two_mul ⌊x / 2⌋₊ hfloor
    refine ⟨p, mem_mediumPrimes.mpr ⟨hp, ((floor_lt hx0).mp hlt).le, ?_⟩⟩
    calc (p : ℝ) ≤ 2 * (⌊x / 2⌋₊ : ℝ) := by exact_mod_cast hle
      _ ≤ 2 * (x / 2) := by gcongr; exact floor_le hx0
      _ = x := by ring

/-! ### Products of distinct primes in `[x / 2, x]` -/

/-- The finite set `N_m(x)` of products of `m` distinct primes from the closed interval
`[x / 2, x]`. -/
noncomputable def mediumPrimeProducts (x : ℝ) (m : ℕ) : Finset ℕ :=
  ((mediumPrimes x).powersetCard m).image fun t ↦ ∏ p ∈ t, p

/-- `N_m(x)` is the image of the `m`-element subsets of `TauCeti.mediumPrimes x` under the
product. -/
theorem mediumPrimeProducts_def (x : ℝ) (m : ℕ) :
    mediumPrimeProducts x m = ((mediumPrimes x).powersetCard m).image fun t ↦ ∏ p ∈ t, p := (rfl)

/-- `n ∈ N_m(x)` exactly when `n` is the product of an `m`-element set of primes in
`[x / 2, x]`. -/
theorem mem_mediumPrimeProducts :
    n ∈ mediumPrimeProducts x m ↔ ∃ t ⊆ mediumPrimes x, #t = m ∧ ∏ p ∈ t, p = n := by
  rw [mediumPrimeProducts_def, mem_image]
  simp only [mem_powersetCard, and_assoc]

/-- `n ∈ N_m(x)` exactly when `n` is squarefree with exactly `m` prime factors, all of them in
`[x / 2, x]`. -/
theorem mem_mediumPrimeProducts_iff_primeFactors :
    n ∈ mediumPrimeProducts x m ↔
      Squarefree n ∧ n.primeFactors ⊆ mediumPrimes x ∧ #n.primeFactors = m := by
  rw [mem_mediumPrimeProducts]
  constructor
  · rintro ⟨t, ht, hcard, rfl⟩
    have hprime : ∀ p ∈ t, p.Prime := fun p hp ↦ prime_of_mem_mediumPrimes (ht hp)
    rw [primeFactors_prod hprime]
    exact ⟨squarefree_prod_of_prime hprime, ht, hcard⟩
  · rintro ⟨hsq, hsub, hcard⟩
    exact ⟨n.primeFactors, hsub, hcard, prod_primeFactors_of_squarefree hsq⟩

/-- The only product of no primes is `1`, for every real `x`. -/
@[simp]
theorem mediumPrimeProducts_zero (x : ℝ) : mediumPrimeProducts x 0 = {1} := by
  rw [mediumPrimeProducts_def, powersetCard_zero, image_singleton, prod_empty]

/-- The products of one prime in `[x / 2, x]` are the primes in `[x / 2, x]`. -/
@[simp]
theorem mediumPrimeProducts_one (x : ℝ) : mediumPrimeProducts x 1 = mediumPrimes x := by
  ext n
  rw [mem_mediumPrimeProducts]
  constructor
  · rintro ⟨t, ht, hcard, rfl⟩
    obtain ⟨p, rfl⟩ := card_eq_one.mp hcard
    rw [prod_singleton]
    exact ht (mem_singleton_self p)
  · intro hn
    exact ⟨{n}, singleton_subset_iff.mpr hn, card_singleton n, prod_singleton _ n⟩

/-- The number of products of `m` distinct primes in `[x / 2, x]` is the binomial coefficient of
the number of such primes and `m`. -/
theorem card_mediumPrimeProducts (x : ℝ) (m : ℕ) :
    #(mediumPrimeProducts x m) = (#(mediumPrimes x)).choose m := by
  rw [mediumPrimeProducts_def]
  exact card_image_prod_powersetCard (fun p ↦ prime_of_mem_mediumPrimes) m

/-- `N_m(x)` is empty exactly when there are fewer than `m` primes in `[x / 2, x]`. -/
theorem mediumPrimeProducts_eq_empty_iff :
    mediumPrimeProducts x m = ∅ ↔ #(mediumPrimes x) < m := by
  rw [← Finset.card_eq_zero, card_mediumPrimeProducts, choose_eq_zero_iff]

/-- The elements of `N_m(x)` are squarefree. -/
theorem squarefree_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    Squarefree n :=
  (mem_mediumPrimeProducts_iff_primeFactors.mp hn).1

/-- The prime factors of an element of `N_m(x)` lie in `[x / 2, x]`. -/
theorem primeFactors_subset_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    n.primeFactors ⊆ mediumPrimes x :=
  (mem_mediumPrimeProducts_iff_primeFactors.mp hn).2.1

/-- An element of `N_m(x)` has exactly `m` prime factors. -/
theorem card_primeFactors_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    #n.primeFactors = m :=
  (mem_mediumPrimeProducts_iff_primeFactors.mp hn).2.2

/-- An element of `N_m(x)` has exactly `m` distinct prime factors. -/
theorem cardDistinctFactors_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    ω n = m := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    card_primeFactors_of_mem_mediumPrimeProducts hn]

/-- An element of `N_m(x)` has exactly `m` prime factors counted with multiplicity. -/
theorem cardFactors_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    Ω n = m := by
  have hsq := squarefree_of_mem_mediumPrimeProducts hn
  rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).mpr
    hsq, cardDistinctFactors_of_mem_mediumPrimeProducts hn]

/-- Every element of `N_m(x)` is at least `(x / 2) ^ m`, for every real `x`. -/
theorem pow_le_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    (x / 2) ^ m ≤ n := by
  obtain ⟨t, ht, rfl, rfl⟩ := mem_mediumPrimeProducts.mp hn
  have hmem : ∀ p ∈ t, x / 2 ≤ p ∧ (p : ℝ) ≤ x := fun p hp ↦ (mem_mediumPrimes.mp (ht hp)).2
  rw [cast_prod, ← prod_const]
  refine prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ (hmem p hp).1
  linarith [(hmem p hp).2, (p.cast_nonneg : (0 : ℝ) ≤ p)]

/-- Every element of `N_m(x)` is at most `x ^ m`. -/
theorem le_pow_of_mem_mediumPrimeProducts (hn : n ∈ mediumPrimeProducts x m) :
    (n : ℝ) ≤ x ^ m := by
  obtain ⟨t, ht, rfl, rfl⟩ := mem_mediumPrimeProducts.mp hn
  rw [cast_prod, ← prod_const]
  exact prod_le_prod₀ (fun p _ ↦ p.cast_nonneg) fun p hp ↦ (mem_mediumPrimes.mp (ht hp)).2.2

example : mediumPrimeProducts (10 : ℕ) 0 = {1} := mediumPrimeProducts_zero _

example : mediumPrimeProducts (10 : ℕ) 1 = {5, 7} := by
  rw [mediumPrimeProducts_def, mediumPrimes_natCast]
  decide +kernel

example : mediumPrimeProducts (10 : ℕ) 2 = {35} := by
  rw [mediumPrimeProducts_def, mediumPrimes_natCast]
  decide +kernel

example : mediumPrimeProducts (10 : ℕ) 3 = ∅ := by
  rw [mediumPrimeProducts_def, mediumPrimes_natCast]
  decide +kernel

example : 25 ∉ mediumPrimeProducts (10 : ℕ) 2 := by
  rw [mediumPrimeProducts_def, mediumPrimes_natCast]
  decide +kernel

example : mediumPrimeProducts (4 : ℕ) 1 = {2, 3} := by
  rw [mediumPrimeProducts_def, mediumPrimes_natCast]
  decide +kernel

end TauCeti
