/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Factorizations of `n!` into bounded factors

`Nat.factorialFactorCount B n` is the least number `t` of factors in a factorization
`n! = a₁ ⋯ a_t` with natural numbers `a_i ≤ B`. The factors are automatically positive, since
`n! ≠ 0`. Erdős problem 392 asks for the size of `factorialFactorCount (n ^ 2) n`; the answer is
`n / 2 - n / (2 log n) + o(n / log n)`, and similarly
`factorialFactorCount n n = n - n / log n + o(n / log n)`.

This file develops the elementary theory of the count. A factorization exists exactly when every
prime `p ≤ n` satisfies `p ≤ B`, the prime factors of `n!` being the primes up to `n`; otherwise
the count is the junk value `0`. When `n ≤ B` the factors `1, 2, …, n` show that the count is at
most `n`. Every factorization gives `n! ≤ B ^ t`, so `log n! ≤ t log B`, and the elementary
lower bound `n log n - n ≤ log n!` turns this into the lower halves of both asymptotics, with no
error term: for `n ≥ 2`, `n - n / log n ≤ factorialFactorCount n n` and
`n / 2 - n / (2 log n) ≤ factorialFactorCount (n ^ 2) n`. The count is antitone in the bound,
and pairing the factors gives `factorialFactorCount (B ^ 2) n ≤ ⌈factorialFactorCount B n / 2⌉`,
which reduces the upper bound for the bound `n ^ 2` to that for the bound `n`.

## Main definitions

* `Nat.factorialFactorCount B n`: the least number of factors at most `B` whose product is `n!`.

## Main results

* `Nat.exists_multiset_prod_eq_factorial_iff`: a factorization of `n!` into factors at most `B`
  exists if and only if every prime `p ≤ n` satisfies `p ≤ B`.
* `Nat.factorialFactorCount_le_iff`: the count is at most `t` if and only if there is a
  factorization into at most `t` factors.
* `Nat.factorialFactorCount_eq_zero_iff`: the count vanishes exactly for `n ≤ 1` and for the
  junk value.
* `Nat.factorialFactorCount_le_self`: the count is at most `n` when `n ≤ B`.
* `Nat.log_factorial_le_factorialFactorCount_mul_log`: `log n! ≤ factorialFactorCount B n * log B`.
* `Nat.sub_div_log_le_factorialFactorCount_self` and
  `Nat.div_two_sub_div_log_le_factorialFactorCount_sq`: the lower bounds
  `n - n / log n ≤ factorialFactorCount n n` and
  `n / 2 - n / (2 log n) ≤ factorialFactorCount (n ^ 2) n`.
* `Nat.antitoneOn_factorialFactorCount`: the count is antitone in the bound on `B ≥ n`.
* `Nat.factorialFactorCount_sq_le`: pairing, `factorialFactorCount (B ^ 2) n ≤ (t + 1) / 2` for
  `t = factorialFactorCount B n`.

## References

* T. F. Bloom, *Erdős problem #392*, <https://www.erdosproblems.com/392>.
* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, blueprint, §8.1,
  Theorems 8.1.1 and 8.1.2.
* T. Tao and contributors, *IEANTN: Integrated Explicit Analytic Number Theory Network*, the
  Erdős 392 blueprint, <https://github.com/teorth/IEANTN>; the lower bounds here follow its
  argument `t log B ≥ log n!`.
-/

public section

open Multiset

namespace Nat

/-- The least number `t` of factors in a factorization `n! = a₁ ⋯ a_t` into natural numbers
`a_i ≤ B`, the factors being counted with multiplicity. The factors are automatically positive,
since `n! ≠ 0`. A factorization exists exactly when every prime `p ≤ n` satisfies `p ≤ B`
(`Nat.exists_multiset_prod_eq_factorial_iff`), for instance when `n ≤ B`; otherwise the value is
the junk `0`. -/
noncomputable def factorialFactorCount (B n : ℕ) : ℕ :=
  sInf {t | ∃ s : Multiset ℕ, card s = t ∧ (∀ a ∈ s, a ≤ B) ∧ s.prod = n !}

variable {B B' n t : ℕ}

/-- A factorization of `n!` into factors at most `B` exists if and only if every prime `p ≤ n`
satisfies `p ≤ B`: the prime factorization of `n!` is one, and a prime `p ≤ n` divides `n!`, hence
one of the factors. -/
theorem exists_multiset_prod_eq_factorial_iff :
    (∃ s : Multiset ℕ, (∀ a ∈ s, a ≤ B) ∧ s.prod = n !) ↔ ∀ p, p.Prime → p ≤ n → p ≤ B := by
  constructor
  · rintro ⟨s, hs, hprod⟩ p hp hpn
    obtain ⟨a, ha, hpa⟩ := hp.prime.exists_mem_multiset_dvd
      (hprod ▸ (hp.dvd_factorial).2 hpn)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact factorial_ne_zero n (hprod ▸ prod_eq_zero ha)
    exact (le_of_dvd (pos_of_ne_zero ha0) hpa).trans (hs a ha)
  · intro h
    refine ⟨(n !).primeFactorsList, fun p hp ↦ ?_, by
      rw [prod_coe, prod_primeFactorsList (factorial_ne_zero n)]⟩
    have hp' := prime_of_mem_primeFactorsList hp
    exact h p hp' ((hp'.dvd_factorial).1 (dvd_of_mem_primeFactorsList hp))

/-- Every factorization of `n!` into factors at most `B` has at least
`factorialFactorCount B n` factors. -/
theorem factorialFactorCount_le_card {s : Multiset ℕ} (hs : ∀ a ∈ s, a ≤ B)
    (hprod : s.prod = n !) : factorialFactorCount B n ≤ card s :=
  Nat.sInf_le ⟨s, rfl, hs, hprod⟩

/-- When every prime `p ≤ n` satisfies `p ≤ B`, the least number of factors is attained. -/
theorem exists_multiset_card_eq_factorialFactorCount (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    ∃ s : Multiset ℕ, card s = factorialFactorCount B n ∧ (∀ a ∈ s, a ≤ B) ∧ s.prod = n ! := by
  obtain ⟨s, hs, hprod⟩ := exists_multiset_prod_eq_factorial_iff.2 hB
  have hne : {t | ∃ s : Multiset ℕ, card s = t ∧ (∀ a ∈ s, a ≤ B) ∧ s.prod = n !}.Nonempty :=
    ⟨card s, s, rfl, hs, hprod⟩
  exact Nat.sInf_mem hne

/-- When every prime `p ≤ n` satisfies `p ≤ B`, the count is at most `t` if and only if `n!` is a
product of at most `t` factors at most `B`. -/
theorem factorialFactorCount_le_iff (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    factorialFactorCount B n ≤ t ↔
      ∃ s : Multiset ℕ, card s ≤ t ∧ (∀ a ∈ s, a ≤ B) ∧ s.prod = n ! := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs, hprod⟩ := exists_multiset_card_eq_factorialFactorCount hB
    exact ⟨s, hcard ▸ h, hs, hprod⟩
  · rintro ⟨s, hcard, hs, hprod⟩
    exact (factorialFactorCount_le_card hs hprod).trans hcard

/-- The count vanishes exactly when `n! = 1`, that is `n ≤ 1`, or when no factorization exists,
that is some prime `p ≤ n` exceeds `B`. -/
theorem factorialFactorCount_eq_zero_iff :
    factorialFactorCount B n = 0 ↔ n ≤ 1 ∨ ∃ p, p.Prime ∧ p ≤ n ∧ B < p := by
  have h := (exists_multiset_prod_eq_factorial_iff (B := B) (n := n)).not
  push Not at h
  rw [← h, factorialFactorCount, Nat.sInf_eq_zero, Set.eq_empty_iff_forall_notMem]
  refine or_congr ⟨?_, fun hn ↦ ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨s, hs, -, hprod⟩
    rwa [Multiset.card_eq_zero.1 hs, prod_zero, eq_comm, factorial_eq_one] at hprod
  · exact ⟨0, card_zero, by simp, by rw [prod_zero, factorial_eq_one.2 hn]⟩
  · intro h' s hs hprod
    exact h' _ ⟨s, rfl, hs, hprod⟩
  · rintro h' t ⟨s, -, hs, hprod⟩
    exact h' s hs hprod

@[simp]
theorem factorialFactorCount_zero_right (B : ℕ) : factorialFactorCount B 0 = 0 :=
  factorialFactorCount_eq_zero_iff.2 (.inl (zero_le _))

@[simp]
theorem factorialFactorCount_one_right (B : ℕ) : factorialFactorCount B 1 = 0 :=
  factorialFactorCount_eq_zero_iff.2 (.inl le_rfl)

/-- For `n ≥ 2`, when a factorization exists, at least one factor is needed. -/
theorem factorialFactorCount_pos (hn : 2 ≤ n) (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    0 < factorialFactorCount B n := by
  refine pos_of_ne_zero fun h ↦ ?_
  rcases factorialFactorCount_eq_zero_iff.1 h with h | ⟨p, hp, hpn, hBp⟩
  · omega
  · exact (hB p hp hpn).not_gt hBp

/-- When `n ≤ B`, the factorization `n! = 1 · 2 ⋯ n` shows that at most `n` factors are needed. -/
theorem factorialFactorCount_le_self (h : n ≤ B) : factorialFactorCount B n ≤ n := by
  have hle := factorialFactorCount_le_card (B := B) (n := n) (s := (Finset.range n).val.map (· + 1))
    (by simpa using fun i hi ↦ hi.trans_le h) (by
      rw [← Finset.prod_eq_multiset_prod, Finset.prod_range_add_one_eq_factorial])
  simpa using hle

/-- When a factorization exists, `n! ≤ B ^ t` for `t = factorialFactorCount B n`. -/
theorem factorial_le_pow_factorialFactorCount (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    n ! ≤ B ^ factorialFactorCount B n := by
  obtain ⟨s, hcard, hs, hprod⟩ := exists_multiset_card_eq_factorialFactorCount hB
  exact hprod ▸ hcard ▸ prod_le_pow_card s B hs

/-- When a factorization exists, `log n! ≤ factorialFactorCount B n * log B`: each factor
contributes at most `log B`. -/
theorem log_factorial_le_factorialFactorCount_mul_log (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    Real.log n ! ≤ factorialFactorCount B n * Real.log B := by
  have h : (n ! : ℝ) ≤ (B : ℝ) ^ factorialFactorCount B n := by
    exact_mod_cast factorial_le_pow_factorialFactorCount hB
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h

/-- The lower bound `n log n - n ≤ factorialFactorCount B n * log B`, when a factorization exists:
combine `log n! ≤ factorialFactorCount B n * log B` with `n log n - n ≤ log n!`. -/
theorem mul_log_sub_le_factorialFactorCount_mul_log (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    n * Real.log n - n ≤ factorialFactorCount B n * Real.log B := by
  have h := Real.le_sum_log_nat (N := n)
  rw [Real.sum_log_eq_log_factorial] at h
  exact h.trans (log_factorial_le_factorialFactorCount_mul_log hB)

/-- The lower bound `n - n / log n ≤ factorialFactorCount n n`, the lower half of
`factorialFactorCount n n = n - n / log n + o(n / log n)`. It fails at `n = 1`, where the right
side is `0` and the left side is `1` (the junk value `1 / log 1 = 0`). -/
theorem sub_div_log_le_factorialFactorCount_self (hn : n ≠ 1) :
    (n : ℝ) - n / Real.log n ≤ factorialFactorCount n n := by
  obtain rfl | hn2 : n = 0 ∨ 2 ≤ n := by omega
  · simp
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have h := mul_log_sub_le_factorialFactorCount_mul_log (B := n) (n := n) fun _ _ h ↦ h
  calc (n : ℝ) - n / Real.log n = (n * Real.log n - n) / Real.log n := by
        rw [sub_div, mul_div_cancel_right₀ _ hlog.ne']
    _ ≤ factorialFactorCount n n := (div_le_iff₀ hlog).2 h

/-- The lower bound `n / 2 - n / (2 log n) ≤ factorialFactorCount (n ^ 2) n`, the lower half of
Erdős problem 392, `factorialFactorCount (n ^ 2) n = n / 2 - n / (2 log n) + o(n / log n)`. It
fails at `n = 1`, where the right side is `0` and the left side is `1 / 2`. -/
theorem div_two_sub_div_log_le_factorialFactorCount_sq (hn : n ≠ 1) :
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ factorialFactorCount (n ^ 2) n := by
  obtain rfl | hn2 : n = 0 ∨ 2 ≤ n := by omega
  · simp
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have h := mul_log_sub_le_factorialFactorCount_mul_log (B := n ^ 2) (n := n)
    fun _ _ h ↦ h.trans (Nat.le_self_pow two_ne_zero n)
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
  calc (n : ℝ) / 2 - n / (2 * Real.log n) = (n * Real.log n - n) / (2 * Real.log n) := by
        field_simp
    _ ≤ factorialFactorCount (n ^ 2) n := (div_le_iff₀ (by positivity)).2 h

/-- Enlarging the bound can only lower the count, as long as a factorization exists for the
smaller bound. -/
theorem factorialFactorCount_le_factorialFactorCount (hB : ∀ p, p.Prime → p ≤ n → p ≤ B)
    (h : B ≤ B') : factorialFactorCount B' n ≤ factorialFactorCount B n := by
  obtain ⟨s, hcard, hs, hprod⟩ := exists_multiset_card_eq_factorialFactorCount hB
  exact hcard ▸ factorialFactorCount_le_card (fun a ha ↦ (hs a ha).trans h) hprod

/-- The count is antitone in the bound `B` on `B ≥ n`. -/
theorem antitoneOn_factorialFactorCount :
    AntitoneOn (factorialFactorCount · n) (Set.Ici n) :=
  fun _ hB _ _ h ↦ factorialFactorCount_le_factorialFactorCount
    (fun _ _ hp ↦ hp.trans (Set.mem_Ici.1 hB)) h

/-- Pairing the factors: `factorialFactorCount (B ^ 2) n ≤ ⌈t / 2⌉ = (t + 1) / 2` for
`t = factorialFactorCount B n`, when a factorization with factors at most `B` exists. -/
theorem factorialFactorCount_sq_le (hB : ∀ p, p.Prime → p ≤ n → p ≤ B) :
    factorialFactorCount (B ^ 2) n ≤ (factorialFactorCount B n + 1) / 2 := by
  -- Multiply the factors in pairs, keeping one unpaired factor if their number is odd.
  have key : ∀ m (s : Multiset ℕ), card s ≤ 2 * m → (∀ a ∈ s, a ≤ B) →
      ∃ s' : Multiset ℕ, card s' ≤ m ∧ (∀ a ∈ s', a ≤ B ^ 2) ∧ s'.prod = s.prod := by
    intro m
    induction m with
    | zero => exact fun s hs _ ↦ ⟨0, by simp, by simp, by simp_all⟩
    | succ m ih =>
      intro s hcard hs
      rcases empty_or_exists_mem s with rfl | ⟨a, ha⟩
      · exact ⟨0, by simp, by simp, rfl⟩
      obtain ⟨r, rfl⟩ := exists_cons_of_mem ha
      have hB2 : B ≤ B ^ 2 := Nat.le_self_pow two_ne_zero B
      rcases empty_or_exists_mem r with rfl | ⟨b, hb⟩
      · exact ⟨{a}, by simp, by simpa using (hs a ha).trans hB2, by simp⟩
      obtain ⟨q, rfl⟩ := exists_cons_of_mem hb
      simp only [card_cons, mem_cons, forall_eq_or_imp] at hcard hs
      obtain ⟨q', hq'card, hq', hq'prod⟩ := ih q (by omega) hs.2.2
      refine ⟨(a * b) ::ₘ q', by simpa using hq'card, ?_, by simp [hq'prod, mul_assoc]⟩
      simp only [mem_cons, forall_eq_or_imp]
      exact ⟨sq B ▸ Nat.mul_le_mul hs.1 hs.2.1, hq'⟩
  obtain ⟨s, hcard, hs, hprod⟩ := exists_multiset_card_eq_factorialFactorCount hB
  obtain ⟨s', hs'card, hs', hs'prod⟩ := key ((factorialFactorCount B n + 1) / 2) s
    (by omega) hs
  exact (factorialFactorCount_le_card hs' (hs'prod.trans hprod)).trans hs'card

end Nat
