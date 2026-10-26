/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# `S`-factored numbers and `p`-adic valuations

Mathlib's `Nat.factoredNumbers S` is the set of positive integers all of whose prime factors lie
in the finite set `S`. This file describes these numbers through `p`-adic valuations:

* `TauCeti.padicValRat_eq_zero_iff`: a nonzero rational number has `p`-adic valuation zero
  exactly when `p` divides neither its numerator nor its denominator;
* `TauCeti.forall_padicValRat_eq_zero_iff_mem_factoredNumbers`: a nonzero rational number has
  `p`-adic valuation zero at every prime `p ∉ S` exactly when its numerator (in absolute value)
  and its denominator are `S`-factored;
* `TauCeti.prod_pow_padicValNat_eq_self_of_mem_factoredNumbers`: if `S` consists of primes, an
  `S`-factored number is the product of the powers `p ^ v_p(n)` over `p ∈ S`.

These are the arithmetic inputs for describing the rational `S`-units.
-/

public section

namespace TauCeti

/-- A nonzero rational number has `p`-adic valuation zero exactly when the prime `p` divides
neither its numerator nor its denominator. -/
theorem padicValRat_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q = 0 ↔ ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
  have hnum : padicValInt p q.num = 0 ↔ ¬ p ∣ q.num.natAbs := by
    simp [padicValInt, padicValNat.eq_zero_iff, hp.out.ne_one, hq]
  have hden : padicValNat p q.den = 0 ↔ ¬ p ∣ q.den := by
    simp [padicValNat.eq_zero_iff, hp.out.ne_one]
  rw [padicValRat_def, ← hnum, ← hden]
  rcases Rat.num_or_den_zero_padicVal q hp.out with h | h <;> simp [h]

/-- A nonzero rational number has `p`-adic valuation zero at every prime `p ∉ S` exactly when the
absolute value of its numerator and its denominator are `S`-factored. -/
theorem forall_padicValRat_eq_zero_iff_mem_factoredNumbers {S : Finset ℕ} {q : ℚ} (hq : q ≠ 0) :
    (∀ p : ℕ, p.Prime → p ∉ S → padicValRat p q = 0) ↔
      q.num.natAbs ∈ Nat.factoredNumbers S ∧ q.den ∈ Nat.factoredNumbers S := by
  have hn : q.num.natAbs ≠ 0 := by simpa using hq
  simp only [Nat.mem_factoredNumbers_iff_primeFactors_subset, Finset.subset_iff,
    Nat.mem_primeFactors]
  refine ⟨fun h ↦ ⟨⟨hn, fun p ⟨hp, hpq, _⟩ ↦ ?_⟩, ⟨q.den_ne_zero, fun p ⟨hp, hpq, _⟩ ↦ ?_⟩⟩,
    fun ⟨⟨_, hnum⟩, ⟨_, hden⟩⟩ p hp hpS ↦ ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    by_contra hpS
    exact ((padicValRat_eq_zero_iff hq).1 (h p hp hpS)).1 hpq
  · have : Fact p.Prime := ⟨hp⟩
    by_contra hpS
    exact ((padicValRat_eq_zero_iff hq).1 (h p hp hpS)).2 hpq
  · have : Fact p.Prime := ⟨hp⟩
    rw [padicValRat_eq_zero_iff hq]
    exact ⟨fun hd ↦ hpS (hnum ⟨hp, hd, hn⟩), fun hd ↦ hpS (hden ⟨hp, hd, q.den_ne_zero⟩)⟩

/-- If `S` consists of primes, an `S`-factored number `n` is the product of the prime powers
`p ^ v_p(n)` over `p ∈ S`. -/
theorem prod_pow_padicValNat_eq_self_of_mem_factoredNumbers {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : n ∈ Nat.factoredNumbers S) :
    ∏ p ∈ S, p ^ padicValNat p n = n := by
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset] at hn
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn.1]
  rw [Finsupp.prod_of_support_subset _ (by simpa using hn.2) _ (fun _ _ ↦ pow_zero _)]
  exact Finset.prod_congr rfl fun p hp ↦ by rw [Nat.factorization_def n (hS p hp)]

end TauCeti
