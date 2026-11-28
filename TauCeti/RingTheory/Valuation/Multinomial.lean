/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Linarith

/-!
# Divisibility of binomial and multinomial coefficients in local rings

Let `O` be a local commutative ring in which a prime `p` is not a unit (for instance, a valuation
domain of residue characteristic `p`). A binomial coefficient `Nat.choose (n + m) n` with
`n + m < p ^ f` has `p`-adic valuation at most `f`, and its prime-to-`p` part is a unit in `O`,
so it divides `p ^ f` in `O`. Consequently, any multinomial coefficient over a finite set `s` of
total degree `< p ^ f` divides `p ^ (s.card * f)` in `O`.

## Main results

* `TauCeti.cast_choose_dvd_pow`: if `p` is prime and not a unit in a local ring `O`, and
  `n + m < p ^ f`, then `((n + m).choose n : O) ∣ p ^ f`.
* `TauCeti.cast_multinomial_dvd_pow`: under the same hypotheses, if `∑ i ∈ s, α i < p ^ f`, then
  `(Nat.multinomial s α : O) ∣ p ^ (s.card * f)`.
* `TauCeti.cast_multinomial_univ_dvd_pow`: the `Fintype` specialization over `Finset.univ`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/InvariantAverage.lean`
  (`New.Average.cast_choose_dvd_pow`, `New.Average.cast_multinomial_dvd_pow`).
-/

public section

namespace TauCeti

open Nat Finset IsLocalRing

/-- If a prime `p` is not a unit in a local ring `O` and `n + m < p ^ f`, then the binomial
coefficient `(n + m).choose n` divides `p ^ f` in `O`. -/
theorem cast_choose_dvd_pow {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ}
    (hp_prime : p.Prime) (hp : ¬IsUnit (p : O)) {f n m : ℕ} (h_lt : n + m < p ^ f) :
    ((n + m).choose n : O) ∣ (p : O) ^ f := by
  set c : ℕ := (n + m).choose n
  have h_coprime : p.Coprime (ordCompl[p] c) :=
    coprime_ordCompl hp_prime (choose_ne_zero le_self_add)
  have h_unit : IsUnit ((ordCompl[p] c : ℕ) : O) :=
    notMem_maximalIdeal.mp (Ideal.IsPrime.notMem_of_isCoprime_of_mem h_coprime.cast hp)
  have h_le : c.factorization p ≤ f :=
    calc c.factorization p ≤ log p (n + m) := factorization_choose_le_log
      _ ≤ log p (p ^ f) := log_mono_right h_lt.le
      _ = f := log_pow hp_prime.one_lt f
  rw [← ordProj_mul_ordCompl_eq_self c p, cast_mul, cast_pow, h_unit.mul_right_dvd]
  exact pow_dvd_pow (p : O) h_le

/-- If a prime `p` is not a unit in a local ring `O` and `∑ i ∈ s, α i < p ^ f`, then
`Nat.multinomial s α` divides `p ^ (s.card * f)` in `O`. -/
theorem cast_multinomial_dvd_pow {O κ : Type*} [CommRing O] [IsLocalRing O] {p : ℕ}
    (hp_prime : p.Prime) (hp : ¬IsUnit (p : O)) {f : ℕ} (s : Finset κ) (α : κ → ℕ)
    (h_lt : ∑ i ∈ s, α i < p ^ f) :
    (Nat.multinomial s α : O) ∣ (p : O) ^ (s.card * f) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Nat.multinomial_cons, cast_mul, card_cons, Nat.add_one_mul, pow_add, mul_comm]
    have h_sub : ∑ i ∈ s, α i < p ^ f := by
      have h_add := h_lt
      rw [sum_cons] at h_add
      linarith
    exact mul_dvd_mul (ih h_sub) (cast_choose_dvd_pow hp_prime hp (by simpa [sum_cons] using h_lt))

/-- If a prime `p` is not a unit in a local ring `O` and `∑ i : σ, α i < p ^ f`, then
`Nat.multinomial Finset.univ α` divides `p ^ (Fintype.card σ * f)` in `O`. -/
theorem cast_multinomial_univ_dvd_pow {O σ : Type*} [CommRing O] [IsLocalRing O] [Fintype σ]
    {p : ℕ} (hp_prime : p.Prime) (hp : ¬IsUnit (p : O)) {f : ℕ} (α : σ → ℕ)
    (h_lt : ∑ i : σ, α i < p ^ f) :
    (Nat.multinomial Finset.univ α : O) ∣ (p : O) ^ (Fintype.card σ * f) :=
  cast_multinomial_dvd_pow hp_prime hp Finset.univ α h_lt

end TauCeti
