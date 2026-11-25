/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Bertrand

/-!
# Degree doubling at new primes is incompatible with logarithmic growth

Let `r : ℕ → ℕ` be a function such that, whenever `r N > 1` and `p` is a prime not dividing
`2N`, the value at `Np` is at least twice the value at `N`. If `r N ≤ K log(2N)` for every
`N ≥ 1`, then `r N ≤ 1` for every `N ≥ 1`
(`TauCeti.le_one_of_two_mul_le_of_le_mul_log`).

This is the counting step of Calegari, Dimitrov and Tang's proof of the unbounded denominators
theorem. There `r N` is the degree `[R₂N : M₂N]`, where `R₂N` is the field spanned over `ℚ(λ)` by
the expansions of the rational weight-zero weak forms with bounded denominators that are invariant
under a finite-index subgroup of geometric level dividing `2N`, and `M₂N` is its subfield spanned
by the rational weight-zero weak forms on `Γ(2N)`. The degree `[R₂N : M₂N]` doubles at each new
prime by `p`-scaling, the degree `[M₂N : ℚ(λ)]` grows at least like `c N³`, and the holonomy rank
bound gives `[R₂N : ℚ(λ)] ≤ C N³ log(2N)`. The form with these two degrees as separate inputs is
`TauCeti.le_one_of_two_mul_le_of_mul_le_mul_log`; its conclusion `[R₂N : M₂N] ≤ 1` says that the
two fields agree.

## Main results

* `TauCeti.le_one_of_two_mul_le_of_le_mul_log`: a function that doubles at new primes and is
  bounded by `K log(2N)` is at most `1`.
* `TauCeti.le_one_of_two_mul_le_of_mul_le_mul_log`: if moreover `m N ≥ c N³` with `c > 0` and
  `r N · m N ≤ C N³ log(2N)`, then `r N ≤ 1`.

## Implementation notes

Suppose `r N₀ ≥ 2`. For `i ≥ 0`, Bertrand's postulate gives a prime `pᵢ` with
`2N₀ · 2ⁱ < pᵢ ≤ 2N₀ · 2ⁱ⁺¹`. These primes are distinct and prime to `2N₀`, so
`N_k = N₀ p₀ ⋯ p_{k-1}` satisfies `r N_k ≥ 2ᵏ r N₀ ≥ 2ᵏ⁺¹`, while
`2N_k ≤ (4N₀)^((k+1)²)`, so `log(2N_k)` grows only quadratically in `k`. Calegari, Dimitrov and
Tang take all primes up to `X` and invoke the prime number theorem; the dyadic primes from
Bertrand's postulate suffice.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), 627–702, Proposition 4.3.5 and (4.3.6)–(4.3.7), pp. 657–658.
-/

public section

open Filter Finset Real Topology

namespace TauCeti

variable {r : ℕ → ℕ}

/-- The dyadic intervals `(B · 2ⁱ, B · 2ⁱ⁺¹]` lie below one another: for `i < k`,
`2 (B · 2ⁱ) ≤ B · 2ᵏ`. -/
private lemma two_mul_mul_two_pow_le (B : ℕ) {i k : ℕ} (h : i < k) :
    2 * (B * 2 ^ i) ≤ B * 2 ^ k := by
  rw [mul_comm 2, mul_assoc, ← pow_succ]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos h)

/-- A prime `pₖ > 2N₀ · 2ᵏ` from a family with `pᵢ ≤ 2N₀ · 2ⁱ⁺¹` does not divide
`2 N₀ p₀ ⋯ p_{k-1}`. -/
private lemma not_dvd_two_mul_mul_prod {N₀ : ℕ} (hN₀ : 0 < N₀) {p : ℕ → ℕ}
    (hp : ∀ i, (p i).Prime ∧ 2 * N₀ * 2 ^ i < p i ∧ p i ≤ 2 * (2 * N₀ * 2 ^ i)) (k : ℕ) :
    ¬ p k ∣ 2 * (N₀ * ∏ i ∈ range k, p i) := by
  have hpk := (hp k).1
  rw [← mul_assoc, hpk.prime.dvd_mul]
  rintro (h | h)
  · have h₁ := Nat.le_of_dvd (by positivity) h
    have h₂ : 2 * N₀ ≤ 2 * N₀ * 2 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
    have h₃ := (hp k).2.1
    omega
  · obtain ⟨i, hi, h⟩ := Prime.exists_mem_finset_dvd hpk.prime h
    rw [Nat.prime_dvd_prime_iff_eq hpk (hp i).1] at h
    have h₁ := two_mul_mul_two_pow_le (2 * N₀) (mem_range.mp hi)
    have h₂ := (hp i).2.2
    have h₃ := (hp k).2.1
    omega

/-- Iterating the doubling along the primes `p₀, p₁, …`: `r (N₀ p₀ ⋯ p_{k-1}) ≥ 2ᵏ r N₀`. -/
private lemma two_pow_mul_le_prod {N₀ : ℕ} (hN₀ : 0 < N₀) {p : ℕ → ℕ}
    (hp : ∀ i, (p i).Prime ∧ 2 * N₀ * 2 ^ i < p i ∧ p i ≤ 2 * (2 * N₀ * 2 ^ i))
    (hdouble : ∀ N p, 0 < N → p.Prime → ¬ p ∣ 2 * N → 1 < r N → 2 * r N ≤ r (N * p))
    (h₂ : 2 ≤ r N₀) (k : ℕ) :
    2 ^ k * r N₀ ≤ r (N₀ * ∏ i ∈ range k, p i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < N₀ * ∏ i ∈ range k, p i := mul_pos hN₀ (prod_pos fun i _ ↦ (hp i).1.pos)
    have h₁ : 1 < r (N₀ * ∏ i ∈ range k, p i) :=
      lt_of_lt_of_le (by nlinarith [Nat.one_le_two_pow (n := k)]) ih
    rw [prod_range_succ, ← mul_assoc, pow_succ', mul_assoc]
    exact (Nat.mul_le_mul_left 2 ih).trans
      (hdouble _ _ hpos (hp k).1 (not_dvd_two_mul_mul_prod hN₀ hp k) h₁)

/-- The size of `2 N₀ p₀ ⋯ p_{k-1}` when `pᵢ ≤ 2N₀ · 2ⁱ⁺¹`: it is at most `(4N₀)^((k+1)²)`. -/
private lemma two_mul_mul_prod_le {N₀ : ℕ} (hN₀ : 0 < N₀) {p : ℕ → ℕ}
    (hp : ∀ i, p i ≤ 2 * (2 * N₀ * 2 ^ i)) (k : ℕ) :
    2 * (N₀ * ∏ i ∈ range k, p i) ≤ (2 * (2 * N₀)) ^ ((k + 1) ^ 2) := by
  have hprod : ∏ i ∈ range k, p i ≤ (2 * N₀ * 2 ^ k) ^ k := by
    simpa using prod_le_pow_card (range k) p (2 * N₀ * 2 ^ k) fun i hi ↦
      (hp i).trans (two_mul_mul_two_pow_le (2 * N₀) (mem_range.mp hi))
  have hbase : 2 * N₀ * 2 ^ k ≤ (2 * (2 * N₀)) ^ (k + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) k)
  have hexp : 1 + (k + 1) * k ≤ (k + 1) ^ 2 := by nlinarith
  calc 2 * (N₀ * ∏ i ∈ range k, p i) = 2 * N₀ * ∏ i ∈ range k, p i := by ring
    _ ≤ 2 * (2 * N₀) * ((2 * (2 * N₀)) ^ (k + 1)) ^ k :=
        Nat.mul_le_mul (by omega) (hprod.trans (Nat.pow_le_pow_left hbase k))
    _ = (2 * (2 * N₀)) ^ (1 + (k + 1) * k) := by ring
    _ ≤ (2 * (2 * N₀)) ^ ((k + 1) ^ 2) := Nat.pow_le_pow_right (by omega) hexp

/-- **Degree doubling contradicts logarithmic growth.** Let `r : ℕ → ℕ` at least double from
`N` to `Np` whenever `r N > 1` and `p` is a prime not dividing `2N`. If
`r N ≤ K log(2N)` for every `N ≥ 1`, then `r N ≤ 1` for every `N ≥ 1`. -/
theorem le_one_of_two_mul_le_of_le_mul_log {K : ℝ}
    (hdouble : ∀ N p, 0 < N → p.Prime → ¬ p ∣ 2 * N → 1 < r N → 2 * r N ≤ r (N * p))
    (hbound : ∀ N, 0 < N → (r N : ℝ) ≤ K * log (2 * N)) {N : ℕ} (hN : 0 < N) : r N ≤ 1 := by
  by_contra! h₂
  choose p hp using fun i : ℕ ↦ Nat.exists_prime_lt_and_le_two_mul (2 * N * 2 ^ i) (by positivity)
  set c : ℝ := max K 0 * log (2 * (2 * N))
  -- Along `N_k = N p₀ ⋯ p_{k-1}`, the doubling and the logarithmic bound give
  -- `2^(k+1) ≤ c (k+1)²`.
  have key (k : ℕ) : (2 : ℝ) ^ (k + 1) ≤ c * (k + 1) ^ 2 := by
    set Nk := N * ∏ i ∈ range k, p i
    have hNk : 0 < Nk := mul_pos hN (prod_pos fun i _ ↦ (hp i).1.pos)
    have hsize : ((2 * Nk : ℕ) : ℝ) ≤ ((2 * (2 * N)) ^ ((k + 1) ^ 2) : ℕ) := by
      exact_mod_cast two_mul_mul_prod_le hN (fun i ↦ (hp i).2.2) k
    have hlog : log (2 * Nk) ≤ (k + 1) ^ 2 * log (2 * (2 * N)) := by
      have := log_le_log (by positivity) hsize
      rw [Nat.cast_pow, log_pow] at this
      push_cast at this
      exact this
    have hdoubling : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ r Nk := by
      exact_mod_cast (Nat.mul_le_mul_left (2 ^ k) h₂).trans
        (two_pow_mul_le_prod hN hp hdouble h₂ k)
    push_cast at hdoubling
    calc (2 : ℝ) ^ (k + 1) ≤ r Nk := hdoubling
      _ ≤ K * log (2 * Nk) := hbound Nk hNk
      _ ≤ max K 0 * log (2 * Nk) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (log_nonneg (by norm_cast; omega))
      _ ≤ max K 0 * ((k + 1) ^ 2 * log (2 * (2 * N))) :=
          mul_le_mul_of_nonneg_left hlog (le_max_right _ _)
      _ = c * (k + 1) ^ 2 := by ring
  -- But `(k+1)² / 2^(k+1) → 0`.
  have hlim : Tendsto (fun k : ℕ ↦ c * (((k + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (k + 1))) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_const_div_const_pow_of_one_lt 2 one_lt_two).comp
      (tendsto_add_atTop_nat 1)).const_mul c
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  rw [mul_div_assoc', div_lt_one (by positivity)] at hk
  push_cast at hk
  linarith [key k]

/-- **Degree doubling contradicts the cubic-logarithmic bound.** Let `r, m : ℕ → ℕ`, where `r`
at least doubles from `N` to `Np` whenever `r N > 1` and `p` is a prime not dividing `2N`, and
`m N ≥ c N³` for a constant `c > 0`. If `r N · m N ≤ C N³ log(2N)` for every `N ≥ 1`, then
`r N ≤ 1` for every `N ≥ 1`. -/
theorem le_one_of_two_mul_le_of_mul_le_mul_log {m : ℕ → ℕ} {c C : ℝ} (hc : 0 < c)
    (hdouble : ∀ N p, 0 < N → p.Prime → ¬ p ∣ 2 * N → 1 < r N → 2 * r N ≤ r (N * p))
    (hm : ∀ N, 0 < N → c * N ^ 3 ≤ m N)
    (hbound : ∀ N, 0 < N → (r N : ℝ) * m N ≤ C * N ^ 3 * log (2 * N)) {N : ℕ} (hN : 0 < N) :
    r N ≤ 1 := by
  refine le_one_of_two_mul_le_of_le_mul_log (K := C / c) hdouble (fun N hN ↦ ?_) hN
  have hN3 : (0 : ℝ) < N ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  refine le_of_mul_le_mul_right ?_ hN3
  calc (r N : ℝ) * c * N ^ 3 = r N * (c * N ^ 3) := by ring
    _ ≤ (r N : ℝ) * m N := mul_le_mul_of_nonneg_left (hm N hN) (Nat.cast_nonneg _)
    _ ≤ C * N ^ 3 * log (2 * N) := hbound N hN
    _ = C * log (2 * N) * N ^ 3 := by ring

end TauCeti
