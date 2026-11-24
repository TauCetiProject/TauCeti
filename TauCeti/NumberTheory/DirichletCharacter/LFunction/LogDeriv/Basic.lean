/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Uniform Euler logarithmic derivatives of Dirichlet `L`-functions

For a Dirichlet character `χ` of any positive level `N` and `1 < re s`, the logarithmic derivative
of `L(s, χ)` is minus the series `∑ χ(n) Λ(n) / n ^ s` (Mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`). This file splits that series into its prime
terms `χ(p) log p / p ^ s` and the terms at the higher prime powers `p ^ k`, `k ≥ 2`. The latter are
bounded in norm by `Λ(n) / n` at the non-prime `n`, uniformly in `N`, `χ` and `s`, so
`‖L′/L(s, χ) + ∑ₚ χ(p) log p / p ^ s‖ ≤ C` with
`C = ∑ₙ (if n is prime then 0 else Λ(n)) / n`, the sum of `log p / p ^ k` over all primes `p` and
`k ≥ 2`. This constant is chosen before the level, the character and the point. Neither
primitivity nor nontriviality of `χ` is needed.

At real `σ > 1` the real parts satisfy the same bound, for every character. For a real-valued
character the logarithmic derivative is moreover real, and the prime series is the cast of the
corresponding real series.

The constant's summability, `ArithmeticFunction.vonMangoldt.summable_nonprime_div`, is in
`TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt`.

## Main results

* `DirichletCharacter.logDeriv_LFunction_eq_neg_LSeries`: `L′/L(s, χ) = -∑ χ(n) Λ(n) / n ^ s`.
* `DirichletCharacter.summable_prime_mul_log_div_cpow`: the prime series converges.
* `DirichletCharacter.logDeriv_LFunction_add_tsum_prime_eq`: `L′/L` plus the prime series is minus
  the higher-prime-power part of the twisted von Mangoldt series.
* `DirichletCharacter.norm_logDeriv_LFunction_add_tsum_prime_le` and
  `DirichletCharacter.exists_norm_logDeriv_LFunction_add_tsum_prime_le`: the uniform bound.
* `DirichletCharacter.abs_re_logDeriv_LFunction_add_tsum_prime_le`: the real-part form at real
  arguments.
* `DirichletCharacter.im_logDeriv_LFunction_ofReal`: `L′/L(σ, χ)` is real for a real-valued
  character.
-/

public section

open ArithmeticFunction LSeries

open scoped LSeries.notation

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- On `1 ≤ re s`, the terms of the twisted von Mangoldt series at non-prime `n` are bounded by
`Λ n / n`, independently of the character and of `s`. -/
theorem norm_term_twist_vonMangoldt_nonprime_le (hs : 1 ≤ s.re) (n : ℕ) :
    ‖if n.Prime then 0 else term (↗χ * ↗Λ) s n‖ ≤ (if n.Prime then 0 else Λ n) / n := by
  split_ifs with hn
  · simp
  rw [norm_term_eq]
  split_ifs with h0
  · simp [h0]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  calc ‖χ n‖ * Λ n / n ^ s.re ≤ 1 * Λ n / n ^ (1 : ℝ) := by
        gcongr
        exact χ.norm_le_one _
    _ = Λ n / n := by simp

private theorem summable_term_twist_vonMangoldt_nonprime (hs : 1 ≤ s.re) :
    Summable fun n ↦ if n.Prime then 0 else term (↗χ * ↗Λ) s n :=
  vonMangoldt.summable_nonprime_div.of_norm_bounded (χ.norm_term_twist_vonMangoldt_nonprime_le hs)

private theorem summable_term_twist_vonMangoldt_prime (hs : 1 < s.re) :
    Summable fun n ↦ if n.Prime then term (↗χ * ↗Λ) s n else 0 :=
  ((LSeriesSummable_twist_vonMangoldt χ hs).sub
    (χ.summable_term_twist_vonMangoldt_nonprime hs.le)).congr fun n ↦ by split_ifs <;> simp

/-- The prime terms of the twisted von Mangoldt series, indexed by the primes. -/
private theorem hasSum_prime_mul_log_div_cpow (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes ↦ χ p * Real.log p / (p : ℂ) ^ s)
      (∑' n, if n.Prime then term (↗χ * ↗Λ) s n else 0) := by
  refine (Function.Injective.hasSum_iff (g := ((↑) : Nat.Primes → ℕ))
    Nat.Primes.coe_nat_injective fun n hn ↦ ?_).mpr
      (χ.summable_term_twist_vonMangoldt_prime hs).hasSum |>.congr_fun fun p ↦ ?_
  · exact ite_eq_right fun h ↦ (hn ⟨⟨n, h⟩, rfl⟩).elim
  · simp [p.prop, term_of_ne_zero p.prop.ne_zero, vonMangoldt_apply_prime p.prop]

/-- For `1 < re s`, the prime series `∑ₚ χ(p) log p / p ^ s` converges. -/
theorem summable_prime_mul_log_div_cpow (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ χ p * Real.log p / (p : ℂ) ^ s :=
  (χ.hasSum_prime_mul_log_div_cpow hs).summable

/-- The terms of the prime series vanish at the primes dividing the level. -/
theorem prime_mul_log_div_cpow_eq_zero_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (s : ℂ) :
    χ p * Real.log p / (p : ℂ) ^ s = 0 := by
  rw [MulChar.map_nonunit _ fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpN, zero_mul,
    zero_div]

/-- For `1 < re s`, the logarithmic derivative of `L(s, χ)` is minus the twisted von Mangoldt
series `∑ χ(n) Λ(n) / n ^ s`. -/
theorem logDeriv_LFunction_eq_neg_LSeries [NeZero N] (hs : 1 < s.re) :
    logDeriv (LFunction χ) s = -LSeries (↗χ * ↗Λ) s := by
  rw [logDeriv_apply, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    LSeries_twist_vonMangoldt_eq χ hs, neg_div, neg_neg]

/-- For `1 < re s`, the logarithmic derivative of `L(s, χ)` plus the prime series is minus the
part of the twisted von Mangoldt series at the higher prime powers. -/
theorem logDeriv_LFunction_add_tsum_prime_eq [NeZero N] (hs : 1 < s.re) :
    logDeriv (LFunction χ) s + ∑' p : Nat.Primes, χ p * Real.log p / (p : ℂ) ^ s =
      -∑' n, if n.Prime then 0 else term (↗χ * ↗Λ) s n := by
  have hsplit : LSeries (↗χ * ↗Λ) s = (∑' n, if n.Prime then term (↗χ * ↗Λ) s n else 0) +
      ∑' n, if n.Prime then 0 else term (↗χ * ↗Λ) s n := by
    rw [LSeries, ← (χ.summable_term_twist_vonMangoldt_prime hs).tsum_add
      (χ.summable_term_twist_vonMangoldt_nonprime hs.le)]
    exact tsum_congr fun n ↦ by split_ifs <;> simp
  rw [χ.logDeriv_LFunction_eq_neg_LSeries hs, (χ.hasSum_prime_mul_log_div_cpow hs).tsum_eq,
    hsplit]
  ring

/-- **Uniform Euler logarithmic derivative.** For `1 < re s`,
`‖L′/L(s, χ) + ∑ₚ χ(p) log p / p ^ s‖` is at most `∑ₙ (if n is prime then 0 else Λ(n)) / n`,
a constant independent of the level, the character and `s`. -/
theorem norm_logDeriv_LFunction_add_tsum_prime_le [NeZero N] (hs : 1 < s.re) :
    ‖logDeriv (LFunction χ) s + ∑' p : Nat.Primes, χ p * Real.log p / (p : ℂ) ^ s‖ ≤
      ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n := by
  rw [χ.logDeriv_LFunction_add_tsum_prime_eq hs, norm_neg]
  exact tsum_of_norm_bounded vonMangoldt.summable_nonprime_div.hasSum
    (χ.norm_term_twist_vonMangoldt_nonprime_le hs.le)

/-- One absolute constant bounds `‖L′/L(s, χ) + ∑ₚ χ(p) log p / p ^ s‖` for every positive level,
every Dirichlet character of that level and every `s` with `1 < re s`. -/
theorem exists_norm_logDeriv_LFunction_add_tsum_prime_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 < s.re →
      ‖logDeriv (LFunction χ) s + ∑' p : Nat.Primes, χ p * Real.log p / (p : ℂ) ^ s‖ ≤ C :=
  ⟨_, fun _ _ χ _ hs ↦ χ.norm_logDeriv_LFunction_add_tsum_prime_le hs⟩

/-! ### Real parts at real arguments -/

/-- At real `σ`, the real part of a term of the prime series is `re χ(p) log p / p ^ σ`. -/
theorem re_prime_mul_log_div_cpow_ofReal (p : ℕ) (σ : ℝ) :
    (χ p * Real.log p / (p : ℂ) ^ (σ : ℂ)).re = (χ p).re * Real.log p / (p : ℝ) ^ σ := by
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_cpow p.cast_nonneg, Complex.div_ofReal_re,
    Complex.re_mul_ofReal]

/-- For real `σ > 1`, the real prime series converges. -/
theorem summable_prime_re_mul_log_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes ↦ (χ p).re * Real.log p / (p : ℝ) ^ σ := by
  simpa only [re_prime_mul_log_div_cpow_ofReal] using
    (Complex.hasSum_re (χ.summable_prime_mul_log_div_cpow (s := σ) (by simpa)).hasSum).summable

/-- **Uniform Euler logarithmic derivative, real form.** For real `σ > 1`,
`|re L′/L(σ, χ) + ∑ₚ re χ(p) log p / p ^ σ|` is at most the absolute constant
`∑ₙ (if n is prime then 0 else Λ(n)) / n`. -/
theorem abs_re_logDeriv_LFunction_add_tsum_prime_le [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    |(logDeriv (LFunction χ) σ).re + ∑' p : Nat.Primes, (χ p).re * Real.log p / (p : ℝ) ^ σ| ≤
      ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n := by
  have hs : 1 < (σ : ℂ).re := by simpa
  have hre : ∑' p : Nat.Primes, (χ p).re * Real.log p / (p : ℝ) ^ σ =
      (∑' p : Nat.Primes, χ p * Real.log p / (p : ℂ) ^ (σ : ℂ)).re := by
    rw [Complex.re_tsum (χ.summable_prime_mul_log_div_cpow hs)]
    exact tsum_congr fun p ↦ (χ.re_prime_mul_log_div_cpow_ofReal p σ).symm
  rw [hre, ← Complex.add_re]
  exact (Complex.abs_re_le_norm _).trans (χ.norm_logDeriv_LFunction_add_tsum_prime_le hs)

/-! ### Real-valued characters at real arguments -/

section Real

variable {χ} (hχ : ∀ a, (χ a).im = 0)

include hχ

/-- For a real-valued character, the terms of the prime series at real `σ` are real. -/
theorem ofReal_re_mul_log_div_rpow (p : ℕ) (σ : ℝ) :
    (((χ p).re * Real.log p / (p : ℝ) ^ σ : ℝ) : ℂ) = χ p * Real.log p / (p : ℂ) ^ (σ : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_cpow p.cast_nonneg,
    Complex.ofReal_natCast]
  congr 2
  exact Complex.ext rfl (hχ p).symm

/-- For a real-valued character, the complex prime series at real `σ` is the cast of the real
prime series. -/
theorem ofReal_tsum_prime_re_mul_log_div_rpow (σ : ℝ) :
    ((∑' p : Nat.Primes, (χ p).re * Real.log p / (p : ℝ) ^ σ : ℝ) : ℂ) =
      ∑' p : Nat.Primes, χ p * Real.log p / (p : ℂ) ^ (σ : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun p ↦ ofReal_re_mul_log_div_rpow hχ p σ

/-- For a real-valued character and real `σ > 1`, the logarithmic derivative `L′/L(σ, χ)` is
real. -/
theorem im_logDeriv_LFunction_ofReal [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (LFunction χ) σ).im = 0 := by
  have hs : 1 < (σ : ℂ).re := by simpa
  rw [χ.logDeriv_LFunction_eq_neg_LSeries hs, Complex.neg_im, LSeries,
    Complex.im_tsum (LSeriesSummable_twist_vonMangoldt χ hs), neg_eq_zero]
  refine (tsum_congr fun n ↦ ?_).trans tsum_zero
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, Pi.mul_apply, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg, Complex.div_ofReal_im]
  simp [hχ]

end Real

end DirichletCharacter
