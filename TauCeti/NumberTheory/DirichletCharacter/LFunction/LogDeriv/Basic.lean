/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Algebra.Order.GroupWithZero.Basic
import TauCeti.NumberTheory.LSeries.ThreeFourOne

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

The file also records the triangle-inequality comparison `‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(σ))` on
`1 < σ ≤ re s`, its tail-extension corollary from `re s ≤ σ₀` to all `s : ℂ`, and the classical
nonpositive weighted sums of real logarithmic derivatives
(`Re (ζ′/ζ(re s)) + Re (L′/L(s, χ)) ≤ 0` and
`3 Re (ζ′/ζ(σ)) + 4 Re (L′/L(σ + i t, χ)) + Re (L′/L(σ + 2 i t, χ²)) ≤ 0`).

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
* `DirichletCharacter.norm_term_twist_vonMangoldt` and
  `DirichletCharacter.re_term_twist_vonMangoldt_add`: norm and real-part formulas for terms of the
  twisted von Mangoldt series.
* `DirichletCharacter.abscissaOfAbsConv_twist_vonMangoldt_le_one` and
  `DirichletCharacter.norm_add_term_twist_vonMangoldt_le`: absolute convergence of the twisted
  series right of `re s = 1`, and the termwise comparison of the `χ` and `χψ` terms with the
  principal and `ψ` terms for a real-valued `ψ`.
* `DirichletCharacter.norm_logDeriv_LFunction_le_of_le_re`,
  `DirichletCharacter.norm_logDeriv_LFunction_le`,
  `DirichletCharacter.neg_re_logDeriv_LFunction_le_max_mul_of_bound_on_left`,
  `DirichletCharacter.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos`, and
  `DirichletCharacter.threeFourOne_re_logDeriv_riemannZeta_LFunction_nonpos`: the half-plane
  triangle inequality, its right-tail extension, and the `1 + χ` and `3-4-1` logarithmic-derivative
  inequalities.
-/

public section

open ArithmeticFunction Finset Filter LSeries
open scoped LSeries.notation Topology

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- The norm of the `n`-th term of the twisted von Mangoldt Dirichlet series is
`‖χ n‖ * Λ n / n ^ s.re` (including `n = 0`, where both sides are `0`). -/
theorem norm_term_twist_vonMangoldt (n : ℕ) :
    ‖term (↗χ * ↗Λ) s n‖ = ‖χ n‖ * Λ n / (n : ℝ) ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [norm_term_eq]
  simp [hn, abs_of_nonneg vonMangoldt_nonneg]

/-- At `s = σ + u` with real `σ`, the real part of the `n`-th twisted von Mangoldt term factors
out the real weight `Λ n / n ^ σ` (including `n = 0`, where both sides are `0`). -/
theorem re_term_twist_vonMangoldt_add (σ : ℝ) (u : ℂ) (n : ℕ) :
    (term (↗χ * ↗Λ) (σ + u) n).re =
      (Λ n / (n : ℝ) ^ σ) * (χ n * (n : ℂ) ^ (-u)).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hpow : (n : ℂ) ^ (-((σ : ℂ) + u)) = (((n : ℝ) ^ σ)⁻¹ : ℝ) * (n : ℂ) ^ (-u) := by
    rw [neg_add, Complex.cpow_add _ _ (mod_cast hn), ← Complex.ofReal_natCast,
      ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0, Real.rpow_neg hn0]
  have hmul : term (↗χ * ↗Λ) (σ + u) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n * (n : ℂ) ^ (-u)) := by
    rw [term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← Complex.cpow_neg, hpow,
      div_eq_mul_inv, Complex.ofReal_mul]
    ring
  rw [hmul, Complex.re_ofReal_mul]

omit χ in
private theorem re_term_modOne_twist_vonMangoldt_ofReal (χ₀ : DirichletCharacter ℂ 1) (σ : ℝ)
    (n : ℕ) : (term (↗χ₀ * ↗Λ) σ n).re = Λ n / (n : ℝ) ^ σ := by
  simpa [Subsingleton.elim χ₀ 1, MulChar.one_apply (isUnit_of_subsingleton _)] using
    χ₀.re_term_twist_vonMangoldt_add σ 0 n

omit χ in
/-- A Dirichlet twist of the von Mangoldt series has abscissa of absolute convergence at most 1. -/
theorem abscissaOfAbsConv_twist_vonMangoldt_le_one (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv (↗χ * ↗Λ) ≤ 1 := by
  apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  exact fun _ hz ↦ LSeriesSummable_twist_vonMangoldt χ (by exact_mod_cast hz)

open scoped ComplexOrder in
omit χ in
/-- For a character `ψ` with `ψ n` real, the `n`-th terms of the twisted von Mangoldt series for
`χ` and `χψ` at `s` have sum of norm at most the real part of the sum of the terms for the
principal character and `ψ` at any real `σ ≤ re s`. -/
theorem norm_add_term_twist_vonMangoldt_le (χ ψ : DirichletCharacter ℂ N)
    {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (n : ℕ) (hψ : (ψ n).im = 0) :
    ‖term (↗χ * ↗Λ) s n + term (↗(χ * ψ) * ↗Λ) s n‖ ≤
      (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) σ n + term (↗ψ * ↗Λ) σ n).re := by
  let A : ℕ → ℂ := ↗(1 : DirichletCharacter ℂ N) * ↗Λ + ↗ψ * ↗Λ
  let B : ℕ → ℂ := ↗χ * ↗Λ + ↗(χ * ψ) * ↗Λ
  have hA : 0 ≤ A n := by
    rw [Complex.le_def]
    simp only [A, Pi.add_apply, Pi.mul_apply, ← add_mul, Complex.zero_re, Complex.zero_im,
      mul_comm _ (↑(Λ n) : ℂ), Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    by_cases hu : IsUnit (n : ZMod N)
    · simp only [MulChar.one_apply hu, Complex.add_re, Complex.add_im, Complex.one_re,
        Complex.one_im, hψ, add_zero, mul_zero, and_true]
      have h := (Complex.abs_re_le_norm (ψ n)).trans (ψ.norm_le_one n)
      exact mul_nonneg vonMangoldt_nonneg (by linarith [(abs_le.mp h).1])
    · rw [MulChar.map_nonunit _ hu, ψ.map_nonunit hu]
      simp
  have hB : B n = χ n * A n := by
    have hχ : χ n * (1 : DirichletCharacter ℂ N) n = χ n := by
      rw [← MulChar.mul_apply, mul_one]
    simp only [A, B, Pi.add_apply, Pi.mul_apply, MulChar.mul_apply]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hχ]
  simp only [← term_add_apply]
  calc
    ‖term B s n‖ ≤ ‖term A s n‖ := norm_term_le s (by
      rw [hB, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n))
    _ ≤ ‖term A σ n‖ := norm_term_le_of_re_le_re A (by simpa using hs) n
    _ = (term A σ n).re := (Complex.re_eq_norm.mpr (term_nonneg hA σ)).symm

/-- On `1 ≤ re s`, the terms of the twisted von Mangoldt series at non-prime `n` are bounded by
`Λ n / n`, independently of the character and of `s`. -/
theorem norm_term_twist_vonMangoldt_nonprime_le (hs : 1 ≤ s.re) (n : ℕ) :
    ‖if n.Prime then 0 else term (↗χ * ↗Λ) s n‖ ≤ (if n.Prime then 0 else Λ n) / n := by
  split_ifs with hn
  · simp
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  have hn1 : (1 : ℝ) ≤ n := mod_cast Nat.one_le_iff_ne_zero.mpr h0
  rw [χ.norm_term_twist_vonMangoldt]
  calc ‖χ n‖ * Λ n / n ^ s.re ≤ 1 * Λ n / n ^ (1 : ℝ) := by
        gcongr
        exact χ.norm_le_one _
    _ = Λ n / n := by simp

private theorem summable_term_twist_vonMangoldt_nonprime (hs : 1 ≤ s.re) :
    Summable fun n ↦ if n.Prime then 0 else term (↗χ * ↗Λ) s n :=
  vonMangoldt.summable_nonprime_div.of_norm_bounded (χ.norm_term_twist_vonMangoldt_nonprime_le hs)

private theorem summable_term_twist_vonMangoldt_prime (hs : 1 < s.re) :
    Summable fun n ↦ if n.Prime then term (↗χ * ↗Λ) s n else 0 :=
  (Summable.sub (LSeriesSummable_twist_vonMangoldt χ hs)
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

/-! ### Nonpositive combinations -/

/-- **Triangle-inequality bound for `L′/L` against `-ζ′/ζ`.** For every Dirichlet character `χ` of
positive level, `1 < σ` and `σ ≤ s.re`, `‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(σ))`. -/
theorem norm_logDeriv_LFunction_le_of_le_re [NeZero N] {σ : ℝ} (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖logDeriv (LFunction χ) s‖ ≤ -(logDeriv riemannZeta σ).re := by
  set χ₀ : DirichletCharacter ℂ 1 := 1
  have hs' : 1 < s.re := hσ.trans_le hs
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have S₀ := LSeriesSummable_twist_vonMangoldt χ₀ hσ'
  have hterm₀ (n : ℕ) : ‖term (↗χ * ↗Λ) s n‖ ≤ (term (↗χ₀ * ↗Λ) σ n).re := by
    calc ‖term (↗χ * ↗Λ) s n‖
        ≤ ‖term (↗χ * ↗Λ) σ n‖ := LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
      _ ≤ ‖term (↗χ₀ * ↗Λ) σ n‖ := by
          refine LSeries.norm_term_le _ ?_
          simpa [Subsingleton.elim χ₀ 1, MulChar.one_apply (isUnit_of_subsingleton _)]
            using mul_le_of_le_one_left (norm_nonneg (Λ n : ℂ)) (χ.norm_le_one n)
      _ = (term (↗χ₀ * ↗Λ) σ n).re := by
          rcases eq_or_ne n 0 with rfl | hn0
          · simp
          rw [norm_term_eq, re_term_modOne_twist_vonMangoldt_ofReal]
          simp [hn0, Real.norm_of_nonneg vonMangoldt_nonneg,
            Subsingleton.elim χ₀ 1, MulChar.one_apply (isUnit_of_subsingleton _)]
  rw [← LFunction_modOne_eq (χ := χ₀), χ₀.logDeriv_LFunction_eq_neg_LSeries hσ',
    χ.logDeriv_LFunction_eq_neg_LSeries hs', norm_neg, Complex.neg_re, neg_neg, LSeries, LSeries]
  exact tsum_of_norm_bounded (Complex.hasSum_re S₀.hasSum) hterm₀

/-- For every Dirichlet character `χ` of positive level and `1 < s.re`,
`‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(s.re))`. -/
theorem norm_logDeriv_LFunction_le [NeZero N] (hs : 1 < s.re) :
    ‖logDeriv (LFunction χ) s‖ ≤ -(logDeriv riemannZeta s.re).re :=
  χ.norm_logDeriv_LFunction_le_of_le_re hs le_rfl

/-- Extending an upper bound `-(logDeriv (LFunction χ) s).re ≤ A₀ * M` from `s.re ≤ σ₀`
(`1 < σ₀`) to arbitrary `s : ℂ` via the Dirichlet-series comparison
`‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(σ₀))` on `σ₀ ≤ s.re`: given `0 < M₀ ≤ M`, this yields
`-(logDeriv (LFunction χ) s).re ≤ max A₀ (-(logDeriv riemannZeta σ₀).re / M₀) * M`. -/
theorem neg_re_logDeriv_LFunction_le_max_mul_of_bound_on_left [NeZero N] {σ₀ A₀ M₀ M : ℝ}
    (hσ₀ : 1 < σ₀) (hM₀ : 0 < M₀) (hM : M₀ ≤ M)
    (hre : s.re ≤ σ₀ → -(logDeriv (LFunction χ) s).re ≤ A₀ * M) :
    -(logDeriv (LFunction χ) s).re ≤ max A₀ (-(logDeriv riemannZeta σ₀).re / M₀) * M := by
  have hMnonneg : 0 ≤ M := hM₀.le.trans hM
  rcases le_or_gt s.re σ₀ with hs | hs
  · exact (hre hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hMnonneg)
  · have hC₀ : 0 ≤ -(logDeriv riemannZeta σ₀).re :=
      (norm_nonneg _).trans (χ.norm_logDeriv_LFunction_le_of_le_re (s := σ₀) hσ₀ (by simp))
    have htail : -(logDeriv (LFunction χ) s).re ≤ -(logDeriv riemannZeta σ₀).re :=
      ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
        (χ.norm_logDeriv_LFunction_le_of_le_re hσ₀ hs.le)
    exact htail.trans ((TauCeti.le_div_mul_of_le hC₀ hM₀ hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hMnonneg))

/-- **The `1 + χ` logarithmic-derivative inequality.** For every Dirichlet character `χ` of
positive level and `1 < s.re`, `Re (ζ′/ζ(s.re)) + Re (L′/L(s, χ)) ≤ 0`. -/
theorem re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos [NeZero N] (hs : 1 < s.re) :
    (logDeriv riemannZeta s.re).re + (logDeriv (LFunction χ) s).re ≤ 0 := by
  linarith [(le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
    (χ.norm_logDeriv_LFunction_le hs))]

/-- **The `3-4-1` logarithmic-derivative inequality.** For every Dirichlet character `χ` of
positive level, real `σ > 1` and real `t`,
`3 Re (ζ′/ζ(σ)) + 4 Re (L′/L(σ + i t, χ)) + Re (L′/L(σ + 2 i t, χ²)) ≤ 0`. -/
theorem threeFourOne_re_logDeriv_riemannZeta_LFunction_nonpos [NeZero N] {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    3 * (logDeriv riemannZeta σ).re + 4 * (logDeriv (LFunction χ) (σ + t * Complex.I)).re +
      (logDeriv (LFunction (χ ^ 2)) (σ + 2 * t * Complex.I)).re ≤ 0 := by
  set χ₀ : DirichletCharacter ℂ 1 := 1
  have hs₀ : 1 < (σ : ℂ).re := by simpa using hσ
  have hs₁ : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  have hs₂ : 1 < ((σ : ℂ) + 2 * t * Complex.I).re := by simpa using hσ
  have S₀ := LSeriesSummable_twist_vonMangoldt χ₀ hs₀
  have S₁ := LSeriesSummable_twist_vonMangoldt χ hs₁
  have S₂ := LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs₂
  have R₀ := ((Complex.hasSum_re S₀.hasSum).summable).mul_left 3
  have R₁ := ((Complex.hasSum_re S₁.hasSum).summable).mul_left 4
  have R₂ := (Complex.hasSum_re S₂.hasSum).summable
  rw [← LFunction_modOne_eq (χ := χ₀), χ₀.logDeriv_LFunction_eq_neg_LSeries hs₀,
    χ.logDeriv_LFunction_eq_neg_LSeries hs₁, (χ ^ 2).logDeriv_LFunction_eq_neg_LSeries hs₂]
  simp only [Complex.neg_re, LSeries, Complex.re_tsum S₀, Complex.re_tsum S₁, Complex.re_tsum S₂]
  suffices 0 ≤ ∑' n, (3 * (term (↗χ₀ * ↗Λ) σ n).re +
      4 * (term (↗χ * ↗Λ) (σ + t * Complex.I) n).re +
      (term (↗(χ ^ 2) * ↗Λ) (σ + 2 * t * Complex.I) n).re) by
    rw [(R₀.add R₁).tsum_add R₂, R₀.tsum_add R₁, tsum_mul_left, tsum_mul_left] at this; linarith
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : 0 < (n : ℝ) := mod_cast Nat.pos_of_ne_zero hn
  set z : ℂ := χ n * (n : ℂ) ^ (-(t * Complex.I)) with hz_def
  have hz : ‖z‖ ≤ 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
    simpa using χ.norm_le_one n
  have ht₂ : (χ ^ 2) n * (n : ℂ) ^ (-(2 * (t : ℂ) * Complex.I)) = z ^ 2 := by
    have hexp : -(2 * (t : ℂ) * Complex.I) = (2 : ℕ) * -(t * Complex.I) := by
      push_cast; ring
    rw [sq χ, MulChar.mul_apply, hexp, Complex.cpow_nat_mul, hz_def]
    ring
  rw [re_term_modOne_twist_vonMangoldt_ofReal, χ.re_term_twist_vonMangoldt_add σ (t * Complex.I) n,
    ← hz_def, (χ ^ 2).re_term_twist_vonMangoldt_add σ (2 * t * Complex.I) n, ht₂]
  have h341 := TauCeti.LSeries.threeFourOneCombination_nonneg hz
  rw [TauCeti.LSeries.threeFourOneCombination_def] at h341
  nlinarith [div_nonneg (vonMangoldt_nonneg (n := n)) (Real.rpow_nonneg hn_pos.le σ)]

end DirichletCharacter
