/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

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

The file also records the classical nonnegative combinations of logarithmic derivatives on
`1 < σ` used in zero-free-region arguments (`Re (ζ′/ζ(σ)) + Re (L′/L(σ, χ)) ≤ 0` and
`3 Re (ζ′/ζ(σ)) + 4 Re (L′/L(σ + i t, χ)) + Re (L′/L(σ + 2 i t, χ²)) ≤ 0`), together with the
comparison `‖L′/L(s, 1_N) - ζ′/ζ(s)‖ ≤ log N` for the principal character on `1 ≤ re s`.

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
* `DirichletCharacter.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos` and
  `DirichletCharacter.three_mul_re_logDeriv_riemannZeta_add_four_add_nonpos`: the `1 + χ` and
  `3-4-1` logarithmic-derivative inequalities on `1 < σ`.
* `DirichletCharacter.norm_logDeriv_trivChar_sub_logDeriv_riemannZeta_le`: the deleted-Euler-factor
  logarithmic-derivative bound `‖L′/L(s, 1_N) - ζ′/ζ(s)‖ ≤ log N` on `1 ≤ re s`.
-/

public section

open ArithmeticFunction Finset Filter LSeries
open scoped LSeries.notation Topology

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

/-! ### Nonnegative combinations and deleted Euler factors -/

omit χ in
private theorem three_add_four_re_add_re_sq_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnorm : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [Complex.sq_norm, Complex.normSq_apply] at hnorm
  rw [sq, Complex.mul_re]
  nlinarith [sq_nonneg (1 + z.re)]

/-- **The `1 + χ` logarithmic-derivative inequality.** For every Dirichlet character `χ` of
positive level and real `σ > 1`, `Re (ζ′/ζ(σ)) + Re (L′/L(σ, χ)) ≤ 0`. -/
theorem re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos [NeZero N] {σ : ℝ}
    (hσ : 1 < σ) :
    (logDeriv riemannZeta σ).re + (logDeriv (LFunction χ) σ).re ≤ 0 := by
  set χ₀ : DirichletCharacter ℂ 1 := 1
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h0 : Summable fun n ↦ (term (↗χ₀ * ↗Λ) σ n).re :=
    (Complex.hasSum_re (LSeriesSummable_twist_vonMangoldt χ₀ hs).hasSum).summable
  have h1 : Summable fun n ↦ (term (↗χ * ↗Λ) σ n).re :=
    (Complex.hasSum_re (LSeriesSummable_twist_vonMangoldt χ hs).hasSum).summable
  rw [← LFunction_modOne_eq (χ := χ₀), χ₀.logDeriv_LFunction_eq_neg_LSeries hs,
    χ.logDeriv_LFunction_eq_neg_LSeries hs, Complex.neg_re, Complex.neg_re, LSeries, LSeries,
    Complex.re_tsum (LSeriesSummable_twist_vonMangoldt χ₀ hs),
    Complex.re_tsum (LSeriesSummable_twist_vonMangoldt χ hs)]
  suffices 0 ≤ ∑' n, ((term (↗χ₀ * ↗Λ) σ n).re + (term (↗χ * ↗Λ) σ n).re) by
    rw [h0.tsum_add h1] at this; linarith
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hχ₀n : χ₀ n = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  have hre : -1 ≤ (χ n).re := (abs_le.mp ((Complex.abs_re_le_norm _).trans (χ.norm_le_one n))).1
  rw [term_of_ne_zero hn, term_of_ne_zero hn, Pi.mul_apply, Pi.mul_apply, hχ₀n, one_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_cpow n.cast_nonneg, Complex.div_ofReal_re,
    Complex.div_ofReal_re, Complex.ofReal_re, Complex.re_mul_ofReal, ← add_div]
  have hnum : 0 ≤ Λ n + (χ n).re * Λ n := by
    have : 0 ≤ (1 + (χ n).re) * Λ n := mul_nonneg (by linarith) vonMangoldt_nonneg
    linarith
  exact div_nonneg hnum (Real.rpow_nonneg n.cast_nonneg _)

/-- **The `3-4-1` logarithmic-derivative inequality.** For every Dirichlet character `χ` of
positive level, real `σ > 1` and real `t`,
`3 Re (ζ′/ζ(σ)) + 4 Re (L′/L(σ + i t, χ)) + Re (L′/L(σ + 2 i t, χ²)) ≤ 0`. -/
theorem three_mul_re_logDeriv_riemannZeta_add_four_add_nonpos [NeZero N] {σ : ℝ}
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
  have hn0 : (n : ℂ) ≠ 0 := mod_cast hn
  set z : ℂ := χ n * (n : ℂ) ^ (-(t * Complex.I))
  have hz : ‖z‖ ≤ 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (mod_cast Nat.pos_of_ne_zero hn)]
    simpa using χ.norm_le_one n
  have hterm {ψ : DirichletCharacter ℂ N} {u : ℂ} :
      term (↗ψ * ↗Λ) (σ + u) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (ψ n * (n : ℂ) ^ (-u)) := by
    rw [term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
      Complex.cpow_add _ _ hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow n.cast_nonneg, Real.rpow_neg n.cast_nonneg, Complex.ofReal_div,
      Complex.ofReal_inv, div_eq_mul_inv]
    ring
  have ht₀ : term (↗χ₀ * ↗Λ) σ n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    simp [term_of_ne_zero hn, χ₀, MulChar.one_apply (isUnit_of_subsingleton _),
      Complex.ofReal_cpow n.cast_nonneg]
  have ht₂ : (χ ^ 2) n * (n : ℂ) ^ (-(2 * (t : ℂ) * Complex.I)) = z ^ 2 := by
    rw [sq χ, MulChar.mul_apply, show -(2 * (t : ℂ) * Complex.I) = (2 : ℕ) * -(t * Complex.I) by
      push_cast; ring, Complex.cpow_nat_mul]
    simp only [z]; ring
  rw [ht₀, hterm, show ((σ : ℂ) + 2 * t * Complex.I) = σ + (2 * (t : ℂ) * Complex.I) by rfl,
    hterm, ht₂, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hzeq : χ n * (n : ℂ) ^ (-(t * Complex.I)) = z := rfl
  rw [hzeq]
  nlinarith [div_nonneg (vonMangoldt_nonneg (n := n)) (Real.rpow_nonneg n.cast_nonneg σ),
    three_add_four_re_add_re_sq_nonneg hz]

omit χ in
private theorem not_differentiableAt_LFunctionTrivChar_one [NeZero N] :
    ¬ DifferentiableAt ℂ (LFunction (1 : DirichletCharacter ℂ N)) 1 := by
  intro hd
  have h0 : Tendsto (fun z ↦ (z - 1) * LFunctionTrivChar N z) (𝓝[≠] 1) (𝓝 0) := by
    have h := (((continuous_id.sub (continuous_const (y := (1 : ℂ)))).tendsto (1 : ℂ)).mul
      hd.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa [LFunctionTrivChar] using h
  exact LFunctionTrivChar₁_apply_one_ne_zero N
    (by simpa using (tendsto_nhds_unique h0 (LFunctionTrivChar_residue_one (N := N))).symm)

omit χ in
private theorem norm_logDeriv_one_sub_prime_cpow_le {p : ℕ} (hp : p.Prime) (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 ∧
      ‖logDeriv (fun z : ℂ ↦ 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp_pos : 0 < (p : ℝ) := mod_cast hp.pos
  have hp_gt1 : (1 : ℝ) < p := mod_cast hp.one_lt
  have hp_ge2 : (2 : ℝ) ≤ p := mod_cast hp.two_le
  have hp0 : (p : ℂ) ≠ 0 := mod_cast hp.ne_zero
  have hd : HasDerivAt (fun z : ℂ ↦ 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Real.log p) s := by
    convert ((hasDerivAt_neg s).const_cpow (.inl hp0)).const_sub 1 using 2
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log p.cast_nonneg]
    ring
  have hw : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re,
      ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp_gt1.le (by linarith)
  have hlo : 1 - (p : ℝ)⁻¹ ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    simp only [norm_one] at this
    linarith
  have hden_pos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_gt1)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp_gt1.le
  refine ⟨norm_pos_iff.mp (hden_pos.trans_le hlo), ?_⟩
  rw [logDeriv_apply, hd.deriv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
  calc
    ‖(p : ℂ) ^ (-s)‖ * Real.log p / ‖1 - (p : ℂ) ^ (-s)‖
      ≤ (p : ℝ)⁻¹ * Real.log p / (1 - (p : ℝ)⁻¹) := by gcongr
    _ = Real.log p / ((p : ℝ) - 1) := by field_simp [hp_pos.ne']
    _ ≤ Real.log p / 1 := by gcongr; linarith
    _ = Real.log p := div_one _

omit χ in
/-- **Deleted Euler factors in the logarithmic derivative.** On the closed half-plane `1 ≤ re s`,
the logarithmic derivative of the principal character modulo `N` differs from `ζ′/ζ(s)` by at most
`log N` in norm. At `s = 1` both functions fail to be differentiable, so both logarithmic
derivatives vanish and the bound holds trivially. -/
theorem norm_logDeriv_trivChar_sub_logDeriv_riemannZeta_le [NeZero N] (hs : 1 ≤ s.re) :
    ‖logDeriv (LFunction (1 : DirichletCharacter ℂ N)) s - logDeriv riemannZeta s‖ ≤
      Real.log N := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have hζ : ¬ DifferentiableAt ℂ riemannZeta 1 := by
      simpa [LFunction_modOne_eq] using not_differentiableAt_LFunctionTrivChar_one (N := 1)
    rw [logDeriv_eq_zero_of_not_differentiableAt _ _ not_differentiableAt_LFunctionTrivChar_one,
      logDeriv_eq_zero_of_not_differentiableAt _ _ hζ, sub_self, norm_zero]
    exact Real.log_nonneg (Nat.one_le_cast.mpr NeZero.one_le)
  set f : ℕ → ℂ → ℂ := fun p z ↦ 1 - (p : ℂ) ^ (-z)
  have hdf (p : ℕ) (hp : p ∈ N.primeFactors) : Differentiable ℂ (f p) := by
    have hp0 : (p : ℂ) ≠ 0 := mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiable_const 1).sub (differentiable_id.neg.const_cpow (.inl hp0))
  have hnef (p : ℕ) (hp : p ∈ N.primeFactors) : f p s ≠ 0 :=
    (norm_logDeriv_one_sub_prime_cpow_le (Nat.prime_of_mem_primeFactors hp) hs).1
  have hPdiff : Differentiable ℂ (∏ p ∈ N.primeFactors, f p) :=
    prod_induction _ (Differentiable ℂ) (fun _ _ hg hh ↦ hg.mul hh) (differentiable_const 1) hdf
  have hPs : (∏ p ∈ N.primeFactors, f p) s ≠ 0 := by
    rw [Finset.prod_apply]
    exact prod_ne_zero_iff.mpr hnef
  have heq : LFunction (1 : DirichletCharacter ℂ N) =ᶠ[𝓝 s]
      (∏ p ∈ N.primeFactors, f p) * riemannZeta := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    simpa [f, LFunctionTrivChar, Finset.prod_apply] using LFunctionTrivChar_eq_mul_riemannZeta hz
  have hlog : logDeriv (LFunction (1 : DirichletCharacter ℂ N)) s - logDeriv riemannZeta s =
      ∑ p ∈ N.primeFactors, logDeriv (f p) s := by
    rw [(logDeriv_congr_nhds heq).eq_of_nhds,
      logDeriv_mul s hPs (riemannZeta_ne_zero_of_one_le_re hs) (hPdiff s)
        (differentiableAt_riemannZeta hs1),
      add_sub_cancel_right]
    exact logDeriv_prod hnef fun p hp ↦ hdf p hp s
  have hprod_pos : 0 < ∏ p ∈ N.primeFactors, (p : ℝ) :=
    prod_pos fun p hp ↦ mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hprod_le : ∏ p ∈ N.primeFactors, (p : ℝ) ≤ N := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)
  rw [hlog]
  calc
    ‖∑ p ∈ N.primeFactors, logDeriv (f p) s‖
      ≤ ∑ p ∈ N.primeFactors, ‖logDeriv (f p) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p :=
        sum_le_sum fun p hp ↦
          (norm_logDeriv_one_sub_prime_cpow_le (Nat.prime_of_mem_primeFactors hp) hs).2
    _ = Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) :=
        (Real.log_prod fun p hp ↦ mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero).symm
    _ ≤ Real.log N := Real.log_le_log hprod_pos hprod_le

end DirichletCharacter
