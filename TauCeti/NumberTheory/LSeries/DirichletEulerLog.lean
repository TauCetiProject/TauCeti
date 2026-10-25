/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The logarithm of a Dirichlet `L`-function near the line `re s = 1`

For a Dirichlet character `χ`, the coefficients
`DirichletCharacter.eulerLogCoeff χ n = χ n * Λ n / log n`
are those of the logarithm of the Euler product of `L(χ, s)`: they vanish off prime powers, equal
`χ p ^ k / k` at `p ^ k`, and are bounded by `1`. For `1 < re s` their `L`-series converges
absolutely and its exponential is `L(χ, s)` (Mathlib's `DirichletCharacter.LSeries_eq_exp_LSeries`).

When `χ` is nontrivial, `L(χ, s)` is entire and has no zero on the closed half-plane `1 ≤ re s`.
The main result, `DirichletCharacter.exists_differentiableOn_exp_eq_LFunction`, uses this to
continue the logarithm holomorphically to an open neighbourhood of that closed half-plane, keeping
its exponential equal to `L(χ, s)`. The continuation is
`TauCeti.exists_differentiableOn_eqOn_exp_comp_le_re`, which patches local branches of the
logarithm on discs centred on the line `re s = 1`; it asserts nothing about a strip of uniform
width, and it is not the principal logarithm of `L(χ, s)`.

The continued logarithm has the shape of the hypotheses of a bounded Tauberian theorem for
Dirichlet series at `s = 1`: coefficients bounded by `1`, an absolutely convergent `L`-series for
`1 < re s`, and a holomorphic extension to an open neighbourhood of `1 ≤ re s`.

The nonvanishing input is Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, and the
Euler-product logarithm for `1 < re s` is Mathlib's
`DirichletCharacter.eulerProduct_log_eq_LSeries`.

## Main results

* `DirichletCharacter.eulerLogCoeff_prime_pow`,
  `DirichletCharacter.eulerLogCoeff_eq_zero_of_not_isPrimePow`,
  `DirichletCharacter.norm_eulerLogCoeff_le_one`: the values and bound of the coefficients.
* `DirichletCharacter.exp_LSeries_eulerLogCoeff`: `exp` of their `L`-series is `L(χ, s)` for
  `1 < re s`.
* `DirichletCharacter.exists_differentiableOn_exp_eq_LFunction`: the holomorphic continuation of
  that logarithm to a neighbourhood of `1 ≤ re s`, for nontrivial `χ`.
-/

public section

open ArithmeticFunction Complex LSeries Set

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The coefficients `χ n * Λ n / log n` of the logarithm of the Euler product of the Dirichlet
`L`-function `L(χ, s)`: by `DirichletCharacter.eulerLogCoeff_prime_pow` they are `χ p ^ k / k` at a
prime power `p ^ k`, and they vanish elsewhere. -/
noncomputable def eulerLogCoeff (n : ℕ) : ℂ :=
  χ n * Λ n / Real.log n

/-- The defining formula of `DirichletCharacter.eulerLogCoeff`. -/
theorem eulerLogCoeff_apply (n : ℕ) : χ.eulerLogCoeff n = χ n * Λ n / Real.log n := by
  rw [eulerLogCoeff]

/-- The coefficient at `0` is `0`, as `Λ 0 = 0`. -/
@[simp]
theorem eulerLogCoeff_zero : χ.eulerLogCoeff 0 = 0 := by
  simp [eulerLogCoeff]

/-- The coefficient at `1` is `0`, as `Λ 1 = 0`. -/
@[simp]
theorem eulerLogCoeff_one : χ.eulerLogCoeff 1 = 0 := by
  simp [eulerLogCoeff]

/-- The coefficients vanish off prime powers. -/
theorem eulerLogCoeff_eq_zero_of_not_isPrimePow {n : ℕ} (hn : ¬IsPrimePow n) :
    χ.eulerLogCoeff n = 0 := by
  simp [eulerLogCoeff, vonMangoldt_eq_zero_iff.mpr hn]

/-- At a prime power `p ^ k` with `k ≠ 0`, the coefficient is `χ p ^ k / k`, the `k`-th term of
the Taylor series of `-log (1 - χ p * p ^ (-s))` at `s = 0`. -/
theorem eulerLogCoeff_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    χ.eulerLogCoeff (p ^ k) = χ p ^ k / k := by
  have hlog : (Real.log p : ℂ) ≠ 0 := mod_cast hp.log_ne_zero
  rw [eulerLogCoeff, vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  simp only [Nat.cast_pow, Real.log_pow, map_pow]
  rw [ofReal_mul, ofReal_natCast, mul_div_mul_right _ _ hlog]

/-- At a prime `p`, the coefficient is `χ p`. -/
@[simp]
theorem eulerLogCoeff_prime {p : ℕ} (hp : p.Prime) : χ.eulerLogCoeff p = χ p := by
  simpa using χ.eulerLogCoeff_prime_pow hp one_ne_zero

/-- The coefficients are bounded by `1`, because `‖χ n‖ ≤ 1` and `Λ n ≤ log n`. -/
theorem norm_eulerLogCoeff_le_one (n : ℕ) : ‖χ.eulerLogCoeff n‖ ≤ 1 := by
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n <;> simp
  have hlog : 0 < Real.log n := Real.log_pos (mod_cast hn)
  rw [eulerLogCoeff, norm_div, norm_mul, norm_real, norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_of_nonneg hlog.le, div_le_one hlog]
  calc ‖χ n‖ * Λ n ≤ 1 * Real.log n :=
        mul_le_mul (χ.norm_le_one _) vonMangoldt_le_log vonMangoldt_nonneg zero_le_one
    _ = Real.log n := one_mul _

/-- The `L`-series of the coefficients converges absolutely for `1 < re s`. -/
theorem LSeriesSummable_eulerLogCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable χ.eulerLogCoeff s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ χ.norm_eulerLogCoeff_le_one n) hs

/-- The `L`-series of the coefficients is holomorphic on `1 < re s`. -/
theorem differentiableOn_LSeries_eulerLogCoeff :
    DifferentiableOn ℂ (LSeries χ.eulerLogCoeff) {s : ℂ | 1 < s.re} :=
  (LSeries_differentiableOn _).mono fun s (hs : 1 < s.re) ↦
    (abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ ↦ χ.norm_eulerLogCoeff_le_one n⟩).trans_lt
      (mod_cast hs)

/-- For `1 < re s`, the `L`-series of the coefficients is a logarithm of `L(χ, s)`. -/
theorem exp_LSeries_eulerLogCoeff [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries χ.eulerLogCoeff s) = LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs, ← LSeries_eq_exp_LSeries χ hs, funext χ.eulerLogCoeff_apply]

/-- **The logarithm of a Dirichlet `L`-function continues across `re s = 1`.** For a nontrivial
Dirichlet character `χ`, some open neighbourhood `Ω` of the closed half-plane `1 ≤ re s` carries a
holomorphic `F` with `exp (F s) = L(χ, s)` on `Ω` and with `F s` the sum of the absolutely
convergent `L`-series of `DirichletCharacter.eulerLogCoeff χ` for `1 < re s`.

`Ω` need not contain a strip `1 - δ < re s` of uniform width. -/
theorem exists_differentiableOn_exp_eq_LFunction [NeZero N] (hχ : χ ≠ 1) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ {s : ℂ | 1 ≤ s.re} ⊆ Ω ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      (∀ s ∈ Ω, exp (F s) = LFunction χ s) ∧
      ∀ s : ℂ, 1 < s.re → LSeriesHasSum χ.eulerLogCoeff s (F s) := by
  obtain ⟨Ω, hΩ, hcover, F, hFd, hFexp, hFf⟩ :=
    TauCeti.exists_differentiableOn_eqOn_exp_comp_le_re isOpen_univ (subset_univ _)
      (differentiable_LFunction hχ).differentiableOn
      (fun s hs ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs)
      χ.differentiableOn_LSeries_eulerLogCoeff fun s hs ↦ χ.exp_LSeries_eulerLogCoeff hs
  refine ⟨Ω, hΩ, hcover, F, hFd, fun s hs ↦ hFexp hs, fun s hs ↦ ?_⟩
  rw [hFf hs]
  exact (χ.LSeriesSummable_eulerLogCoeff hs).LSeriesHasSum

end DirichletCharacter
