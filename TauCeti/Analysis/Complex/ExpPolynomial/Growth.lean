/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Growth bounds for multivariate complex exponential polynomials

On `ι → ℂ` equipped with the supremum norm, an exponential monomial
`z ↦ (∏ v, z v ^ τ v) * exp (∑ v, w v * z v)` satisfies
`‖(∏ v, z v ^ τ v) * exp (w · z)‖ ≤ (1 + ‖z‖) ^ (∑ v, τ v) * exp ((∑ v, ‖w v‖) * ‖z‖)`.
Using `1 + ‖z‖` rather than `‖z‖` for the polynomial factor makes `(1 + ‖z‖) ^ d` monotone in the
total degree `d = ∑ v, τ v` even inside the unit polydisc `‖z‖ < 1`, so a single upper bound
`(1 + R) ^ D * exp (B * R)` controls every monomial of total degree at most `D` and frequency
`ℓ¹`-norm at most `B` on the closed polydisc of radius `R`. In transcendence proofs by auxiliary
functions (such as the Schneider–Lang criterion and Baker's theorem), these bounds supply the
polydisc growth estimates fed into Cauchy coefficient bounds and Schwarz-type extrapolation
inequalities.

## Main results

* `TauCeti.norm_cexp_sum_mul_le`: `‖exp (∑ v, w v * z v)‖ ≤ exp ((∑ v, ‖w v‖) * ‖z‖)`.
* `TauCeti.norm_prod_pow_mul_cexp_le`: growth bound for a single exponential monomial.
* `TauCeti.norm_prod_pow_mul_cexp_le_of_le`: uniform growth bound for an exponential monomial of
  total degree at most `D` and frequency `ℓ¹`-norm at most `B` on `‖z‖ ≤ R`.
* `TauCeti.norm_sum_mul_prod_pow_mul_cexp_le_of_le` and
  `TauCeti.norm_sum_mul_prod_pow_mul_cexp_le`: uniform growth bounds for finite linear
  combinations of exponential monomials.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer (2000), Chapter 4, §4.6.
* M. Karatarakis, formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/ExpPoly.lean`, Apache 2.0).
-/

public section

open Finset

namespace TauCeti

/-- On `ι → ℂ` with the supremum norm, `‖exp (∑ v, w v * z v)‖ ≤ exp ((∑ v, ‖w v‖) * ‖z‖)`. -/
theorem norm_cexp_sum_mul_le {ι : Type*} [Fintype ι] (w z : ι → ℂ) :
    ‖Complex.exp (∑ v, w v * z v)‖ ≤ Real.exp ((∑ v, ‖w v‖) * ‖z‖) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun v _ ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z v) (norm_nonneg _)

/-- **Growth bound for a multivariate exponential monomial.** On `ι → ℂ` with the supremum norm,
`‖(∏ v, z v ^ τ v) * exp (∑ v, w v * z v)‖ ≤ (1 + ‖z‖) ^ (∑ v, τ v) * exp ((∑ v, ‖w v‖) * ‖z‖)`.
The base `1 + ‖z‖` keeps the polynomial factor monotone in the total degree `∑ v, τ v` even inside
the unit polydisc `‖z‖ < 1`. -/
theorem norm_prod_pow_mul_cexp_le {ι : Type*} [Fintype ι] (τ : ι → ℕ) (w z : ι → ℂ) :
    ‖(∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)‖ ≤
      (1 + ‖z‖) ^ (∑ v, τ v) * Real.exp ((∑ v, ‖w v‖) * ‖z‖) := by
  rw [norm_mul, norm_prod, ← prod_pow_eq_pow_sum]
  refine mul_le_mul ?_ (norm_cexp_sum_mul_le w z) (by positivity) (by positivity)
  gcongr with v
  rw [norm_pow]
  gcongr
  exact (norm_le_pi_norm z v).trans (le_add_of_nonneg_left zero_le_one)

/-- Uniform growth bound for an exponential monomial of total degree at most `D` and frequency
`ℓ¹`-norm at most `B` on `‖z‖ ≤ R`. Nonnegativity of `B` and `R` follows from the norm hypotheses
and is not assumed separately. -/
theorem norm_prod_pow_mul_cexp_le_of_le {ι : Type*} [Fintype ι] {τ : ι → ℕ} {D : ℕ}
    (hτ : ∑ v, τ v ≤ D) {w : ι → ℂ} {B : ℝ} (hw : ∑ v, ‖w v‖ ≤ B) {z : ι → ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) :
    ‖(∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)‖ ≤
      (1 + R) ^ D * Real.exp (B * R) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hB : 0 ≤ B := (sum_nonneg fun _ _ ↦ norm_nonneg _).trans hw
  refine (norm_prod_pow_mul_cexp_le τ w z).trans ?_
  refine mul_le_mul ?_ (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _) (by positivity)
  · exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hτ)
  · exact mul_le_mul hw hz (norm_nonneg z) hB

/-- Uniform growth bound for a finite linear combination of exponential monomials on `‖z‖ ≤ R`.
None of `C`, `B`, or `R` is assumed nonnegative: when `s` is empty both sides are `0`, and when
`s` is nonempty their nonnegativity follows from the norm hypotheses. -/
theorem norm_sum_mul_prod_pow_mul_cexp_le_of_le {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {c : κ → ℂ} {C : ℝ} (hc : ∀ k ∈ s, ‖c k‖ ≤ C)
    {τ : κ → ι → ℕ} {D : ℕ} (hτ : ∀ k ∈ s, ∑ v, τ k v ≤ D)
    {w : κ → ι → ℂ} {B : ℝ} (hw : ∀ k ∈ s, ∑ v, ‖w k v‖ ≤ B)
    {z : ι → ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))‖ ≤
      #s * C * (1 + R) ^ D * Real.exp (B * R) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp
  have hC : 0 ≤ C := (norm_nonneg (c k₀)).trans (hc k₀ hk₀)
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_card_nsmul s _ (C * ((1 + R) ^ D * Real.exp (B * R))) fun k hk ↦ ?_).trans_eq ?_
  · rw [norm_mul]
    exact mul_le_mul (hc k hk)
      (norm_prod_pow_mul_cexp_le_of_le (hτ k hk) (hw k hk) hz) (norm_nonneg _) hC
  · simp only [nsmul_eq_mul]
    ring

/-- Pointwise growth bound for a finite linear combination of exponential monomials of total degree
at most `D`, coefficient norm at most `C`, and frequency `ℓ¹`-norm at most `B`. -/
theorem norm_sum_mul_prod_pow_mul_cexp_le {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {c : κ → ℂ} {C : ℝ} (hc : ∀ k ∈ s, ‖c k‖ ≤ C)
    {τ : κ → ι → ℕ} {D : ℕ} (hτ : ∀ k ∈ s, ∑ v, τ k v ≤ D)
    {w : κ → ι → ℂ} {B : ℝ} (hw : ∀ k ∈ s, ∑ v, ‖w k v‖ ≤ B) (z : ι → ℂ) :
    ‖∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))‖ ≤
      #s * C * (1 + ‖z‖) ^ D * Real.exp (B * ‖z‖) :=
  norm_sum_mul_prod_pow_mul_cexp_le_of_le hc hτ hw le_rfl

end TauCeti
