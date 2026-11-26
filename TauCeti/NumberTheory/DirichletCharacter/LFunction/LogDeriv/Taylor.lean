/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.Landau

/-!
# Taylor coefficients of Dirichlet logarithmic derivatives

We expand the negative logarithmic derivative of a Dirichlet `L`-function at `s` in the variable
`t`, using `-L′/L(s - t)`. Right of the line `Re s = 1` its Taylor coefficients are twisted von
Mangoldt series with the weight `(log n)^k / k!`.

For a real character `ψ` and a real centre `σ > 1`, the real part of the sum of the coefficients
for the principal character and `ψ` bounds the norm of the sum for `χ` and `χψ` at `σ + it`.
This supplies
the four-term positivity inequality used in the Deuring–Heilbronn argument. The inequality is
the one used by Levent Alpöge in his [formalization of the Riemann hypothesis for Dirichlet
`L`-functions][alpoege]; the proof here uses a norm comparison of the two sums.

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open ArithmeticFunction Filter LSeries
open scoped ComplexOrder LSeries.notation Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The coefficient of `t^k` in the Taylor expansion of `-L′/L(s - t, χ)` at `t = 0`
when the logarithmic derivative is analytic at `s`. -/
noncomputable def negLogDerivTaylorCoeff (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * iteratedDeriv k (-logDeriv (LFunction χ)) s / (k.factorial : ℂ)

/-- The signed, factorial-normalized derivative defining the Taylor coefficient. -/
theorem negLogDerivTaylorCoeff_def (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) :
    χ.negLogDerivTaylorCoeff k s =
      (-1 : ℂ) ^ k * iteratedDeriv k (-logDeriv (LFunction χ)) s / (k.factorial : ℂ) := (rfl)

/-- The constant Taylor coefficient is the negative logarithmic derivative. -/
@[simp] theorem negLogDerivTaylorCoeff_zero (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.negLogDerivTaylorCoeff 0 s = -logDeriv (LFunction χ) s := by
  simp [negLogDerivTaylorCoeff_def]

/-- Right of the line `Re s = 1`, the Taylor coefficient is the twisted von Mangoldt
Dirichlet series weighted by `(log n)^k / k!`. -/
theorem negLogDerivTaylorCoeff_eq_LSeries (χ : DirichletCharacter ℂ N) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    χ.negLogDerivTaylorCoeff k s = LSeries (logMul^[k] (↗χ * ↗Λ)) s / (k.factorial : ℂ) := by
  have heq : -logDeriv (LFunction χ) =ᶠ[𝓝 s] LSeries (↗χ * ↗Λ) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    simpa only [Pi.neg_apply, neg_neg] using
      congrArg Neg.neg (χ.logDeriv_LFunction_eq_neg_LSeries hz)
  have habs : abscissaOfAbsConv (↗χ * ↗Λ) < s.re :=
    χ.abscissaOfAbsConv_twist_vonMangoldt_le_one.trans_lt (by exact_mod_cast hs)
  rw [negLogDerivTaylorCoeff_def, heq.iteratedDeriv_eq k, LSeries_iteratedDeriv k habs,
    ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-- The Taylor coefficient is the sum of the twisted von Mangoldt terms with the
nonnegative weight `(log n)^k / k!`. -/
theorem hasSum_negLogDerivTaylorCoeff (χ : DirichletCharacter ℂ N) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ ((Real.log n ^ k / k.factorial : ℝ) : ℂ) * term (↗χ * ↗Λ) s n)
      (χ.negLogDerivTaylorCoeff k s) := by
  rw [χ.negLogDerivTaylorCoeff_eq_LSeries k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗χ * ↗Λ)) < s.re := by
    rw [abscissaOfAbsConv_logPowMul]
    exact (χ.abscissaOfAbsConv_twist_vonMangoldt_le_one).trans_lt (by exact_mod_cast hs)
  refine ((LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).hasSum.div_const _).congr_fun
    (fun n ↦ ?_)
  simp only [TauCeti.LSeries.term_logPowMul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow]
  rw [div_mul_eq_mul_div]

/-- **Four-character Taylor coefficient bound.** For a real-valued character `ψ`, the
principal and `ψ` coefficients at real `σ > 1` dominate the norm of the sum for `χ` and
`χψ` at any `s` with `σ ≤ Re s`. In particular the sum of the real parts of all four
coefficients is nonnegative. -/
theorem norm_add_negLogDerivTaylorCoeff_le (χ ψ : DirichletCharacter ℂ N)
    (hψ : ∀ a, (ψ a).im = 0) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) (k : ℕ) :
    ‖χ.negLogDerivTaylorCoeff k s + (χ * ψ).negLogDerivTaylorCoeff k s‖ ≤
      ((1 : DirichletCharacter ℂ N).negLogDerivTaylorCoeff k σ +
        ψ.negLogDerivTaylorCoeff k σ).re := by
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hs' := hσ.trans_le hs
  have hU := (χ.hasSum_negLogDerivTaylorCoeff k hs').add
    ((χ * ψ).hasSum_negLogDerivTaylorCoeff k hs')
  have h₁ := (1 : DirichletCharacter ℂ N).hasSum_negLogDerivTaylorCoeff k hσ'
  have hV := Complex.hasSum_re (h₁.add (ψ.hasSum_negLogDerivTaylorCoeff k hσ'))
  rw [← hU.tsum_eq]
  refine tsum_of_norm_bounded hV fun n ↦ ?_
  have hw : 0 ≤ Real.log n ^ k / (k.factorial : ℝ) :=
    div_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) (Nat.cast_nonneg _)
  simp only [← mul_add, norm_mul, Complex.norm_of_nonneg hw, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (χ.norm_add_term_twist_vonMangoldt_le ψ hs n (hψ n)) hw

/-- The four Taylor coefficients in the Deuring–Heilbronn argument have nonnegative sum
of real parts. This holds for every `σ > 1`, and hence at the usual centres `2` and `2 + it`. -/
theorem re_add_negLogDerivTaylorCoeff_nonneg (χ ψ : DirichletCharacter ℂ N)
    (hψ : ∀ a, (ψ a).im = 0) {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    0 ≤ ((1 : DirichletCharacter ℂ N).negLogDerivTaylorCoeff k s.re +
      ψ.negLogDerivTaylorCoeff k s.re + χ.negLogDerivTaylorCoeff k s +
      (χ * ψ).negLogDerivTaylorCoeff k s).re := by
  have h := χ.norm_add_negLogDerivTaylorCoeff_le ψ hψ hs le_rfl k
  have hneg := Complex.re_le_norm (-(χ.negLogDerivTaylorCoeff k s +
    (χ * ψ).negLogDerivTaylorCoeff k s))
  simp only [Complex.add_re, Complex.neg_re, norm_neg] at h hneg ⊢
  linarith

end DirichletCharacter
