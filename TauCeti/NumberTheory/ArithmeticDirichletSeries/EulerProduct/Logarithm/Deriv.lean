/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic

import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The derivative of the prime-power logarithmic expansion

`TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub` expands the sum of local
logarithms over the prime powers `(P, e)`.  This file differentiates that expansion in `s`, term by
term, on the open half-plane where the ideal-indexed series converges absolutely.

Each term `(χ(P) N(P)⁻ˢ) ^ (e+1) / (e+1)` differentiates to `-log N(P) * (χ(P) N(P)⁻ˢ) ^ (e+1)`, so
the differentiated family is the undivided one weighted by `-log N(P)`.  Termwise differentiation of
a sum needs a summable majorant valid across a neighbourhood rather than at the single point, and
the half-plane supplies it: strictly to the right of a point of absolute convergence the weight
`log N(P)` is absorbed, which is `summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and the
exponent direction is geometric, which is `TauCeti.summable_mul_norm_pow_succ`.

`EulerProduct/Branch.lean` identifies the derivative of a *branch* of the logarithm with the
logarithmic derivative of the `L`-series.  That is an abstract identification; this file gives the
prime-power series the derivative is equal to.

## Main results

* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow`: the prime-power expansion
  differentiates termwise, strictly right of the abscissa of absolute convergence.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_prime_pow`: that derivative **is**
  the logarithmic derivative of the `L`-series.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- **The Taylor term at `(P, e)` differentiates to `-log N(P)` times the undivided power.**  The
division by `e + 1` is what makes the derivative the plain power rather than a multiple of it. -/
theorem hasDerivAt_prime_pow_taylor_term (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
        / ((e : ℂ) + 1))
      (-(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (e + 1))) s := by
  have hne : ((e : ℂ) + 1) ≠ 0 := by
    have : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero e
  have hterm : ∀ z : ℂ, (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
      = idealTerm K χ.toIdealArithmeticFunction z (P.primeIdealPow (e + 1)) := fun z ↦
    (idealTerm_toIdealArithmeticFunction_primeIdealPow χ P (e + 1) z).symm
  have hlog : Complex.log ((Ideal.absNorm ((P.primeIdealPow (e + 1) : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K))) : ℂ)
      = ((e : ℂ) + 1) * Complex.log (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [P.absNorm_primeIdealPow, ← Complex.natCast_log, ← Complex.natCast_log]
    push_cast [Real.log_pow]
    ring
  have hval : -(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
      = -(Complex.log ((Ideal.absNorm ((P.primeIdealPow (e + 1) : (Ideal (𝓞 K))⁰) :
            Ideal (𝓞 K))) : ℂ)
          * idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
        / ((e : ℂ) + 1) := by
    rw [hlog]
    field_simp
  simp_rw [hterm]
  rw [hval]
  exact (hasDerivAt_idealTerm K χ.toIdealArithmeticFunction
    (P.primeIdealPow (e + 1)) s).div_const ((e : ℂ) + 1)

/-- **The differentiated term is dominated by its value at the edge of the half-plane.**  The bound
is uniform in `z` across `σ₀ ≤ z.re`, which is what termwise differentiation of a sum requires. -/
theorem norm_log_mul_prime_pow_le (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) {σ₀ : ℝ} {z : ℂ}
    (hz : σ₀ ≤ z.re) :
    ‖-(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1))‖
      ≤ Real.log (Ideal.absNorm P.asIdeal)
          * ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (e + 1) := by
  have hlogpos : 0 ≤ Real.log (Ideal.absNorm P.asIdeal : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P).le)
  have hlog : ‖Complex.log (Ideal.absNorm P.asIdeal : ℂ)‖
      = Real.log (Ideal.absNorm P.asIdeal) := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_of_nonneg hlogpos]
  have hmono : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z‖
      ≤ ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ := by
    have := norm_idealTerm_le_of_re_le_re K χ.toIdealArithmeticFunction
      (s := (σ₀ : ℂ)) (s' := z) (by simpa using hz) (P.primeIdealPow 1)
    simpa [idealTerm_toIdealArithmeticFunction_primeIdealPow] using this
  rw [norm_neg, norm_mul, norm_pow, hlog]
  gcongr

/-- **The log-weighted majorant is summable over primes and exponents together.**  Strictly to the
right of a point of absolute convergence the weight `log N(P)` is absorbed, and the exponent
direction is geometric. -/
theorem summable_log_absNorm_mul_norm_prime_pow {s s' : ℂ} (h : s.re < s'.re)
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s'‖ ^ (pe.2 + 1) := by
  have hs' : Summable (idealTerm K χ.toIdealArithmeticFunction s') :=
    summable_idealTerm_of_re_le_re K h.le hs
  have hwr : Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      Real.log (Ideal.absNorm P.asIdeal)
        * ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s'‖ := by
    refine ((summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re K h hs).comp_injective
      HeightOneSpectrum.primeIdealPow_one_injective).congr fun P ↦ ?_
    have hP : 0 < Ideal.absNorm P.asIdeal := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm P
      omega
    simp only [Function.comp_apply, norm_idealTerm, HeightOneSpectrum.coe_primeIdealPow, pow_one,
      toIdealArithmeticFunction_apply, norm_div, Complex.norm_natCast_cpow_of_pos hP]
  have hhalf : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s'‖ ≤ 1 / 2 :=
    (χ.summable_div_of_summable_idealTerm hs').tendsto_cofinite_zero.norm.eventually_le_const
      (by norm_num)
  refine summable_mul_norm_pow_succ ?_ hwr ?_
  · exact ⟨1 / 2, by norm_num, by filter_upwards [hhalf] with P hP _; linarith⟩
  · exact fun P _ ↦ χ.norm_div_lt_one_of_summable_idealTerm hs' P

/-- **The prime-power expansion differentiates termwise.**  Strictly to the right of the abscissa
of absolute convergence, the sum over prime powers is differentiable and its derivative is the
termwise one: the same family weighted by `-log N(P)`, with the division by `e + 1` gone.

The abscissa is all that is needed: convergence propagates rightward from any point to its left,
which is what supplies the majorant on a neighbourhood of `s`. -/
theorem hasDerivAt_tsum_prime_pow {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    HasDerivAt (fun z : ℂ ↦ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
      (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1))) s := by
  obtain ⟨s₀, hs₀, hs₀s⟩ : ∃ y : ℝ, Summable (idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [idealAbscissaOfAbsConv_def, sInf_lt_iff] using hs
  obtain ⟨σ₀, hσ₁₀, hσ₀s⟩ := exists_between hs₀s
  have hu : Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (pe.2 + 1) :=
    χ.summable_log_absNorm_mul_norm_prime_pow (s := (s₀ : ℂ)) (s' := (σ₀ : ℂ))
      (by simpa using hσ₁₀) hs₀
  have hsum : Summable (idealTerm K χ.toIdealArithmeticFunction s) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  have hy₀ := Complex.summable_taylorSeries_neg_log
    (r := fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
    (χ.summable_div_of_summable_idealTerm hsum)
    (χ.norm_div_lt_one_of_summable_idealTerm hsum)
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (pe : HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
    (g' := fun (pe : HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
        * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1)))
    (t := {z : ℂ | σ₀ < z.re}) (y₀ := s)
    hu (isOpen_lt continuous_const continuous_re)
    (convex_halfSpace_re_gt σ₀).isPreconnected
    (fun pe z _ ↦ χ.hasDerivAt_prime_pow_taylor_term pe.1 pe.2 z)
    (fun pe z hz ↦ χ.norm_log_mul_prime_pow_le pe.1 pe.2 (le_of_lt hz))
    hσ₀s hy₀ hσ₀s

/-- **The logarithmic derivative of the `L`-series, as a prime-power series.**  Strictly to the
right of a point of absolute convergence,

`logDeriv L(s) = ∑' (P, e), -log N(P) · (χ(P) N(P)⁻ˢ) ^ (e+1)`

strictly to the right of the abscissa of absolute convergence.

The prime-power expansion is a branch of the logarithm of the `L`-series there — its exponential
is the `L`-series, by `exp_tsum_prime_pow_eq_LSeries` — and the derivative of any such branch is
the logarithmic derivative, the branch ambiguity being locally constant.

This is what lets a density argument work with the logarithmic derivative termwise over prime
powers, rather than with the `L`-series itself. -/
theorem logDeriv_LSeries_eq_tsum_prime_pow {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s
      = ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1)) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, Summable (idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [idealAbscissaOfAbsConv_def, sInf_lt_iff] using hs
  set U : Set ℂ := {z : ℂ | y < z.re} with hU
  set f : ℂ → ℂ := fun z ↦ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
    (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) with hf
  have hmem : ∀ z ∈ U, idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < z.re := by
    intro z hz
    rw [hU, Set.mem_ofPred_eq] at hz
    exact lt_of_le_of_lt (by simpa using idealAbscissaOfAbsConv_le K hy) (by exact_mod_cast hz)
  have hsU : s ∈ U := by rw [hU, Set.mem_ofPred_eq]; exact hys
  have hUo : IsOpen U := by rw [hU]; exact isOpen_lt continuous_const continuous_re
  have hderiv : ∀ z ∈ U, HasDerivAt f
      (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1))) z := by
    intro z hz
    rw [hf]
    exact χ.hasDerivAt_tsum_prime_pow (hmem z hz)
  have hdiff : DifferentiableOn ℂ f U := fun z hz ↦
    (hderiv z hz).differentiableAt.differentiableWithinAt
  have heq : Set.EqOn (Complex.exp ∘ f) (LSeries (normCoeff K χ.toIdealArithmeticFunction)) U := by
    intro z hz
    rw [Function.comp_apply, hf]
    exact χ.exp_tsum_prime_pow_eq_LSeries
      (summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (hmem z hz))
  rw [← deriv_eq_logDeriv_of_eqOn_exp_comp hUo hdiff heq hsU, (hderiv s hsU).deriv]

end MultiplicativeIdealWeight

end TauCeti
