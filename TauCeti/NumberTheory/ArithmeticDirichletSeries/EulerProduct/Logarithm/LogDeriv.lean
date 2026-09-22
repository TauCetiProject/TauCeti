/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Data
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv

import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The logarithmic derivative of an ideal Euler product

Where the Dirichlet series indexed by the nonzero ideals converges absolutely, the `L`-series of
the norm coefficients of a `TauCeti.EulerProductData` is the unrestricted product of its local
Euler factors, by `TauCeti.EulerProductData.hasProd_eulerFactor`.  A *finite* product has for
logarithmic derivative the sum of the logarithmic derivatives of its factors.  This file proves
that the same holds for the infinite product: at every point strictly to the right of the
ideal-indexed abscissa of absolute convergence at which no local factor vanishes,
`logDeriv` of the `L`-series is the sum over the height-one primes of `logDeriv` of the local
factors.  Each summand is the negative quotient of a log-weighted prime-power series by its local
factor, by
`TauCeti.EulerProductData.logDeriv_eulerFactor_eq`.

Differentiating an infinite product is not a formal consequence of the pointwise product formula:
it needs the convergence to be locally uniform, and that is what absolute convergence at a real
point `σ` further left supplies.  On the half-plane `Re z > σ` the deviation of the local factor at
`P` from `1` is bounded, uniformly in `z`, by the prime-power tail
`∑_{e ≥ 1} ‖D(P ^ e)‖ N(P) ^ (-e σ)`, and those tails are summable over the primes.  That majorant
is exactly what `Summable.hasProdLocallyUniformlyOn_one_add` asks for, so the partial Euler
products converge to the `L`-series locally uniformly on the half-plane, and
`Complex.logDeriv_tendsto` carries their logarithmic derivatives to that of the limit.  The
logarithmic derivative of a partial product is the corresponding finite sum, by
`logDeriv_fun_prod`, so the limit is the asserted infinite sum.

The nonvanishing hypothesis is stated on the local factors, as for the logarithm itself in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/Data.lean`; by
`TauCeti.EulerProductData.LSeries_eq_zero_iff_exists_eulerFactor_eq_zero` it is equivalent to
nonvanishing of the `L`-series, and for a completely multiplicative weight it is automatic.

## Main results

* `TauCeti.EulerProductData.hasSum_logDeriv_eulerFactor` and
  `TauCeti.EulerProductData.logDeriv_LSeries_eq_tsum_logDeriv_eulerFactor`: the logarithmic
  derivative of the `L`-series is the sum of the local logarithmic derivatives.
* `TauCeti.MultiplicativeIdealWeight.hasSum_logDeriv_eulerFactor` and
  `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_logDeriv_eulerFactor`: the same for a
  completely multiplicative weight, where absolute convergence alone supplies the nonvanishing.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

namespace TauCeti

open Complex Filter IsDedekindDomain

open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open IdealArithmeticFunction

variable (D : EulerProductData K)

/-- **The logarithmic derivative of an ideal Euler product is the sum of the local logarithmic
derivatives.**  Strictly to the right of the ideal-indexed abscissa of absolute convergence, and at
a point where no local Euler factor vanishes, the family of logarithmic derivatives of the local
factors is summable over the height-one primes, with sum the logarithmic derivative of the
`L`-series of the norm coefficients. -/
theorem hasSum_logDeriv_eulerFactor {s : ℂ}
    (hs : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < s.re)
    (hne : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0) :
    HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦ logDeriv (D.eulerFactor P) s)
      (logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s) := by
  -- On a half-plane `U ∋ s` of absolute convergence the local factors are `1` plus a family whose
  -- norms are bounded, uniformly on `U`, by a summable function of the prime.  That is Mathlib's
  -- criterion for the partial Euler products to converge locally uniformly on `U`, and a locally
  -- uniform limit of nonvanishing holomorphic functions carries logarithmic derivatives along.
  obtain ⟨σ, hσabs, hσs⟩ := EReal.exists_between_coe_real hs
  have hσs' : σ < s.re := by exact_mod_cast hσs
  set U : Set ℂ := {z : ℂ | σ < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hσs'
  have habs : ∀ z ∈ U, idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < (z.re : EReal) :=
    fun z hz ↦ hσabs.trans (by exact_mod_cast hz)
  have hconv : ∀ z ∈ U, Summable (idealTerm K D.toIdealArithmeticFunction z) := fun z hz ↦
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (habs z hz)
  have hσconv : Summable (idealTerm K D.toIdealArithmeticFunction (σ : ℂ)) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (by simpa using hσabs)
  have hdiffF : ∀ (P : HeightOneSpectrum (𝓞 K)), ∀ z ∈ U,
      DifferentiableAt ℂ (D.eulerFactor P) z := fun P z hz ↦
    (D.hasDerivAt_eulerFactor P
      ((D.abscissaOfAbsConv_localArithmeticFactor_le P).trans_lt (habs z hz))).differentiableAt
  -- the uniform majorant for the deviations of the local factors from `1`
  have hbsumIdeal : Summable fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction (σ : ℂ)
        (P.idealPrimePowerOf e : (Ideal (𝓞 K))⁰)‖ :=
    summable_tsum_norm_idealPrimePowerOf (summable_norm_iff.mpr hσconv)
  have hbsum : Summable fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction (σ : ℂ) (P.primeIdealPow (e + 1))‖ :=
    hbsumIdeal.congr fun P ↦ tsum_congr fun e ↦
      congrArg
        (fun I : (Ideal (𝓞 K))⁰ ↦ ‖idealTerm K D.toIdealArithmeticFunction (σ : ℂ) I‖)
        (Subtype.ext (by simp) :
          (P.idealPrimePowerOf e : (Ideal (𝓞 K))⁰) = P.primeIdealPow (e + 1))
  have hble : ∀ P : HeightOneSpectrum (𝓞 K), ∀ z ∈ U, ‖D.eulerFactor P z - 1‖ ≤ ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction (σ : ℂ) (P.primeIdealPow (e + 1))‖ :=
    fun P z hz ↦ D.norm_eulerFactor_sub_one_le_tsum_norm_of_re_le_re
      (hσconv.comp_injective P.primeIdealPow_injective) (by simpa using hz.le)
  -- the partial Euler products converge to the `L`-series locally uniformly on `U`
  have hone : TendstoLocallyUniformlyOn
      (fun t : Finset (HeightOneSpectrum (𝓞 K)) ↦ fun z ↦
        ∏ P ∈ t, (1 + (D.eulerFactor P z - 1)))
      (fun z ↦ ∏' P : HeightOneSpectrum (𝓞 K), (1 + (D.eulerFactor P z - 1))) atTop U :=
    Summable.hasProdLocallyUniformlyOn_one_add (f := fun P z ↦ D.eulerFactor P z - 1) hUo hbsum
      (.of_forall hble) fun P z hz ↦ ((hdiffF P z hz).sub_const 1).continuousAt.continuousWithinAt
  have hlu : TendstoLocallyUniformlyOn
      (fun t : Finset (HeightOneSpectrum (𝓞 K)) ↦ fun z ↦ ∏ P ∈ t, D.eulerFactor P z)
      (LSeries (normCoeff K D.toIdealArithmeticFunction)) atTop U :=
    (hone.congr fun t z _ ↦ Finset.prod_congr rfl fun P _ ↦ by ring).congr_right fun z hz ↦
      (tprod_congr fun P ↦ (by ring : 1 + (D.eulerFactor P z - 1) = D.eulerFactor P z)).trans
        (D.tprod_eulerFactor (hconv z hz))
  -- a locally uniform limit of holomorphic functions carries logarithmic derivatives along
  have key := Complex.logDeriv_tendsto hUo hsU hlu
    (.of_forall fun t ↦ DifferentiableOn.fun_finsetProd fun P _ z hz ↦
      (hdiffF P z hz).differentiableWithinAt)
    (D.LSeries_ne_zero_of_forall_eulerFactor_ne_zero (hconv s hsU) hne)
  rw [HasSum]
  exact key.congr fun t ↦ logDeriv_fun_prod (fun P _ ↦ hne P) fun P _ ↦ hdiffF P s hsU

/-- **The logarithmic derivative of an ideal Euler product, as a sum over the primes.**  The
`tsum` form of `TauCeti.EulerProductData.hasSum_logDeriv_eulerFactor`. -/
theorem logDeriv_LSeries_eq_tsum_logDeriv_eulerFactor {s : ℂ}
    (hs : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < s.re)
    (hne : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0) :
    logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s =
      ∑' P : HeightOneSpectrum (𝓞 K), logDeriv (D.eulerFactor P) s :=
  (D.hasSum_logDeriv_eulerFactor hs hne).tsum_eq.symm

end EulerProductData

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

/-- **The logarithmic derivative of the Euler product of a completely multiplicative weight.**  A
degree-one weight has local factors `(1 - χ(P) N(P) ^ (-s))⁻¹`, which absolute convergence already
keeps away from `0`, so no nonvanishing hypothesis is needed here. -/
theorem hasSum_logDeriv_eulerFactor (χ : MultiplicativeIdealWeight K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦
        logDeriv ((EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P) s)
      (logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s) := by
  have hcoe : (EulerProductData.ofMultiplicativeIdealWeight χ).toIdealArithmeticFunction
      = χ.toIdealArithmeticFunction :=
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight χ
  have hconv : Summable (idealTerm K χ.toIdealArithmeticFunction s) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  have hne : ∀ P : HeightOneSpectrum (𝓞 K),
      (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s ≠ 0 := by
    intro P
    rw [eulerFactor_ofMultiplicativeIdealWeight χ P
      (norm_div_lt_one_of_summable_idealTerm χ hconv P)]
    exact inv_ne_zero (one_sub_div_ne_zero_of_summable_idealTerm χ hconv P)
  simpa only [hcoe] using
    (EulerProductData.ofMultiplicativeIdealWeight χ).hasSum_logDeriv_eulerFactor
      (by simpa only [hcoe] using hs) hne

/-- **The logarithmic derivative of a completely multiplicative Euler product, as a sum over the
primes.**  The `tsum` form of
`TauCeti.MultiplicativeIdealWeight.hasSum_logDeriv_eulerFactor`. -/
theorem logDeriv_LSeries_eq_tsum_logDeriv_eulerFactor (χ : MultiplicativeIdealWeight K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        logDeriv ((EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P) s :=
  (χ.hasSum_logDeriv_eulerFactor hs).tsum_eq.symm

end MultiplicativeIdealWeight

end TauCeti
