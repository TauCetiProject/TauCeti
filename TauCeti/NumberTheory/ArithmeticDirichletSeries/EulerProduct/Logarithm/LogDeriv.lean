/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Data

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.LSeries.Deriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv

/-!
# The logarithmic derivative of an ideal Euler product

Where the Dirichlet series indexed by the nonzero ideals converges absolutely, the `L`-series of
the norm coefficients of a `TauCeti.EulerProductData` is the unrestricted product of its local
Euler factors, by `TauCeti.EulerProductData.hasProd_eulerFactor`.  A *finite* product has for
logarithmic derivative the sum of the logarithmic derivatives of its factors.  This file proves
that the same holds for the infinite product: at every point strictly to the right of the
ideal-indexed abscissa of absolute convergence at which no local factor vanishes,
`logDeriv` of the `L`-series is the sum over the height-one primes of `logDeriv` of the local
factors.

Differentiating an infinite product is not a formal consequence of the pointwise product formula:
it needs the convergence to be locally uniform, and that is what absolute convergence at a real
point `σ` further left supplies.  On the half-plane `Re z > σ` the deviation of the local factor at
`P` from `1` is bounded, uniformly in `z`, by the prime-power tail
`∑_{e ≥ 1} ‖D(P ^ (e + 1))‖ N(P) ^ (-(e + 1) σ)`, and those tails are summable over the primes.
Outside a finite set of primes that bound is at most `1 / 2`, so there the local factor stays in
the slit plane, its principal logarithm is holomorphic on the whole half-plane, and those
logarithms are dominated by a summable function of `P`.  Weierstrass' theorem, in the form
`Complex.hasSum_deriv_of_summable_norm`, differentiates their sum term by term.  The finitely many
remaining factors are holomorphic, and nonzero at the point in question, so they contribute a
finite sum of logarithmic derivatives.

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
  -- The proof splits the primes into those whose local factor is uniformly close to `1` on a
  -- half-plane `U ∋ s` of absolute convergence and the finitely many others.  Over the first set
  -- the principal logarithms of the local factors are holomorphic on `U` and dominated by a
  -- summable function, so their sum differentiates term by term and exponentiates to the partial
  -- Euler product over that set; the second set contributes a finite product.  Splitting
  -- `logDeriv` along that factorisation of the `L`-series and recombining the two families gives
  -- the result.
  classical
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
  set b : HeightOneSpectrum (𝓞 K) → ℝ := fun P ↦ ∑' e : ℕ,
    ‖idealTerm K D.toIdealArithmeticFunction (σ : ℂ) (P.primeIdealPow (e + 1))‖
  have hbsum : Summable b := summable_tsum_norm_idealTerm_primeIdealPow_succ hσconv
  have hble : ∀ P : HeightOneSpectrum (𝓞 K), ∀ z ∈ U, ‖D.eulerFactor P z - 1‖ ≤ b P :=
    fun P z hz ↦ D.norm_eulerFactor_sub_one_le_tsum_norm_of_re_le hσconv (by simpa using hz.le) P
  -- the primes at which the majorant does control the logarithm; the others are finite in number
  set T : Set (HeightOneSpectrum (𝓞 K)) := {P | b P < 1 / 2}
  have hfin : Tᶜ.Finite := Filter.eventually_cofinite.mp
    (hbsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (by norm_num)))
  have hTfin : Fintype (Tᶜ : Set (HeightOneSpectrum (𝓞 K))) := hfin.fintype
  have hsmall : ∀ (P : T), ∀ z ∈ U, ‖D.eulerFactor P.1 z - 1‖ ≤ 1 / 2 :=
    fun P z hz ↦ (hble P.1 z hz).trans P.2.le
  have hslit : ∀ (P : T), ∀ z ∈ U, D.eulerFactor P.1 z ∈ slitPlane := by
    intro P z hz
    have h1 : ‖D.eulerFactor P.1 z - 1‖ < 1 := lt_of_le_of_lt (hsmall P z hz) (by norm_num)
    simpa using Complex.mem_slitPlane_of_norm_lt_one h1
  -- the controlled local logarithms are holomorphic and dominated by a summable function
  have hgdiff : ∀ P : T, DifferentiableOn ℂ (fun z ↦ log (D.eulerFactor P.1 z)) U := by
    intro P z hz
    exact ((hdiffF P.1 z hz).clog (hslit P z hz)).differentiableWithinAt
  have hgle : ∀ (P : T) (z : ℂ), z ∈ U → ‖log (D.eulerFactor P.1 z)‖ ≤ 3 / 2 * b P.1 := by
    intro P z hz
    have hone : D.eulerFactor P.1 z = 1 + (D.eulerFactor P.1 z - 1) := by ring
    calc ‖log (D.eulerFactor P.1 z)‖
        = ‖log (1 + (D.eulerFactor P.1 z - 1))‖ := by rw [← hone]
      _ ≤ 3 / 2 * ‖D.eulerFactor P.1 z - 1‖ :=
          Complex.norm_log_one_add_half_le_self (hsmall P z hz)
      _ ≤ 3 / 2 * b P.1 := by gcongr; exact hble P.1 z hz
  have hu : Summable fun P : T ↦ 3 / 2 * b P.1 :=
    (hbsum.mul_left (3 / 2)).comp_injective Subtype.val_injective
  -- Weierstrass: the sum of those logarithms differentiates term by term
  have hderiv := Complex.hasSum_deriv_of_summable_norm hu hgdiff hUo hgle hsU
  have hderiv_eq : ∀ P : T,
      deriv (fun z ↦ log (D.eulerFactor P.1 z)) s = logDeriv (D.eulerFactor P.1) s := by
    intro P
    rw [logDeriv_apply, ((hdiffF P.1 s hsU).hasDerivAt.clog (hslit P s hsU)).deriv]
  simp only [hderiv_eq] at hderiv
  -- the sum of those logarithms exponentiates to the product over the controlled primes
  have hlogsummable : ∀ z ∈ U, Summable fun P : T ↦ log (D.eulerFactor P.1 z) :=
    fun z hz ↦ Summable.of_norm_bounded hu fun P ↦ hgle P z hz
  have hdecomp : ∀ z ∈ U, LSeries (normCoeff K D.toIdealArithmeticFunction) z =
      exp (∑' P : T, log (D.eulerFactor P.1 z)) *
        ∏ P : (Tᶜ : Set (HeightOneSpectrum (𝓞 K))), D.eulerFactor P.1 z := by
    intro z hz
    refine (D.hasProd_eulerFactor (hconv z hz)).unique
      (HasProd.mul_compl (f := fun P ↦ D.eulerFactor P z) (s := T) ?_ (hasProd_fintype _))
    exact Complex.hasProd_of_hasSum_log (fun P ↦ slitPlane_ne_zero (hslit P z hz))
      (hlogsummable z hz).hasSum
  -- the logarithmic derivative of that decomposition
  have hhdiff : DifferentiableAt ℂ (fun w ↦ ∑' P : T, log (D.eulerFactor P.1 w)) s :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hgdiff hUo hgle).differentiableAt
      (hUo.mem_nhds hsU)
  have hEdiff : DifferentiableAt ℂ (fun z ↦ exp (∑' P : T, log (D.eulerFactor P.1 z))) s :=
    hhdiff.cexp
  have hGdiff : DifferentiableAt ℂ
      (∏ P : (Tᶜ : Set (HeightOneSpectrum (𝓞 K))), D.eulerFactor P.1) s :=
    DifferentiableAt.finsetProd fun P _ ↦ hdiffF P.1 s hsU
  have hGne : (∏ P : (Tᶜ : Set (HeightOneSpectrum (𝓞 K))), D.eulerFactor P.1) s ≠ 0 := by
    rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr fun P _ ↦ hne P.1
  have hEq : LSeries (normCoeff K D.toIdealArithmeticFunction) =ᶠ[nhds s]
      (fun z ↦ exp (∑' P : T, log (D.eulerFactor P.1 z))) *
        (∏ P : (Tᶜ : Set (HeightOneSpectrum (𝓞 K))), D.eulerFactor P.1) := by
    filter_upwards [hUo.mem_nhds hsU] with z hz
    simpa [Finset.prod_apply] using hdecomp z hz
  have hlogE : logDeriv (fun z ↦ exp (∑' P : T, log (D.eulerFactor P.1 z))) s
      = deriv (fun w ↦ ∑' P : T, log (D.eulerFactor P.1 w)) s := by
    rw [logDeriv_apply, hhdiff.hasDerivAt.cexp.deriv, mul_comm, mul_div_assoc,
      div_self (exp_ne_zero _), mul_one]
  have hlog : logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s
      = deriv (fun w ↦ ∑' P : T, log (D.eulerFactor P.1 w)) s
        + ∑ P : (Tᶜ : Set (HeightOneSpectrum (𝓞 K))), logDeriv (D.eulerFactor P.1) s := by
    rw [(logDeriv_congr_nhds hEq).eq_of_nhds,
      logDeriv_mul s (by simp [exp_ne_zero]) hGne hEdiff hGdiff, hlogE,
      logDeriv_prod (fun P _ ↦ hne P.1) fun P _ ↦ hdiffF P.1 s hsU]
  rw [hlog]
  exact HasSum.add_compl (f := fun P ↦ logDeriv (D.eulerFactor P) s) (s := T) hderiv
    (hasSum_fintype _)

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
