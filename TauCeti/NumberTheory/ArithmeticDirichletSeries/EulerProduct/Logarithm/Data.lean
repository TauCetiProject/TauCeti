/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Branch
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PowerIndex

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# The zeros and the logarithm of an ideal Euler product

A `TauCeti.EulerProductData` over a number field `K` carries a coprime-multiplicative coefficient
function on the nonzero ideals of `𝓞 K`, together with its prime-power local data, and where its
ideal-indexed Dirichlet series converges absolutely its local factors
`TauCeti.EulerProductData.eulerFactor` have an unrestricted product equal to the `L`-series of its
norm coefficients
(`TauCeti.EulerProductData.hasProd_eulerFactor`).  A convergent infinite product of nonzero factors
may still vanish, so that identity alone decides neither whether the `L`-series vanishes nor whether
the product has a logarithm.

This file settles both questions for a general Euler product.  The local factor at `P` is
`1 + ∑_{e ≥ 1} D(P ^ e) N(P) ^ (-e s)`, and the tails over the distinct prime-power ideals form a
subfamily of the absolutely convergent ideal-indexed series; so the local factors are `1` up to a
summable error.  For such a product the two questions have the same answer: the `L`-series vanishes
exactly when some local factor does, and only finitely many local factors can vanish at all.  When
none does, the sum of the principal logarithms of the local factors converges and its exponential is
the `L`-series.

The degree-one case is separate: a completely multiplicative weight has local factors
`(1 - χ(P) N(P) ^ (-s))⁻¹`, which are visibly nonzero, so there absolute convergence alone gives
nonvanishing (`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`).  For
general data the hypothesis cannot be dropped: the local series is an arbitrary power series in
`N(P) ^ (-s)` with constant term `1`, and already a local factor `1 + c N(P) ^ (-s)` with `c ≠ 0`
vanishes for some `s`.

## Main results

* `TauCeti.EulerProductData.summable_eulerFactor_sub_one`: the local Euler factors differ from `1`
  by a summable error.
* `TauCeti.EulerProductData.norm_eulerFactor_sub_one_le_tsum_norm_of_re_le_re`: the deviation of a
  local factor from `1` is uniformly bounded on a right half-plane by a prime-power tail.
* `TauCeti.EulerProductData.eulerFactor_ne_zero_of_tsum_norm_lt_one` and
  `TauCeti.EulerProductData.finite_setOf_eulerFactor_eq_zero`: a local factor whose prime-power
  tail has norm sum less than `1` is nonzero, and only finitely many local factors vanish.
* `TauCeti.EulerProductData.LSeries_eq_zero_iff_exists_eulerFactor_eq_zero`: the `L`-series of the
  norm coefficients vanishes exactly when some local Euler factor vanishes.
* `TauCeti.EulerProductData.exp_tsum_log_eulerFactor_eq_LSeries`: with every local factor nonzero,
  the `L`-series is the exponential of the sum of the principal logarithms of the local factors.
* `TauCeti.EulerProductData.exists_differentiableOn_exp_eq_LSeries`: a holomorphic logarithm of the
  `L`-series on a simply connected region of absolute convergence with nonvanishing local factors.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain Set

open scoped nonZeroDivisors NumberField

namespace EulerProductData

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

section Pointwise

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local factors are `1` up to a summable error -/

/-- **The local Euler factor, with its constant term split off.**  The `e = 0` term of the local
series at `P` is the value at the unit ideal, which coprime multiplicativity fixes to be `1`; only
convergence of the local series at `P` is needed. -/
theorem eulerFactor_eq_one_add_tsum {P : HeightOneSpectrum (𝓞 K)}
    (hsP : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow e)) :
    D.eulerFactor P s =
      1 + ∑' e : ℕ, idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)) := by
  have h0 : idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow 0) = 1 := by
    have hpow : P.primeIdealPow 0 = 1 := Subtype.ext (by simp)
    rw [hpow, idealTerm_def]
    simp [D.isMultiplicative.map_one, Ideal.one_eq_top]
  rw [D.eulerFactor_eq_tsum P, hsP.tsum_eq_zero_add, h0]

/-- **The local Euler factors differ from `1` by a summable error.**  This is the quantitative
content of absolute convergence at `s`: the deviation of the local factor at `P` from `1` is the
tail of the local series, and those tails are a subfamily of the ideal-indexed series. -/
theorem summable_eulerFactor_sub_one (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ D.eulerFactor P s - 1 := by
  have htails : Summable fun Pk : HeightOneSpectrum (𝓞 K) × ℕ ↦
      idealTerm K D.toIdealArithmeticFunction s (Pk.1.primeIdealPow (Pk.2 + 1)) :=
    (summable_comp_idealPrimePowerOf hs).congr fun ⟨P, k⟩ ↦
      congrArg _ (Subtype.ext (by simp))
  exact htails.prod.congr fun P ↦ by
    rw [D.eulerFactor_eq_one_add_tsum (hs.comp_injective P.primeIdealPow_injective),
      add_sub_cancel_left]

/-- The deviation of a local Euler factor from `1` is at most the norm sum of the prime-power
tail at that prime. -/
theorem norm_eulerFactor_sub_one_le {P : HeightOneSpectrum (𝓞 K)}
    (hsP : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow e)) :
    ‖D.eulerFactor P s - 1‖ ≤
      ∑' e : ℕ, ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ := by
  rw [D.eulerFactor_eq_one_add_tsum hsP, add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm (summable_norm_iff.mpr ((summable_nat_add_iff 1).mpr hsP))

/-- **The local Euler factors approach `1` uniformly on a half-plane of absolute convergence.**
To the right of a point `w` of absolute convergence, the deviation of the local factor at `P` from
`1` is bounded, independently of the point, by the prime-power tail at `P` computed at `w`. -/
theorem norm_eulerFactor_sub_one_le_tsum_norm_of_re_le_re {w z : ℂ}
    (hw : Summable (idealTerm K D.toIdealArithmeticFunction w)) (hz : w.re ≤ z.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖D.eulerFactor P z - 1‖ ≤ ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction w (P.primeIdealPow (e + 1))‖ := by
  have hzP : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction z (P.primeIdealPow e) :=
    (summable_idealTerm_of_re_le_re K hz hw).comp_injective P.primeIdealPow_injective
  have hwP : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction w (P.primeIdealPow e) :=
    hw.comp_injective P.primeIdealPow_injective
  refine (D.norm_eulerFactor_sub_one_le hzP).trans (Summable.tsum_le_tsum
    (fun e ↦ norm_idealTerm_le_of_re_le_re K _ hz _)
    (summable_norm_iff.mpr ((summable_nat_add_iff 1).mpr hzP))
    (summable_norm_iff.mpr ((summable_nat_add_iff 1).mpr hwP)))

/-! ### Nonvanishing -/

/-- **A local Euler factor with a small prime-power tail is nonzero.**  This is the criterion the
nonvanishing theorems below consume; it is checkable from a bound on the coefficients at the
powers of the single prime `P`. -/
theorem eulerFactor_ne_zero_of_tsum_norm_lt_one {P : HeightOneSpectrum (𝓞 K)}
    (hsP : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow e))
    (hP : ∑' e : ℕ, ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ < 1) :
    D.eulerFactor P s ≠ 0 := fun h ↦ by
  have := (D.norm_eulerFactor_sub_one_le hsP).trans_lt hP
  rw [h] at this
  simp at this

/-- **Only finitely many local Euler factors can vanish.**  The deviations from `1` are summable,
hence smaller than `1` outside a finite set of primes. -/
theorem finite_setOf_eulerFactor_eq_zero
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    {P : HeightOneSpectrum (𝓞 K) | D.eulerFactor P s = 0}.Finite := by
  have hsmall : ∀ᶠ P in Filter.cofinite, ‖D.eulerFactor P s - 1‖ < 1 :=
    (D.summable_eulerFactor_sub_one hs).tendsto_cofinite_zero.norm.eventually
      (eventually_lt_nhds (by simp))
  refine (Filter.eventually_cofinite.mp hsmall).subset fun P hP ↦ ?_
  simp only [mem_ofPred_eq] at hP
  simp [hP]

/-- **A vanishing local Euler factor kills the `L`-series.**  Every finite partial product over a
set of primes containing the offending one is zero, and those partial products converge to the
`L`-series. -/
theorem LSeries_eq_zero_of_eulerFactor_eq_zero
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s))
    {P : HeightOneSpectrum (𝓞 K)} (hP : D.eulerFactor P s = 0) :
    LSeries (normCoeff K D.toIdealArithmeticFunction) s = 0 := by
  exact (D.hasProd_eulerFactor hs).unique (hasProd_zero_of_exists_eq_zero ⟨P, hP⟩)

/-- **The Euler product of nonvanishing local factors does not vanish.**  Absolute convergence
makes the local factors `1` up to a summable error, and such a product vanishes only if one of its
factors does. -/
theorem LSeries_ne_zero_of_forall_eulerFactor_ne_zero
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s))
    (hP : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0) :
    LSeries (normCoeff K D.toIdealArithmeticFunction) s ≠ 0 := by
  rw [← D.tprod_eulerFactor hs]
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun P : HeightOneSpectrum (𝓞 K) ↦ D.eulerFactor P s - 1)
    (fun P ↦ by simpa using hP P)
    (summable_norm_iff.mpr (D.summable_eulerFactor_sub_one hs))
  simpa using h

/-- **The `L`-series of a general Euler product vanishes exactly where a local factor does.**  On
the region of absolute convergence the zeros of an ideal Euler product are therefore local data. -/
theorem LSeries_eq_zero_iff_exists_eulerFactor_eq_zero
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    LSeries (normCoeff K D.toIdealArithmeticFunction) s = 0 ↔
      ∃ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hP⟩ ↦ D.LSeries_eq_zero_of_eulerFactor_eq_zero hs hP⟩
  by_contra hne
  exact D.LSeries_ne_zero_of_forall_eulerFactor_ne_zero hs (not_exists.mp hne) h

/-! ### The logarithm of the product -/

/-- **The principal logarithms of the local Euler factors are summable.**  No nonvanishing
hypothesis is needed: `Complex.log 0 = 0`, and the finitely many vanishing factors of
`TauCeti.EulerProductData.finite_setOf_eulerFactor_eq_zero` cannot affect summability. -/
theorem summable_log_eulerFactor (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ log (D.eulerFactor P s) :=
  (D.summable_eulerFactor_sub_one hs).neg.clog_one_sub.congr fun P ↦ by
    (congr 1; ring)

/-- **The Euler product in exponential form.**  Where the ideal-indexed Dirichlet series converges
absolutely and no local Euler factor vanishes, the `L`-series of the norm coefficients is the
exponential of the sum of the principal logarithms of the local factors.

As `exp` is not injective this does not exhibit a logarithm *of* the `L`-series; for that see
`TauCeti.EulerProductData.exists_differentiableOn_exp_eq_LSeries`. -/
theorem exp_tsum_log_eulerFactor_eq_LSeries
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s))
    (hP : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0) :
    exp (∑' P : HeightOneSpectrum (𝓞 K), log (D.eulerFactor P s)) =
      LSeries (normCoeff K D.toIdealArithmeticFunction) s := by
  rw [← D.tprod_eulerFactor hs]
  exact Complex.cexp_tsum_eq_tprod hP (D.summable_log_eulerFactor hs)

end Pointwise

/-- **A holomorphic logarithm of the `L`-series of an Euler product.**  On a simply connected open
set where the ideal-indexed Dirichlet series converges absolutely and no local Euler factor
vanishes, there is a holomorphic `L` with `exp ∘ L` the `L`-series of the norm coefficients, and
`deriv L` is its logarithmic derivative.

For a completely multiplicative weight the local hypothesis is automatic; in general it is the
hypothesis that cuts out a zero-free region, by
`TauCeti.EulerProductData.LSeries_eq_zero_iff_exists_eulerFactor_eq_zero`. -/
theorem exists_differentiableOn_exp_eq_LSeries (D : EulerProductData K) {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hconv : ∀ z ∈ U, Summable (idealTerm K D.toIdealArithmeticFunction z))
    (hne : ∀ z ∈ U, ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      EqOn (exp ∘ L) (LSeries (normCoeff K D.toIdealArithmeticFunction)) U ∧
      ∀ z ∈ U, deriv L z = logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) z :=
  IdealArithmeticFunction.exists_differentiableOn_exp_eq_LSeries _ hUc hUo hconv
    fun z hz ↦ D.LSeries_ne_zero_of_forall_eulerFactor_ne_zero (hconv z hz) (hne z hz)

end EulerProductData

end TauCeti
