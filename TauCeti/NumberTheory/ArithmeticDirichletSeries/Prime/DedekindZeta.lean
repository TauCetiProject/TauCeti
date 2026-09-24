/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Boundary
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial

/-!
# The von Mangoldt series of all prime ideals is `-ζ_K'/ζ_K`

Over all height-one primes of a number field `K`, the coefficient system
`TauCeti.primeVonMangoldtCoeff K Set.univ` is the norm regrouping of the ideal von Mangoldt
function `Λ_K`, whose partial sums are Chebyshev's `ψ_K`.  This file identifies its Dirichlet
series on `Re s > 1` with the negative logarithmic derivative of the Dedekind zeta function:

```text
∑ n, Λ_K(n) n^{-s} = ∑_A Λ(A) N(A)^{-s} = -ζ_K'(s) / ζ_K(s),   Re s > 1,
```

the number-field analogue of Mathlib's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. It is the trivial-weight case of
`TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`, since the
trivial weight regroups to `ζ_K` (`TauCeti.dedekindZeta_eq_LSeries_normCoeff_one`) and its von
Mangoldt transform is `Λ_K`.

Consequently the series half of the boundary data `TauCeti.PrimeBoundaryRemainder K Set.univ 1`
is no longer a hypothesis: `TauCeti.PrimeBoundaryRemainder.ofDedekindZeta` builds the package
from a single function `G`, continuous on `Re s ≥ 1`, that agrees with
`-ζ_K'(s)/ζ_K(s) - 1/(s - 1)` on `Re s > 1`.  Producing such a `G` needs the meromorphic
continuation of `ζ_K` across `Re s = 1`, with a simple pole at `1` and no zeros on that line; this
file does not supply it.  Given one, `TauCeti.primeIdealTheorem_of_boundary` applied to the
package gives the prime ideal theorem.

## Main results

* `TauCeti.hasSum_idealTerm_vonMangoldt`: the ideal-indexed series of `Λ_K` sums to
  `-ζ_K'(s)/ζ_K(s)` on `Re s > 1`.
* `TauCeti.LSeriesHasSum_primeVonMangoldtCoeff_univ` and
  `TauCeti.LSeries_primeVonMangoldtCoeff_univ_eq_deriv_dedekindZeta_div`: the same for the
  norm-regrouped coefficients, in Mathlib's `LSeries` vocabulary.
* `TauCeti.PrimeBoundaryRemainder.ofDedekindZeta`: boundary data with residue one for all primes
  from a continuous extension of `-ζ_K'/ζ_K - 1/(s - 1)` to `Re s ≥ 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti

open NumberField
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- **The von Mangoldt series of `K` is `-ζ_K'/ζ_K`.** On `Re s > 1` the ideal-indexed series
`∑_A Λ(A) N(A)^{-s}` converges absolutely to `-ζ_K'(s) / ζ_K(s)`. -/
theorem hasSum_idealTerm_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealTerm K IdealArithmeticFunction.vonMangoldt s)
      (-deriv (dedekindZeta K) s / dedekindZeta K s) := by
  have habs : idealAbscissaOfAbsConv K
      (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction < s.re := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1) (fun I ↦ by simp) hs
  have hsum := IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform habs
  have hlog := MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform 1 habs
  simp only [MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    IdealArithmeticFunction.vonMangoldtTransform_one] at hsum hlog
  rw [funext (dedekindZeta_eq_LSeries_normCoeff_one K), neg_div, ← logDeriv_apply, hlog, neg_neg]
  exact hsum.hasSum

/-- **The von Mangoldt coefficients of all primes have Dirichlet series `-ζ_K'/ζ_K`.** On
`Re s > 1` the series of `TauCeti.primeVonMangoldtCoeff K Set.univ` converges absolutely to
`-ζ_K'(s) / ζ_K(s)`.  This is the `LSeriesHasSum` field of
`TauCeti.PrimeBoundaryRemainder K Set.univ δ`, with an explicit sum. -/
theorem LSeriesHasSum_primeVonMangoldtCoeff_univ {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (primeVonMangoldtCoeff K Set.univ n : ℂ)) s
      (-deriv (dedekindZeta K) s / dedekindZeta K s) := by
  simpa only [← normCoeff_vonMangoldt] using regroupByNorm K (hasSum_idealTerm_vonMangoldt hs)

/-- On `Re s > 1` the `LSeries` of the von Mangoldt coefficients of all primes is
`-ζ_K'(s) / ζ_K(s)`. -/
theorem LSeries_primeVonMangoldtCoeff_univ_eq_deriv_dedekindZeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (primeVonMangoldtCoeff K Set.univ n : ℂ)) s =
      -deriv (dedekindZeta K) s / dedekindZeta K s :=
  (LSeriesHasSum_primeVonMangoldtCoeff_univ hs).LSeries_eq

namespace PrimeBoundaryRemainder

variable (G : ℂ → ℂ) (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGζ : ∀ s : ℂ, 1 < s.re →
      G s = -deriv (dedekindZeta K) s / dedekindZeta K s - 1 / (s - 1))

/-- **Boundary data for all primes from the Dedekind zeta function.** A function `G`, continuous
on `Re s ≥ 1`, that agrees on `Re s > 1` with `-ζ_K'(s)/ζ_K(s) - 1/(s - 1)` is the whole of
the analytic input to `TauCeti.PrimeBoundaryRemainder K Set.univ 1`: the series is
`-ζ_K'/ζ_K` by `TauCeti.LSeriesHasSum_primeVonMangoldtCoeff_univ`. -/
noncomputable def ofDedekindZeta : PrimeBoundaryRemainder K Set.univ 1 :=
  ofFunctions (fun s ↦ -deriv (dedekindZeta K) s / dedekindZeta K s) G
    (fun _ hs ↦ LSeriesHasSum_primeVonMangoldtCoeff_univ hs) hG
    (fun s hs ↦ by rw [hGζ s hs, Complex.ofReal_one])

@[simp]
theorem ofDedekindZeta_series (s : {s : ℂ // 1 < s.re}) :
    (ofDedekindZeta G hG hGζ).series s =
      -deriv (dedekindZeta K) (s : ℂ) / dedekindZeta K (s : ℂ) := by
  rw [ofDedekindZeta, ofFunctions_series]

@[simp]
theorem ofDedekindZeta_remainder (s : {s : ℂ // 1 ≤ s.re}) :
    (ofDedekindZeta G hG hGζ).remainder s = G s := by
  rw [ofDedekindZeta, ofFunctions_remainder]

end PrimeBoundaryRemainder

end TauCeti
