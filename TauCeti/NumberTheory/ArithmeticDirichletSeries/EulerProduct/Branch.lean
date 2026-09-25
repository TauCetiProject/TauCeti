/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Deriv

/-!
# Holomorphic logarithms of ideal `L`-series

The exponential form of an Euler product determines a logarithm only modulo `2πi ℤ`.  It does
not choose a branch: a branch is a single holomorphic function on a region, and choosing one needs
the region to be simply connected as well as zero-free.

This file makes that choice for the norm-regrouped `L`-series of a general
`TauCeti.IdealArithmeticFunction` on a zero-free region of absolute convergence, hence in
particular for the coefficient function underlying `TauCeti.EulerProductData`.  It also specializes
the result to a completely multiplicative ideal weight, whose Euler product supplies nonvanishing
automatically.  The derivative of the chosen logarithm is the logarithmic derivative of the
`L`-series — the same function for every choice of branch, since two branches differ by a locally
constant multiple of `2πi`.

## Main results

* `TauCeti.IdealArithmeticFunction.exists_differentiableOn_exp_eq_LSeries`: a holomorphic
  logarithm for a norm-regrouped ideal coefficient function on a simply connected zero-free
  region of absolute convergence.
* `TauCeti.MultiplicativeIdealWeight.exists_differentiableOn_exp_eq_LSeries`: the branch, together
  with the identification of its derivative, for a completely multiplicative ideal weight.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain Set

open scoped NumberField

namespace IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (f : IdealArithmeticFunction K)

/-- **A holomorphic logarithm after regrouping an ideal-indexed series by norm.**  Let `U` be a
simply connected open set where the ideal-indexed series of `f` converges absolutely and its
norm-regrouped `L`-series does not vanish.  Then there is a holomorphic function `L` on `U` whose
exponential is that `L`-series, and `deriv L` is its logarithmic derivative.

The zero-free hypothesis is necessary for a general coefficient function.  For a completely
multiplicative degree-one weight, the Euler product supplies it automatically. -/
theorem exists_differentiableOn_exp_eq_LSeries {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U)
    (hconv : ∀ s ∈ U, Summable (idealTerm K f s))
    (hzero : ∀ s ∈ U, LSeries (normCoeff K f) s ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      EqOn (Complex.exp ∘ L) (LSeries (normCoeff K f)) U ∧
      ∀ s ∈ U, deriv L s = logDeriv (LSeries (normCoeff K f)) s := by
  have hdiff := differentiableOn_LSeries_normCoeff K f hUo hconv
  have h₀ : 0 ∉ LSeries (normCoeff K f) '' U := by
    rintro ⟨s, hs, hs0⟩
    exact hzero s hs hs0
  obtain ⟨L, hL, hLeq⟩ := exists_differentiableOn_eqOn_exp_comp hUc hUo hdiff h₀
  exact ⟨L, hL, hLeq, fun s hs ↦ deriv_eq_logDeriv_of_eqOn_exp_comp hUo hL hLeq hs⟩

end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- **A holomorphic logarithm of the `L`-series on a simply connected zero-free region.**  Let `U`
be a simply connected open set at every point of which the ideal-indexed series converges
absolutely.  Then there is a holomorphic `L` on `U` with `exp ∘ L` the `L`-series, and `deriv L` is
its logarithmic derivative.

Absolute convergence does two jobs: through the Euler product it makes the `L`-series zero-free on
`U`, and through a point of `U` slightly to the left of each `s` it puts `s` strictly right of the
abscissa of absolute convergence, which is what makes the `L`-series holomorphic there.  Simple
connectedness is what turns pointwise nonvanishing into a single branch. -/
theorem exists_differentiableOn_exp_eq_LSeries {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U)
    (hconv : ∀ s ∈ U, Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      EqOn (Complex.exp ∘ L) (LSeries (normCoeff K χ.toIdealArithmeticFunction)) U ∧
      ∀ s ∈ U, deriv L s = logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s := by
  exact IdealArithmeticFunction.exists_differentiableOn_exp_eq_LSeries
    χ.toIdealArithmeticFunction hUc hUo hconv
    (fun s hs ↦ χ.LSeries_ne_zero_of_summable_idealTerm (hconv s hs))

end MultiplicativeIdealWeight

end TauCeti
