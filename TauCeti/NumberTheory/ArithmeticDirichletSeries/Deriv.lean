/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Derivatives of ideal-indexed Dirichlet series

Differentiating an ideal term `idealTerm K f s I = f I / N(I) ^ s` in `s` returns the same term
weighted by `-log N(I)`.

This is the pointwise input to differentiating an ideal-indexed Dirichlet series **termwise**: such
an argument needs the derivative of each term together with a summable bound on those derivatives,
and this supplies the first.  The logarithmic weight it produces is also what that bound has to
absorb.

## Main results

* `TauCeti.hasDerivAt_idealTerm`: the derivative in `s` of an ideal term is the term itself,
  weighted by `-log N(I)`.
* `TauCeti.IdealArithmeticFunction.differentiableOn_LSeries_normCoeff`: absolute convergence of
  an ideal-indexed series throughout an open set makes its norm-regrouped `L`-series holomorphic
  there.
-/

public section

namespace TauCeti

open Complex

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The derivative of an ideal term.**  Differentiating `f I / N(I) ^ s` in `s` returns the same
term weighted by `-log N(I)`.

Differentiating a sum of ideal terms termwise needs this at each term.  The logarithm is the
complex one, of a positive real argument: `N(I) ≥ 1` for a nonzero ideal, so it agrees with
`Real.log N(I)` and is real and nonnegative. -/
theorem hasDerivAt_idealTerm (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    HasDerivAt (fun z ↦ idealTerm K f z I)
      (-(Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I)) s := by
  have hn : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 :=
    (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
  -- An ideal term is the `L`-series term of the constant coefficient `f I` at `N(I)`, so
  -- Mathlib's `LSeries.hasDerivAt_term` already does the calculus.
  have h := LSeries.hasDerivAt_term (fun _ ↦ f I) (Ideal.absNorm (I : Ideal (𝓞 K))) s
  simp only [LSeries.term_of_ne_zero hn, LSeries.logMul] at h
  simpa [idealTerm_def, mul_div_assoc] using h

namespace IdealArithmeticFunction

/-- **Holomorphy after regrouping an ideal-indexed series by norm.** If the ideal-indexed series
of `f` converges absolutely at every point of an open set `U`, then the `L`-series of its norm
coefficients is holomorphic on `U`.

At each point, openness supplies a nearby point strictly to its left which remains in `U`.
Absolute convergence there puts the original point strictly right of the abscissa of absolute
convergence, where Mathlib's `LSeries` is differentiable. -/
theorem differentiableOn_LSeries_normCoeff (f : IdealArithmeticFunction K) {U : Set ℂ}
    (hUo : IsOpen U) (hconv : ∀ s ∈ U, Summable (idealTerm K f s)) :
    DifferentiableOn ℂ (LSeries (normCoeff K f)) U := by
  refine (LSeries_differentiableOn _).mono fun s hs ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo s hs
  have hmem : s - ((ε / 2 : ℝ) : ℂ) ∈ U := by
    refine hball ?_
    simp only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  refine ((LSeriesSummable_normCoeff K (hconv _ hmem)).abscissaOfAbsConv_le).trans_lt ?_
  rw [Complex.sub_re, Complex.ofReal_re, EReal.coe_lt_coe_iff]
  linarith

end IdealArithmeticFunction

end TauCeti
