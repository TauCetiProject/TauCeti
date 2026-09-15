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

end TauCeti
