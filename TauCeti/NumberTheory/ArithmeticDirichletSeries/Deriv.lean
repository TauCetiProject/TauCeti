/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Derivatives of ideal-indexed Dirichlet series

Differentiating an ideal term `idealTerm K f s I = f I / N(I) ^ s` in `s` returns the same term
weighted by `-log N(I)`.  Summing over the nonzero integral ideals, the derivative of the
norm-regrouped `L`-series is therefore, up to a sign, the ideal-indexed Dirichlet series of the
*logarithmic weighting* `TauCeti.IdealArithmeticFunction.logMul` of `f`, the pointwise product of
`f` with `log N(I)`.

This file proves that identity, its iterated form, and the resulting expression of the logarithmic
derivative as a quotient of two ideal-indexed sums.  The hypothesis throughout is that `s` lies
strictly to the right of `TauCeti.idealAbscissaOfAbsConv K f`, the abscissa of absolute convergence
of the ideal-indexed series; the logarithmic weight can destroy summability on the boundary line
itself, which is why a point of convergence strictly to the left is what the estimates consume.

Two facts do the work.  Regrouping by absolute norm turns `logMul` into Mathlib's `LSeries.logMul`,
because the weight `log N(I)` is constant on a norm fibre
(`TauCeti.normCoeff_logMul`); and a logarithmic weight leaves the ideal-indexed series summable
strictly to the right of any point of absolute convergence
(`TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`).  Mathlib's `LSeries_hasDerivAt`
then supplies the calculus, and `TauCeti.regroupByNorm` converts its conclusion back to a sum over
ideals.

## Main definitions

* `TauCeti.IdealArithmeticFunction.logMul`: the pointwise product of an ideal arithmetic function
  with `log N(I)`, the ideal-indexed counterpart of Mathlib's `LSeries.logMul`.  Its `m`-fold
  iterate weights by `log N(I) ^ m` (`TauCeti.IdealArithmeticFunction.logMul_iterate_apply`).

## Main results

* `TauCeti.hasDerivAt_idealTerm`: the derivative in `s` of an ideal term is the term itself,
  weighted by `-log N(I)`.
* `TauCeti.normCoeff_logMul`: regrouping by absolute norm carries the ideal-indexed logarithmic
  weight to Mathlib's.
* `TauCeti.summable_idealTerm_logMul_of_re_lt_re`: a logarithmic weight preserves absolute
  convergence strictly to the right.
* `TauCeti.IdealArithmeticFunction.hasDerivAt_LSeries_normCoeff` and
  `TauCeti.IdealArithmeticFunction.deriv_LSeries_normCoeff`: the derivative of the regrouped
  `L`-series is `-∑ I, log N(I) f I N(I) ^ (-s)`, summed over the nonzero integral ideals.
* `TauCeti.IdealArithmeticFunction.iteratedDeriv_LSeries_normCoeff`: the `m`-th derivative, with
  the weight `log N(I) ^ m`.
* `TauCeti.IdealArithmeticFunction.logDeriv_LSeries_normCoeff`: the logarithmic derivative as the
  quotient of the two ideal-indexed sums.
* `TauCeti.IdealArithmeticFunction.differentiableOn_LSeries_normCoeff`: absolute convergence of
  an ideal-indexed series throughout an open set makes its norm-regrouped `L`-series holomorphic
  there.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
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

/-! ### The logarithmic weighting -/

namespace IdealArithmeticFunction

variable {K}

/-- **The logarithmic weighting of an ideal arithmetic function**: the pointwise product of `f`
with `log N(I)`.

It is the ideal-indexed counterpart of Mathlib's `LSeries.logMul`, and it is the coefficient
system that appears, up to a sign, when the ideal-indexed Dirichlet series of `f` is
differentiated in `s`. -/
noncomputable def logMul (f : IdealArithmeticFunction K) : IdealArithmeticFunction K :=
  fun I ↦ log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * f I

/-- Evaluation of the logarithmic weighting. -/
theorem logMul_apply (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.logMul I = log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * f I :=
  (rfl)

/-- Evaluation of an iterated logarithmic weighting: the weight is the `m`-th power of
`log N(I)`. -/
theorem logMul_iterate_apply (f : IdealArithmeticFunction K) (m : ℕ) (I : (Ideal (𝓞 K))⁰) :
    logMul^[m] f I = log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ m * f I := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', logMul_apply, ih]
      ring

end IdealArithmeticFunction

open IdealArithmeticFunction

/-- The ideal term of a logarithmic weighting is the original term weighted by `log N(I)`. -/
theorem idealTerm_logMul (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f.logMul s I =
      log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I := by
  rw [idealTerm_def, idealTerm_def, logMul_apply, mul_div_assoc]

/-- The absolute value of a logarithmically weighted ideal term: the weight `log N(I)` is a
nonnegative real number, so it passes through the norm unchanged. -/
theorem norm_idealTerm_logMul (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f.logMul s I‖ =
      Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) * ‖idealTerm K f s I‖ := by
  have hlog : ‖log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)‖ =
      Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg _)]
  rw [idealTerm_logMul, norm_mul, hlog]

/-- **Regrouping by absolute norm carries the logarithmic weight to Mathlib's.**  The weight
`log N(I)` depends on the ideal only through its absolute norm, so it is constant on a norm fibre
and factors out of the regrouping. -/
@[simp]
theorem normCoeff_logMul (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f.logMul n = LSeries.logMul (⇑(normCoeff K f)) n := by
  have hf : f.logMul = fun I ↦ f I * log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) :=
    funext fun I ↦ mul_comm _ _
  rw [hf, normCoeff_fun_mul_comp_absNorm K f (fun m : ℕ ↦ log (m : ℂ)) n]
  exact mul_comm _ _

/-- Iterating the previous identity: the `m`-fold logarithmic weight is carried to Mathlib's. -/
@[simp]
theorem normCoeff_logMul_iterate (f : IdealArithmeticFunction K) (m n : ℕ) :
    normCoeff K (logMul^[m] f) n = LSeries.logMul^[m] (⇑(normCoeff K f)) n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', normCoeff_logMul]
      simp only [LSeries.logMul, ih]

/-- **A logarithmic weight preserves absolute convergence strictly to the right.**  The strict
inequality is essential: `log N(I)` grows, so the weighted series can diverge on the very line
where the unweighted one converges. -/
theorem summable_idealTerm_logMul_of_re_lt_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re < s'.re) (hs : Summable (idealTerm K f s)) :
    Summable (idealTerm K f.logMul s') := by
  rw [← summable_norm_iff]
  exact (summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re K h hs).congr fun I ↦
    (norm_idealTerm_logMul K f s' I).symm

/-- Iterating a logarithmic weight still preserves absolute convergence strictly to the right:
each of the `m` weights is absorbed on a shorter interval of real parts. -/
theorem summable_idealTerm_logMul_iterate_of_re_lt_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (m : ℕ) (h : s.re < s'.re) (hs : Summable (idealTerm K f s)) :
    Summable (idealTerm K (logMul^[m] f) s') := by
  induction m generalizing s' with
  | zero => simpa using summable_idealTerm_of_re_le_re K h.le hs
  | succ m ih =>
      -- Absorb the last weight between the midpoint of the two real parts and `s'`.
      rw [Function.iterate_succ_apply']
      have hleft : s.re < (((s.re + s'.re) / 2 : ℝ) : ℂ).re := by
        simp only [Complex.ofReal_re]
        linarith
      have hright : (((s.re + s'.re) / 2 : ℝ) : ℂ).re < s'.re := by
        simp only [Complex.ofReal_re]
        linarith
      exact summable_idealTerm_logMul_of_re_lt_re K hright (ih hleft)

namespace IdealArithmeticFunction

/-! ### Differentiating the regrouped `L`-series -/

/-- **Termwise differentiation of an ideal-indexed Dirichlet series.**  Strictly to the right of
the ideal-indexed abscissa of absolute convergence, the norm-regrouped `L`-series of `f` is
differentiable and its derivative is the ideal-indexed series of `-f.logMul`, that is
`-∑ I, log N(I) f I N(I) ^ (-s)`. -/
theorem hasDerivAt_LSeries_normCoeff (f : IdealArithmeticFunction K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    HasDerivAt (LSeries (normCoeff K f))
      (-∑' I : (Ideal (𝓞 K))⁰, idealTerm K f.logMul s I) s := by
  obtain ⟨y, hy, hys⟩ := exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  have hsum : Summable (idealTerm K f.logMul s) :=
    summable_idealTerm_logMul_of_re_lt_re K (by simpa using hys) hy
  have habs : LSeries.abscissaOfAbsConv (normCoeff K f) < s.re :=
    lt_of_le_of_lt (abscissaOfAbsConv_normCoeff_le K f) hs
  have h := LSeries_hasDerivAt habs
  rwa [LSeries_congr (fun {n} _ ↦ (normCoeff_logMul K f n).symm) s,
    LSeries_normCoeff K hsum] at h

/-- **The derivative of a norm-regrouped ideal Dirichlet series.**  The value form of
`TauCeti.IdealArithmeticFunction.hasDerivAt_LSeries_normCoeff`. -/
theorem deriv_LSeries_normCoeff (f : IdealArithmeticFunction K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    deriv (LSeries (normCoeff K f)) s =
      -∑' I : (Ideal (𝓞 K))⁰, idealTerm K f.logMul s I :=
  (hasDerivAt_LSeries_normCoeff K f hs).deriv

/-- **The higher derivatives of a norm-regrouped ideal Dirichlet series.**  The `m`-th derivative
carries the weight `log N(I) ^ m` and the sign `(-1) ^ m`. -/
theorem iteratedDeriv_LSeries_normCoeff (f : IdealArithmeticFunction K) (m : ℕ) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    iteratedDeriv m (LSeries (normCoeff K f)) s =
      (-1) ^ m * ∑' I : (Ideal (𝓞 K))⁰, idealTerm K (logMul^[m] f) s I := by
  obtain ⟨y, hy, hys⟩ := exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  have hsum : Summable (idealTerm K (logMul^[m] f) s) :=
    summable_idealTerm_logMul_iterate_of_re_lt_re K m (by simpa using hys) hy
  have habs : LSeries.abscissaOfAbsConv (normCoeff K f) < s.re :=
    lt_of_le_of_lt (abscissaOfAbsConv_normCoeff_le K f) hs
  rw [LSeries_iteratedDeriv m habs,
    LSeries_congr (fun {n} _ ↦ (normCoeff_logMul_iterate K f m n).symm) s,
    LSeries_normCoeff K hsum]

/-- **The logarithmic derivative of a norm-regrouped ideal Dirichlet series.**  Strictly to the
right of the ideal-indexed abscissa of absolute convergence it is the quotient of the
logarithmically weighted ideal-indexed sum by the unweighted one.

No nonvanishing hypothesis is needed: both sides are the same quotient, and
`TauCeti.LSeries_normCoeff` identifies the denominator with the value of the `L`-series. -/
theorem logDeriv_LSeries_normCoeff (f : IdealArithmeticFunction K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    logDeriv (LSeries (normCoeff K f)) s =
      -(∑' I : (Ideal (𝓞 K))⁰, idealTerm K f.logMul s I) /
        ∑' I : (Ideal (𝓞 K))⁰, idealTerm K f s I := by
  rw [logDeriv_apply, deriv_LSeries_normCoeff K f hs,
    LSeries_normCoeff K (summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs)]

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
