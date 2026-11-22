/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Absolute convergence of ideal convolution

The product of two absolutely convergent ideal-indexed Dirichlet series is the Dirichlet
series of their ideal convolution. This statement retains absolute convergence before
regrouping by norm: convergence of the grouped series alone can conceal cancellation among
ideals of the same norm, and does not suffice for ideal Euler products.

`TauCeti.hasSum_idealTerm_convolution` gives the product formula with specified sums;
`TauCeti.summable_idealTerm_convolution` supplies absolute convergence, including at a common
boundary point when both factors converge there. The ideal-indexed abscissa of the convolution
is at most the maximum of the two original abscissae, with infinite abscissae allowed.

The argument follows Mathlib's `LSeriesHasSum.convolution`: form the absolutely convergent
product family and regroup it by multiplication. Here the fibres are the finite factorizations
of a nonzero ideal, rather than the factorizations of a positive integer.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Multiplying coefficients by `N(I) ^ (-s)` commutes with ideal convolution. -/
@[simp]
theorem idealTerm_convolution (f g : IdealArithmeticFunction K) (s : ℂ) :
    idealTerm K (f.convolution g) s =
      IdealArithmeticFunction.convolution (idealTerm K f s) (idealTerm K g s) := by
  funext A
  simp only [idealTerm_def, IdealArithmeticFunction.convolution_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hA := congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
    (Ideal.mem_divisorsAntidiagonal.mp hp)
  simp only [Submonoid.coe_mul, map_mul] at hA
  rw [← hA, Nat.cast_mul, Complex.natCast_mul_cpow]
  exact mul_div_mul_comm _ _ _ _

/-- The ideal-indexed Dirichlet series of a convolution has the product of the sums of
the two factors. The hypotheses assert absolute convergence of the ungrouped ideal series. -/
theorem hasSum_idealTerm_convolution {f g : IdealArithmeticFunction K} {s a b : ℂ}
    (hf : HasSum (idealTerm K f s) a) (hg : HasSum (idealTerm K g s) b) :
    HasSum (idealTerm K (f.convolution g) s) (a * b) := by
  have hprod := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  have h := (hf.mul hg hprod).tsum_fiberwise
    (fun p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ ↦ p.1 * p.2)
  refine h.congr_fun fun A ↦ ?_
  have hfiber : (fun p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ ↦ p.1 * p.2) ⁻¹' {A} =
      (Ideal.divisorsAntidiagonal A : Set ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰)) := by
    ext p
    simp
  rw [hfiber, Finset.tsum_subtype' (Ideal.divisorsAntidiagonal A)
    (fun p ↦ idealTerm K f s p.1 * idealTerm K g s p.2), idealTerm_convolution,
    IdealArithmeticFunction.convolution_apply]

/-- Ideal convolution preserves absolute convergence at every common point of absolute
convergence of its factors. No multiplicativity or sign condition is required. -/
theorem summable_idealTerm_convolution {f g : IdealArithmeticFunction K} {s : ℂ}
    (hf : Summable (idealTerm K f s)) (hg : Summable (idealTerm K g s)) :
    Summable (idealTerm K (f.convolution g) s) :=
  (hasSum_idealTerm_convolution hf.hasSum hg.hasSum).summable

/-- The sum of the ideal-indexed convolution series is the product of the two ideal-indexed
sums wherever both factors converge absolutely. -/
theorem tsum_idealTerm_convolution {f g : IdealArithmeticFunction K} {s : ℂ}
    (hf : Summable (idealTerm K f s)) (hg : Summable (idealTerm K g s)) :
    ∑' I, idealTerm K (f.convolution g) s I =
      (∑' I, idealTerm K f s I) * ∑' I, idealTerm K g s I :=
  (hasSum_idealTerm_convolution hf.hasSum hg.hasSum).tsum_eq

/-- The ideal-indexed abscissa of absolute convergence of a convolution is at most the maximum
of the two original abscissae. This includes the values `⊥` and `⊤`. -/
theorem idealAbscissaOfAbsConv_convolution_le (f g : IdealArithmeticFunction K) :
    idealAbscissaOfAbsConv K (f.convolution g) ≤
      max (idealAbscissaOfAbsConv K f) (idealAbscissaOfAbsConv K g) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hf : Summable (idealTerm K f (x : ℂ)) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K
      (by simpa using (le_max_left ..).trans_lt hx)
  have hg : Summable (idealTerm K g (x : ℂ)) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K
      (by simpa using (le_max_right ..).trans_lt hx)
  simpa using idealAbscissaOfAbsConv_le K (summable_idealTerm_convolution hf hg)

/-! ### Norm-regrouped convolution series -/

/-- Ideal convolution preserves absolute convergence of the norm-regrouped Dirichlet series at
every common point of absolute convergence of its factors. -/
theorem LSeriesSummable_normCoeff_convolution {f g : IdealArithmeticFunction K} {s : ℂ}
    (hf : LSeriesSummable (normCoeff K f) s) (hg : LSeriesSummable (normCoeff K g) s) :
    LSeriesSummable (normCoeff K (f.convolution g)) s := by
  rw [normCoeff_convolution]
  exact ArithmeticFunction.LSeriesSummable_mul hf hg

/-- The norm-regrouped Dirichlet series of a convolution is the product of the two
norm-regrouped Dirichlet series wherever both converge absolutely. -/
theorem LSeries_normCoeff_convolution {f g : IdealArithmeticFunction K} {s : ℂ}
    (hf : LSeriesSummable (normCoeff K f) s) (hg : LSeriesSummable (normCoeff K g) s) :
    LSeries (normCoeff K (f.convolution g)) s =
      LSeries (normCoeff K f) s * LSeries (normCoeff K g) s := by
  rw [normCoeff_convolution, ArithmeticFunction.LSeries_mul' hf hg]

/-- The norm-regrouped abscissa of absolute convergence of a convolution is at most the maximum
of the two original norm-regrouped abscissae. -/
theorem abscissaOfAbsConv_normCoeff_convolution_le (f g : IdealArithmeticFunction K) :
    LSeries.abscissaOfAbsConv (normCoeff K (f.convolution g)) ≤
      max (LSeries.abscissaOfAbsConv (normCoeff K f))
        (LSeries.abscissaOfAbsConv (normCoeff K g)) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
  have hf : LSeriesSummable (normCoeff K f) y :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using (le_max_left ..).trans_lt hy)
  have hg : LSeriesSummable (normCoeff K g) y :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using (le_max_right ..).trans_lt hy)
  exact LSeriesSummable_normCoeff_convolution hf hg

/-- **Product identity on `Re s > 1`.** Whenever the regrouped `L`-series of `f` converges
absolutely at `s` with `1 < Re s`, the regrouped `L`-series of `1 * f` is `ζ_K(s) L(f, s)`. -/
theorem LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul {f : IdealArithmeticFunction K}
    {s : ℂ} (hs : 1 < s.re) (hf : LSeriesSummable (normCoeff K f) s) :
    LSeries (normCoeff K (IdealArithmeticFunction.convolution 1 f)) s =
      NumberField.dedekindZeta K s * LSeries (normCoeff K f) s := by
  rw [LSeries_normCoeff_convolution ((LSeriesSummable_normCoeff_one_iff K).mpr hs) hf,
    dedekindZeta_eq_LSeries_normCoeff_one]

/-- The Dirichlet series of `1 * f` converges absolutely on `Re s > 1` whenever `f` is uniformly
bounded on nonzero ideals. -/
theorem LSeriesSummable_normCoeff_convolution_one_of_bounded {f : IdealArithmeticFunction K} {C : ℝ}
    (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (normCoeff K (IdealArithmeticFunction.convolution 1 f)) s :=
  LSeriesSummable_normCoeff_convolution ((LSeriesSummable_normCoeff_one_iff K).mpr hs)
    (LSeriesSummable_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re hf hs))

/-- The abscissa of absolute convergence of `1 * f` is at most `1` whenever `f` is uniformly
bounded on nonzero ideals. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_le_one_of_bounded
    {f : IdealArithmeticFunction K} {C : ℝ} (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) :
    LSeries.abscissaOfAbsConv (normCoeff K (IdealArithmeticFunction.convolution 1 f)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy ↦
    LSeriesSummable_normCoeff_convolution_one_of_bounded hf (by simpa using hy)

end TauCeti
