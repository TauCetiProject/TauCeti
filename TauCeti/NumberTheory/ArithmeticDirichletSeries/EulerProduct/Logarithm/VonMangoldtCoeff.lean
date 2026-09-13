/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.PrimePowerIndex
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt

/-!
# The logarithmic derivative as a von Mangoldt Dirichlet series

Strictly to the right of the abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`,

the sum running over the nonzero integral ideals of `𝓞 K`, with `Λ` the ideal von Mangoldt
function. This is the coefficient identity: it names the exact Dirichlet coefficients of the
logarithmic derivative, which is what a Tauberian argument consumes.

The prime-power expansion of `logDeriv_LSeries_eq_tsum_prime_pow` is the same sum written over
`(𝔭, k)`. The two agree termwise, because the von Mangoldt transform of a completely multiplicative
weight at `𝔭 ^ (k+1)` is `χ(𝔭) ^ (k+1) log N(𝔭)` and `N(𝔭 ^ (k+1)) = N(𝔭) ^ (k+1)`; the transform
vanishes off the prime powers, so nothing else contributes.

## Main results

* `TauCeti.MultiplicativeIdealWeight.summable_idealTerm_vonMangoldtTransform`: the von Mangoldt
  weighted ideal terms are summable on the half-plane.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`: the
  coefficient identity itself.

## Implementation notes

Summability is comparison against `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`,
whose weight `log N(I)` dominates `‖Λ(I)‖` by `norm_vonMangoldt_le_log`. Passing from the
`(𝔭, k)`-indexed sum to the ideal-indexed one is
`TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti

namespace MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- The von Mangoldt weighted ideal term at `𝔭 ^ (k + 1)` is the `(𝔭, k)` summand of the
prime-power expansion of the logarithmic derivative. -/
private theorem idealTerm_vonMangoldtTransform_prime_pow (s : ℂ)
    (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s
        (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰)
      = Complex.log (Ideal.absNorm P.asIdeal : ℂ)
          * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (k + 1) := by
  have hmem : P.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hP : Prime (((⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰)) : Ideal (𝓞 K)) :=
    Ideal.prime_of_isPrime P.ne_bot P.isPrime
  have hpow : (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰)
      = (⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰) ^ (k + 1) := Subtype.ext (by simp)
  have hlog : Complex.log (Ideal.absNorm P.asIdeal : ℂ)
      = ((Real.log (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [idealTerm_def, hpow,
    MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos,
    SubmonoidClass.coe_pow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow, hlog, Nat.succ_eq_add_one]
  ring

/-- **The von Mangoldt weighted ideal terms converge absolutely.** Strictly to the right of the
abscissa of absolute convergence of `χ`, the terms `χ(A) Λ(A) / N(A) ^ s` are summable.

`Λ(A)` is bounded by `log N(A)`, and weighting the ideal terms by `log N(A)` preserves summability
strictly to the right of a point of absolute convergence. -/
theorem summable_idealTerm_vonMangoldtTransform {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, Summable (idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [idealAbscissaOfAbsConv_def, sInf_lt_iff] using hs
  have hlog := summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re
    (f := χ.toIdealArithmeticFunction) (s := (y : ℂ)) (s' := s)
    (h := by simpa using hys) (hs := hy)
  refine hlog.of_norm_bounded fun A ↦ ?_
  have hfac : ‖idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A‖
      = ‖(IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) A‖
        * ‖idealTerm K χ.toIdealArithmeticFunction s A‖ := by
    rw [idealTerm_def, idealTerm_def, IdealArithmeticFunction.vonMangoldtTransform_apply,
      norm_div, norm_div, norm_mul]
    ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_right
    (IdealArithmeticFunction.norm_vonMangoldt_le_log A) (norm_nonneg _)

/-- **The coefficient identity for the logarithmic derivative.** Strictly to the right of the
abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`.

The minus sign is the usual one: the Dirichlet coefficients of `-L'/L` are the von Mangoldt
transform of the weight, nonnegative when the weight is trivial. -/
theorem logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s
      = -∑' A : (Ideal (𝓞 K))⁰,
          idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A := by
  have hsum := χ.summable_idealTerm_vonMangoldtTransform hs
  have hsupp : Function.support (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s)
      ⊆ {A : (Ideal (𝓞 K))⁰ | IsPrimePow (A : Ideal (𝓞 K))} := by
    intro A hA
    rw [Function.mem_support, idealTerm_def, div_ne_zero_iff] at hA
    exact ((IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff _).mp hA.1).1
  have hinj : Function.Injective
      (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦ (idealPrimePowerOf pe.1 pe.2 : (Ideal (𝓞 K))⁰)) :=
    Subtype.coe_injective.comp idealPrimePowerEquiv.injective
  have key : ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
        * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1)
      = ∑' A : (Ideal (𝓞 K))⁰,
          idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A := by
    have hprod := (hsum.comp_injective hinj).tsum_prod
    simp only [Function.comp_apply] at hprod
    rw [tsum_eq_tsum_idealPrimePower_of_support_subset hsum hsupp, ← hprod]
    exact tsum_congr fun pe ↦ (idealTerm_vonMangoldtTransform_prime_pow χ s pe.1 pe.2).symm
  rw [χ.logDeriv_LSeries_eq_tsum_prime_pow hs, tsum_neg, key]

end MultiplicativeIdealWeight

end TauCeti
