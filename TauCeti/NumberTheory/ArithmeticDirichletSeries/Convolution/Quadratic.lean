/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import Mathlib.Algebra.GroupWithZero.Torsion
import TauCeti.Algebra.Group.Submonoid.Operations
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Multiplicative
import TauCeti.NumberTheory.LSeries.Positivity
import TauCeti.NumberTheory.LSeries.Term

/-!
# Ideal convolution positivity for quadratic ideal weights

Let `K` be a number field and `χ : TauCeti.MultiplicativeIdealWeight K` a completely multiplicative
ideal weight whose pointwise square `χ ^ 2` is trivial on its good ideals, meaning
`χ I ∈ {0, 1, -1}` for every integral ideal `I`. This file establishes the arithmetic positivity
properties of the Dirichlet convolution `1 * χ`, whose Dirichlet series on `Re s > 1` is the
product `ζ_K(s) L(χ, s)`:

* at every prime power `𝔭 ^ n`, the convolution evaluates to `∑_{i=0}^n χ(𝔭)^i`, which is `1` when
  `χ(𝔭) = 0`, `n + 1` when `χ(𝔭) = 1`, and `1` or `0` according to the parity of `n` when
  `χ(𝔭) = -1`;
* by multiplicativity, `(1 * χ)(A) ≥ 0` for every nonzero integral ideal `A`, and `(1 * χ)(A²) ≥ 1`
  for every square ideal `A²`;
* regrouping by absolute norm preserves nonnegativity (`0 ≤ ⇑(normCoeff K (1 * χ))`) and yields the
  square comparison `normCoeff K 1 m ≤ normCoeff K (1 * χ) (m ^ 2)`, using injectivity of squaring
  on integral ideals (`HasUniqueRoots (Ideal (𝓞 K))`, i.e. `pow_left_injective`);
* consequently, absolute convergence of `L(1 * χ, s)` implies absolute convergence of `ζ_K(2s)`, so
  `L(1 * χ, s)` does not converge absolutely anywhere in `Re s ≤ 1 / 2`, its abscissa of absolute
  convergence lies in `[1 / 2, 1]`, and on the real half-line of convergence
  `ζ_K(2σ) ≤ L(1 * χ, σ)`.

Both endpoints of the abscissa interval `[1 / 2, 1]` are sharp: the trivial weight `1` attains `1`
(`TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_one` in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution/Analytic.lean`), and the ideal Liouville
weight `TauCeti.MultiplicativeIdealWeight.liouville K` attains `1 / 2` (see
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution/Liouville.lean`).

## Main results

* `TauCeti.convolution_one_nonneg`, `TauCeti.one_le_convolution_one_sq`,
  `TauCeti.normCoeff_convolution_one_nonneg`,
  `TauCeti.normCoeff_one_le_normCoeff_convolution_one_sq`: nonnegativity and square lower bounds
  for `1 * χ`.
* `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_le_one`,
  `TauCeti.LSeriesSummable_normCoeff_one_two_mul_of_LSeriesSummable_normCoeff_convolution_one`,
  `TauCeti.not_LSeriesSummable_normCoeff_convolution_one_of_re_le_half`,
  `TauCeti.half_le_abscissaOfAbsConv_normCoeff_convolution_one`,
  `TauCeti.dedekindZeta_two_mul_le_LSeries_convolution_one`: summability transfer, failure of
  absolute convergence on `Re s ≤ 1 / 2`, abscissa bounds in `[1 / 2, 1]`, and the real-line
  comparison with `ζ_K(2σ)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* The Dirichlet-character prototype is Mathlib's `zetaMul` positivity in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

namespace TauCeti

open Complex IsDedekindDomain NumberField
open scoped ComplexOrder nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Prime-power values and ideal-level positivity of `1 * χ` -/

/-- Three-case evaluation of `(1 * χ)(𝔭 ^ n)` when `(χ ^ 2).IsTrivialOnGood`. -/
private theorem convolution_one_primeIdealPow_cases {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) = 1) ∨
    (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) =
      (n + 1 : ℂ)) ∨
    (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) =
      if Even n then 1 else 0) := by
  rcases χ.apply_eq_zero_or_one_or_neg_one_of_isTrivialOnGood_sq hχ P.asIdeal with h | h | h
  · left
    rw [convolution_one_primeIdealPow, h, Finset.sum_range_succ']
    simp
  · right; left
    rw [convolution_one_primeIdealPow, h]
    simp
  · right; right
    exact convolution_one_primeIdealPow_of_apply_eq_neg_one h n

/-- At a prime power, `1 * χ` is nonnegative whenever `χ ^ 2` is trivial on its good ideals. -/
private theorem convolution_one_primeIdealPow_nonneg {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    0 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) := by
  rcases convolution_one_primeIdealPow_cases hχ P n with h | h | h <;> rw [h]
  · exact zero_le_one
  · exact_mod_cast Nat.zero_le (n + 1)
  · split_ifs <;> norm_num

/-- At an even prime power, `1 * χ` is at least `1` whenever `χ ^ 2` is trivial on its good
ideals. -/
private theorem one_le_convolution_one_primeIdealPow_two_mul {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    1 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction
      (P.primeIdealPow (2 * k)) := by
  rcases convolution_one_primeIdealPow_cases hχ P (2 * k) with h | h | h
  · rw [h]
  · rw [h]
    simp [Complex.le_def]
  · rw [h]
    simp [even_two_mul k]

/-- **Nonnegativity of `1 * χ` on all nonzero integral ideals.** If `χ ^ 2` is trivial on its good
ideals, then `(1 * χ)(A) ≥ 0` (as a nonnegative real number in `ℂ`) for every nonzero ideal `A`. -/
theorem convolution_one_nonneg {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (A : (Ideal (𝓞 K))⁰) :
    0 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction A := by
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.property)
  have hmul :
      (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      χ.isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S e A hA]
  exact Finset.prod_nonneg fun P _ ↦ convolution_one_primeIdealPow_nonneg hχ P (e P)

/-- **Square lower bound for `1 * χ`.** If `χ ^ 2` is trivial on its good ideals, then
`1 ≤ (1 * χ)(A ^ 2)` for every nonzero integral ideal `A`. -/
theorem one_le_convolution_one_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (A : (Ideal (𝓞 K))⁰) :
    1 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (A ^ 2) := by
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.property)
  have hA2 : ((A ^ 2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = ∏ P ∈ S, P.asIdeal ^ (2 * e P) := by
    rw [SubmonoidClass.coe_pow, hA, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun P _ ↦ ?_
    rw [← pow_mul, mul_comm]
  have hmul :
      (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      χ.isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S (fun P ↦ 2 * e P) (A ^ 2) hA2]
  exact Finset.one_le_prod₀ fun P _ ↦ one_le_convolution_one_primeIdealPow_two_mul hχ P (e P)

/-! ### Norm-coefficient positivity and square comparison -/

/-- The norm coefficients of `1 * χ` are nonnegative whenever `χ ^ 2` is trivial on its good
ideals. -/
theorem normCoeff_convolution_one_nonneg {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) :
    0 ≤ (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction) : ℕ → ℂ) :=
  normCoeff_nonneg K (convolution_one_nonneg hχ)

/-- **Norm-coefficient square comparison.** For every `m : ℕ`, the number of ideals of norm `m` is
bounded above by the `(m ^ 2)`-th norm coefficient of `1 * χ`, because squaring injects the norm-`m`
fibre into the norm-`m²` fibre and `(1 * χ)(A²) ≥ 1`. -/
theorem normCoeff_one_le_normCoeff_convolution_one_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (m : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) m ≤
      normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction) (m ^ 2) := by
  classical
  rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  have hsub : (normFiber K m).image (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2) ⊆ normFiber K (m ^ 2) := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    exact (sq_mem_normFiber_iff K A m).mpr hA
  calc
    ∑ A ∈ normFiber K m, (1 : IdealArithmeticFunction K) A
      ≤ ∑ A ∈ normFiber K m,
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (A ^ 2) :=
        Finset.sum_le_sum fun A _ ↦ one_le_convolution_one_sq hχ A
    _ = ∑ B ∈ (normFiber K m).image (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2),
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction B :=
        (Finset.sum_image fun _ _ _ _ h ↦ pow_left_injective two_ne_zero h).symm
    _ ≤ ∑ B ∈ normFiber K (m ^ 2),
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction B :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun B _ _ ↦ convolution_one_nonneg hχ B

/-! ### Failure of absolute convergence on `Re s ≤ 1 / 2`, abscissa bounds, and real comparison -/

/-- The abscissa of absolute convergence of `1 * χ` is at most `1` whenever `χ ^ 2` is trivial on
its good ideals. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_le_one {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) :
    LSeries.abscissaOfAbsConv
        (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) ≤ 1 :=
  abscissaOfAbsConv_normCoeff_convolution_one_le_one_of_bounded (C := 1) fun I ↦ by
    simpa using χ.norm_apply_le_one_of_isTrivialOnGood_sq hχ (I : Ideal (𝓞 K))

/-- Termwise norm comparison between `ζ_K(2s)` and the square-indexed terms of `L(1 * χ, s)`. -/
private theorem norm_term_normCoeff_one_two_mul_le {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (s : ℂ) (m : ℕ) :
    ‖LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) m‖ ≤
      ‖LSeries.term (normCoeff K (IdealArithmeticFunction.convolution 1
        χ.toIdealArithmeticFunction)) s (m ^ 2)‖ := by
  rw [TauCeti.LSeries.term_sq]
  refine LSeries.norm_term_le (2 * s) ?_
  have h0 : 0 ≤ normCoeff K (1 : IdealArithmeticFunction K) m := normCoeff_one_nonneg K m
  have hle := normCoeff_one_le_normCoeff_convolution_one_sq hχ m
  have h1 := h0.trans hle
  rw [Complex.eq_coe_norm_of_nonneg h0, Complex.eq_coe_norm_of_nonneg h1,
    Complex.real_le_real] at hle
  exact hle

/-- **Summability transfer from `L(1 * χ, s)` to `ζ_K(2s)`.** If `χ ^ 2` is trivial on its good
ideals and `L(1 * χ, s)` converges absolutely at `s`, then `ζ_K(2s)` converges absolutely. -/
theorem LSeriesSummable_normCoeff_one_two_mul_of_LSeriesSummable_normCoeff_convolution_one
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {s : ℂ}
    (hs : LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) s) :
    LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) := by
  rw [LSeriesSummable, ← summable_norm_iff] at hs ⊢
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_term_normCoeff_one_two_mul_le hχ s)
    (hs.comp_injective (Nat.pow_left_injective two_ne_zero))

/-- **Failure of absolute convergence of `L(1 * χ, s)` on `Re s ≤ 1 / 2`.** If `χ ^ 2` is trivial
on its good ideals, then the Dirichlet series of `1 * χ` does not converge absolutely anywhere in
`Re s ≤ 1 / 2`. -/
theorem not_LSeriesSummable_normCoeff_convolution_one_of_re_le_half
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {s : ℂ}
    (hs : s.re ≤ 1 / 2) :
    ¬ LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) s := by
  intro hsum
  have h1 := (LSeriesSummable_normCoeff_one_iff K).mp
    (LSeriesSummable_normCoeff_one_two_mul_of_LSeriesSummable_normCoeff_convolution_one hχ hsum)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h1
  linarith

/-- **Lower bound on the abscissa of `1 * χ`.** If `χ ^ 2` is trivial on its good ideals, then the
abscissa of absolute convergence of `1 * χ` is at least `1 / 2`. -/
theorem half_le_abscissaOfAbsConv_normCoeff_convolution_one {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) :
    ((1 / 2 : ℝ) : EReal) ≤ LSeries.abscissaOfAbsConv
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) := by
  by_contra h
  exact not_LSeriesSummable_normCoeff_convolution_one_of_re_le_half hχ
    (s := ((1 / 2 : ℝ) : ℂ)) (by simp)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using not_le.mp h))

/-- **Real-line lower bound by `ζ_K(2σ)`.** At every real point `σ` where `L(1 * χ, σ)` converges
absolutely, `ζ_K(2σ) ≤ L(1 * χ, σ)` in `ComplexOrder` (in particular
`(ζ_K(2σ)).re ≤ (L(1 * χ, σ)).re`). -/
theorem dedekindZeta_two_mul_le_LSeries_convolution_one {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {σ : ℝ}
    (hσ : LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) σ) :
    dedekindZeta K ((2 * σ : ℝ) : ℂ) ≤
      LSeries
        (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) σ := by
  have h1_sum :
      LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) ((2 * σ : ℝ) : ℂ) := by
    simpa [Complex.ofReal_mul] using
      LSeriesSummable_normCoeff_one_two_mul_of_LSeriesSummable_normCoeff_convolution_one hχ hσ
  rw [dedekindZeta_eq_LSeries_normCoeff_one,
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg (normCoeff_one_nonneg K) (2 * σ),
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg (normCoeff_convolution_one_nonneg hχ) σ,
    Complex.real_le_real]
  refine (summable_norm_iff.mpr h1_sum).tsum_le_tsum_of_inj (fun m : ℕ ↦ m ^ 2)
    (Nat.pow_left_injective two_ne_zero) (fun _ _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (summable_norm_iff.mpr hσ)
  simpa [Complex.ofReal_mul] using norm_term_normCoeff_one_two_mul_le hχ σ m

end TauCeti
