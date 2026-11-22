/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Liouville
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Multiplicative
import TauCeti.NumberTheory.LSeries.Positivity

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

Both endpoints of the abscissa interval `[1 / 2, 1]` are sharp: the trivial weight `1` attains `1`,
and the ideal Liouville weight `TauCeti.MultiplicativeIdealWeight.liouville K` satisfies
`(1 * λ_K)(A) = 1` on square ideals and `0` elsewhere, giving `L(1 * λ_K, s) = ζ_K(2s)` with exact
abscissa `1 / 2`.

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
* `TauCeti.normCoeff_convolution_one_liouville_sq`,
  `TauCeti.normCoeff_convolution_one_liouville_of_notMem_range`,
  `TauCeti.LSeries_normCoeff_convolution_one_liouville`,
  `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_liouville`, and
  `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_one`: sharpness of both abscissa endpoints.

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

/-- Prime-power evaluation when `χ 𝔭 = -1`. -/
private theorem convolution_one_primeIdealPow_of_apply_eq_neg_one
    {χ : MultiplicativeIdealWeight K} {P : HeightOneSpectrum (𝓞 K)}
    (hP : χ P.asIdeal = -1) (n : ℕ) :
    IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) =
      if Even n then 1 else 0 := by
  rw [convolution_one_primeIdealPow, hP, neg_one_geom_sum]
  by_cases hn : Even n
  · simp [hn, Nat.not_even_iff_odd.mpr hn.add_one]
  · simp [hn, (Nat.not_even_iff_odd.mp hn).add_one]

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
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.2)
  have hmul :
      (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      χ.isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S e A hA]
  refine Finset.prod_nonneg fun P _ ↦ ?_
  have hP : (⟨P.asIdeal ^ e P, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (e P) P.ne_bot)⟩ :
      (Ideal (𝓞 K))⁰) = P.primeIdealPow (e P) :=
    Subtype.ext (HeightOneSpectrum.coe_primeIdealPow P (e P)).symm
  rw [hP]
  exact convolution_one_primeIdealPow_nonneg hχ P (e P)

/-- **Square lower bound for `1 * χ`.** If `χ ^ 2` is trivial on its good ideals, then
`1 ≤ (1 * χ)(A ^ 2)` for every nonzero integral ideal `A`. -/
theorem one_le_convolution_one_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (A : (Ideal (𝓞 K))⁰) :
    1 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (A ^ 2) := by
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.2)
  have hA2 : ((A ^ 2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = ∏ P ∈ S, P.asIdeal ^ (2 * e P) := by
    rw [SubmonoidClass.coe_pow, hA, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun P _ ↦ ?_
    rw [← pow_mul, mul_comm]
  have hmul :
      (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      χ.isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S (fun P ↦ 2 * e P) (A ^ 2) hA2]
  refine Finset.one_le_prod₀ fun P _ ↦ ?_
  have hP : (⟨P.asIdeal ^ (2 * e P), mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero (2 * e P) P.ne_bot)⟩ : (Ideal (𝓞 K))⁰) = P.primeIdealPow (2 * e P) :=
    Subtype.ext (HeightOneSpectrum.coe_primeIdealPow P (2 * e P)).symm
  rw [hP]
  exact one_le_convolution_one_primeIdealPow_two_mul hχ P (e P)

/-! ### Norm-coefficient positivity and square comparison -/

/-- Squaring is injective on nonzero integral ideals. -/
private theorem sq_injective_nonZeroDivisors :
    Function.Injective (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2) := fun _ _ h ↦
  Subtype.ext (pow_left_injective two_ne_zero
    (by simpa [SubmonoidClass.coe_pow] using congrArg Subtype.val h))

/-- A squared nonzero ideal lies in the norm-`m ^ 2` fibre iff the ideal lies in the norm-`m`
fibre. -/
private theorem sq_mem_normFiber_iff (A : (Ideal (𝓞 K))⁰) (m : ℕ) :
    A ^ 2 ∈ normFiber K (m ^ 2) ↔ A ∈ normFiber K m := by
  rw [mem_normFiber, mem_normFiber, SubmonoidClass.coe_pow, map_pow]
  exact ⟨fun h ↦ Nat.pow_left_injective two_ne_zero h, fun h ↦ congrArg (· ^ 2) h⟩

/-- The norm coefficients of the everywhere-one ideal function are nonnegative. -/
private theorem normCoeff_one_nonneg :
    0 ≤ (normCoeff K (1 : IdealArithmeticFunction K) : ℕ → ℂ) := fun n ↦ by
  rw [Pi.zero_apply, normCoeff_eq_sum_normFiber]
  exact Finset.sum_nonneg fun _ _ ↦ zero_le_one

/-- Order between nonnegative complex numbers implies order between their norms. -/
private theorem norm_le_norm_of_nonneg_le {a b : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ := by
  rw [Complex.eq_coe_norm_of_nonneg ha, Complex.eq_coe_norm_of_nonneg hb] at hab
  exact_mod_cast hab

/-- The norm coefficients of `1 * χ` are nonnegative whenever `χ ^ 2` is trivial on its good
ideals. -/
theorem normCoeff_convolution_one_nonneg {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) :
    0 ≤ (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction) : ℕ → ℂ) :=
  fun n ↦ by
    rw [Pi.zero_apply, normCoeff_eq_sum_normFiber]
    exact Finset.sum_nonneg fun A _ ↦ convolution_one_nonneg hχ A

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
    exact (sq_mem_normFiber_iff A m).mpr hA
  calc
    ∑ A ∈ normFiber K m, (1 : IdealArithmeticFunction K) A
      ≤ ∑ A ∈ normFiber K m,
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (A ^ 2) :=
        Finset.sum_le_sum fun A _ ↦ one_le_convolution_one_sq hχ A
    _ = ∑ B ∈ (normFiber K m).image (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2),
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction B :=
        (Finset.sum_image fun _ _ _ _ h ↦ sq_injective_nonZeroDivisors h).symm
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

/-- Complex power identity `((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s)`. -/
private theorem natCast_sq_cpow (m : ℕ) (s : ℂ) :
    ((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s) := by
  simpa [Nat.cast_pow] using (Complex.natCast_cpow_natCast_mul m 2 s).symm

/-- Termwise norm comparison between `ζ_K(2s)` and the square-indexed terms of `L(1 * χ, s)`. -/
private theorem norm_term_normCoeff_one_two_mul_le {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (s : ℂ) (m : ℕ) :
    ‖LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) m‖ ≤
      ‖LSeries.term (normCoeff K (IdealArithmeticFunction.convolution 1
        χ.toIdealArithmeticFunction)) s (m ^ 2)‖ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm2, norm_div, norm_div,
    natCast_sq_cpow]
  gcongr
  exact norm_le_norm_of_nonneg_le (normCoeff_one_nonneg m)
    (normCoeff_convolution_one_nonneg hχ (m ^ 2))
    (normCoeff_one_le_normCoeff_convolution_one_sq hχ m)

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
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg (normCoeff_one_nonneg (K := K)) (2 * σ),
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg (normCoeff_convolution_one_nonneg hχ) σ,
    Complex.real_le_real]
  refine (summable_norm_iff.mpr h1_sum).tsum_le_tsum_of_inj (fun m : ℕ ↦ m ^ 2)
    (Nat.pow_left_injective two_ne_zero) (fun _ _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (summable_norm_iff.mpr hσ)
  simpa [Complex.ofReal_mul] using norm_term_normCoeff_one_two_mul_le hχ σ m

/-! ### Sharpness witnesses: the ideal Liouville weight and the trivial weight -/

open Classical in
/-- **Ideal convolution with the Liouville weight detects square ideals.** For every nonzero
integral ideal `A`, `(1 * λ_K)(A)` equals `1` if `A` is the square of a nonzero ideal and `0`
otherwise. -/
theorem convolution_one_liouville_apply (A : (Ideal (𝓞 K))⁰) :
    IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction A =
      if ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 then 1 else 0 := by
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.2)
  have hmul : (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      (MultiplicativeIdealWeight.liouville K).isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S e A hA]
  have hprod :
      ∏ P ∈ S, IdealArithmeticFunction.convolution 1
          (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction
          ⟨P.asIdeal ^ e P, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (e P) P.ne_bot)⟩ =
        ∏ P ∈ S, (if Even (e P) then (1 : ℂ) else 0) := by
    refine Finset.prod_congr rfl fun P _ ↦ ?_
    have hP : (⟨P.asIdeal ^ e P, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (e P) P.ne_bot)⟩ :
        (Ideal (𝓞 K))⁰) = P.primeIdealPow (e P) :=
      Subtype.ext (HeightOneSpectrum.coe_primeIdealPow P (e P)).symm
    rw [hP]
    exact convolution_one_primeIdealPow_of_apply_eq_neg_one
      (MultiplicativeIdealWeight.liouville_prime K P) (e P)
  rw [hprod]
  by_cases hall : ∀ P ∈ S, Even (e P)
  · have hsq : ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 := by
      refine ⟨∏ P ∈ S, P.primeIdealPow (e P / 2), Subtype.ext ?_⟩
      rw [hA, SubmonoidClass.coe_pow, Submonoid.coe_finsetProd, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun P hP ↦ ?_
      rw [HeightOneSpectrum.coe_primeIdealPow, ← pow_mul,
        Nat.div_mul_cancel (even_iff_two_dvd.mp (hall P hP))]
    rw [ite_eq_left hsq]
    exact Finset.prod_eq_one fun P hP ↦ ite_eq_left (hall P hP)
  · push Not at hall
    obtain ⟨P, hPS, hPodd⟩ := hall
    have hnsq : ¬ ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 := by
      rintro ⟨B, rfl⟩
      exact hPodd (Ideal.even_of_sq_eq_prod_pow
        (by simpa [SubmonoidClass.coe_pow] using hA) hPS)
    rw [ite_eq_right hnsq]
    exact Finset.prod_eq_zero hPS (ite_eq_right hPodd)

open Classical in
/-- At a square index `m ^ 2`, the norm coefficient of `1 * λ_K` equals `normCoeff K 1 m`. -/
theorem normCoeff_convolution_one_liouville_sq (m : ℕ) :
    normCoeff K (IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction) (m ^ 2) =
      normCoeff K (1 : IdealArithmeticFunction K) m := by
  rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  simp_rw [convolution_one_liouville_apply]
  simp only [Finset.sum_boole, Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  symm
  refine Finset.card_bij (fun B _ ↦ B ^ 2) ?_ (fun _ _ _ _ h ↦ sq_injective_nonZeroDivisors h) ?_
  · intro B hB
    exact Finset.mem_filter.mpr ⟨(sq_mem_normFiber_iff B m).mpr hB, ⟨B, rfl⟩⟩
  · intro A hA
    obtain ⟨hAm, B, rfl⟩ := Finset.mem_filter.mp hA
    exact ⟨B, (sq_mem_normFiber_iff B m).mp hAm, rfl⟩

/-- Away from squares, the norm coefficients of `1 * λ_K` vanish. -/
theorem normCoeff_convolution_one_liouville_of_notMem_range {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ ↦ m ^ 2)) :
    normCoeff K (IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction) n = 0 := by
  classical
  rw [normCoeff_eq_sum_normFiber]
  refine Finset.sum_eq_zero fun A hA ↦ ?_
  rw [convolution_one_liouville_apply, ite_eq_right]
  rintro ⟨B, rfl⟩
  exact hn ⟨Ideal.absNorm (B : Ideal (𝓞 K)), by
    rw [← (mem_normFiber K).mp hA, SubmonoidClass.coe_pow, map_pow]⟩

/-- On a square index `m ^ 2`, the Dirichlet term of `1 * λ_K` at `s` equals the `m`-th term of
`ζ_K` at `2s`. -/
private theorem term_normCoeff_convolution_one_liouville_sq (s : ℂ) (m : ℕ) :
    LSeries.term (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s (m ^ 2) =
      LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hm0), LSeries.term_of_ne_zero hm0,
    normCoeff_convolution_one_liouville_sq, natCast_sq_cpow]

/-- Away from squares, the Dirichlet term of `1 * λ_K` vanishes. -/
private theorem term_normCoeff_convolution_one_liouville_eq_zero_of_notMem_range (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ ↦ m ^ 2)) :
    LSeries.term (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rw [LSeries.term_of_ne_zero hn0, normCoeff_convolution_one_liouville_of_notMem_range hn, zero_div]

/-- **Exact `L`-series identity for `1 * λ_K`.** For every `s : ℂ`,
`L(1 * λ_K, s) = ζ_K(2s)`. -/
theorem LSeries_normCoeff_convolution_one_liouville (s : ℂ) :
    LSeries (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s =
      dedekindZeta K (2 * s) := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, LSeries, LSeries,
    ← tsum_congr (term_normCoeff_convolution_one_liouville_sq (K := K) s)]
  refine (Function.Injective.tsum_eq (Nat.pow_left_injective two_ne_zero) ?_).symm
  intro n hn
  by_contra hnot
  exact hn (term_normCoeff_convolution_one_liouville_eq_zero_of_notMem_range s hnot)

/-- The Dirichlet series of `1 * λ_K` converges absolutely exactly on `Re s > 1 / 2`. -/
theorem LSeriesSummable_normCoeff_convolution_one_liouville_iff {s : ℂ} :
    LSeriesSummable (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s ↔ 1 / 2 < s.re := by
  rw [LSeriesSummable, ← (Nat.pow_left_injective two_ne_zero).summable_iff
    (fun n hn ↦ term_normCoeff_convolution_one_liouville_eq_zero_of_notMem_range s hn)]
  simp_rw [Function.comp_def, term_normCoeff_convolution_one_liouville_sq]
  rw [← LSeriesSummable, LSeriesSummable_normCoeff_one_iff]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  constructor <;> intro h <;> linarith

/-- **Sharpness of the lower bound `1 / 2`.** The ideal Liouville weight satisfies
`((liouville K) ^ 2).IsTrivialOnGood` and its convolution `1 * λ_K` has exact abscissa of absolute
convergence `1 / 2`. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_liouville :
    LSeries.abscissaOfAbsConv (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) =
        ((1 / 2 : ℝ) : EReal) := by
  refine le_antisymm ?_
    (half_le_abscissaOfAbsConv_normCoeff_convolution_one
      (MultiplicativeIdealWeight.isTrivialOnGood_liouville_sq K))
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy ↦
    (LSeriesSummable_normCoeff_convolution_one_liouville_iff (K := K)).mpr (by simpa using hy)

/-- **Sharpness of the upper bound `1`.** The trivial weight `1` satisfies `(1 ^ 2).IsTrivialOnGood`
and its convolution `1 * 1` (the ideal divisor function) has exact abscissa of absolute convergence
`1`. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_one :
    LSeries.abscissaOfAbsConv (normCoeff K (IdealArithmeticFunction.convolution 1
      (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction)) = 1 := by
  have h1sq : ((1 : MultiplicativeIdealWeight K) ^ 2).IsTrivialOnGood := by
    rw [one_pow]; exact MultiplicativeIdealWeight.isTrivialOnGood_one
  refine le_antisymm (abscissaOfAbsConv_normCoeff_convolution_one_le_one h1sq) ?_
  by_contra hlt
  have hsum : LSeriesSummable (normCoeff K (IdealArithmeticFunction.convolution 1
      (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction)) 1 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using not_le.mp hlt)
  apply not_LSeriesSummable_normCoeff_one K
  rw [LSeriesSummable, ← summable_norm_iff] at hsum ⊢
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  refine LSeries.norm_term_le 1 (norm_le_norm_of_nonneg_le (normCoeff_one_nonneg n)
    (normCoeff_convolution_one_nonneg h1sq n) ?_)
  rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  refine Finset.sum_le_sum fun A _ ↦ ?_
  rw [Pi.one_apply, MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    IdealArithmeticFunction.convolution_one_one_apply]
  exact_mod_cast (Finset.one_le_card.mpr ⟨(1, A), by simp⟩ :
    1 ≤ (Ideal.divisorsAntidiagonal A).card)

end TauCeti
