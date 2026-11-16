/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Multiplicative
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Convolution.Basic
import TauCeti.NumberTheory.LSeries.Positivity
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Ideal convolution positivity for quadratic ideal weights

Let `K` be a number field and `χ : TauCeti.MultiplicativeIdealWeight K` a completely multiplicative
ideal weight whose pointwise square `χ ^ 2` is trivial on its good ideals, meaning
`χ I ∈ {0, 1, -1}` for every integral ideal `I`. This file establishes the arithmetic positivity
properties of the Dirichlet convolution `1 * χ`
whose Dirichlet series on `Re s > 1` is the product `ζ_K(s) L(χ, s)`:

* at every prime power `𝔭 ^ n`, the convolution evaluates to `∑_{i=0}^n χ(𝔭)^i`, which is `1` when
  `χ(𝔭) = 0`, `n + 1` when `χ(𝔭) = 1`, and `1` or `0` according to the parity of `n` when
  `χ(𝔭) = -1`;
* by multiplicativity, `(1 * χ)(A) ≥ 0` for every nonzero integral ideal `A`, and `(1 * χ)(A²) ≥ 1`
  for every square ideal `A²`;
* regrouping by absolute norm preserves nonnegativity (`0 ≤ ⇑(normCoeff K (1 * χ))`) and yields the
  square comparison `normCoeff K 1 m ≤ normCoeff K (1 * χ) (m ^ 2)`, using injectivity of squaring
  on integral ideals (`HasUniqueRoots (Ideal (𝓞 K))`, i.e. `pow_left_injective`);
* consequently, absolute convergence of `L(1 * χ, s)` implies absolute convergence of `ζ_K(2s)`, so
  `L(1 * χ, s)` diverges for `Re s ≤ 1 / 2`, its abscissa of absolute convergence lies in
  `[1 / 2, 1]`, and on the real half-line of convergence `ζ_K(2σ) ≤ L(1 * χ, σ)`.

More generally, if `χ ^ 2` is a purely imaginary norm twist with parameter `u` on its good ideals
(`(χ ^ 2).IsNormTwistOnGood u`), twisting `χ` by `N(I) ^ (-(u / 2) * I)` reduces to the case
`(χ' ^ 2).IsTrivialOnGood`, and `χ` is automatically unitary.

Both endpoints of the abscissa interval `[1 / 2, 1]` are sharp: the trivial weight `1` attains `1`,
and the **ideal Liouville weight** `MultiplicativeIdealWeight.liouville K`, taking value `-1` at
every height-one prime, satisfies `(1 * λ_K)(A) = 1` on square ideals and `0` elsewhere, giving
`L(1 * λ_K, s) = ζ_K(2s)` with exact abscissa `1 / 2`.

## Main definitions

* `TauCeti.MultiplicativeIdealWeight.liouville`: the ideal Liouville weight `I ↦ (-1) ^ Ω(I)` on
  nonzero ideals of `𝓞 K`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.isTrivialOnGood_sq_iff`,
  `TauCeti.MultiplicativeIdealWeight.isTrivialOnGood_sq_normTwist_of_isNormTwistOnGood_sq`,
  `TauCeti.MultiplicativeIdealWeight.norm_apply_eq_one_of_isNormTwistOnGood_sq`: structure and
  unitarity of weights whose square is trivial or a norm twist on good ideals.
* `TauCeti.convolution_one_nonneg`, `TauCeti.one_le_convolution_one_sq`,
  `TauCeti.normCoeff_convolution_one_nonneg`,
  `TauCeti.normCoeff_one_le_normCoeff_convolution_one_sq`: nonnegativity and square lower bounds
  for `1 * χ`.
* `TauCeti.LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul`: product identity
  `L(1 * f, s) = ζ_K(s) L(f, s)` for any ideal arithmetic function whose regrouped `L`-series
  converges absolutely at `s` with `Re s > 1`.
* `TauCeti.not_LSeriesSummable_normCoeff_convolution_one_of_re_le_half`,
  `TauCeti.half_le_abscissaOfAbsConv_normCoeff_convolution_one`,
  `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_le_one`,
  `TauCeti.dedekindZeta_two_mul_le_LSeries_convolution_one`: divergence at `1 / 2`, abscissa bounds
  in `[1 / 2, 1]`, and the real-line comparison with `ζ_K(2σ)`.
* `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_liouville` and
  `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_one`: sharpness of both endpoints.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* The Dirichlet-character prototype is Mathlib's `zetaMul` positivity in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll and David Loeffler).
-/

public section

namespace TauCeti

open Complex IsDedekindDomain NumberField
open scoped ComplexOrder nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Quadratic and norm-twisted-square ideal weights -/

namespace MultiplicativeIdealWeight

/-- A weight has pointwise square trivial on its good ideals exactly when it takes values in
`{1, -1}` on its good ideals. -/
theorem isTrivialOnGood_sq_iff {χ : MultiplicativeIdealWeight K} :
    (χ ^ 2).IsTrivialOnGood ↔ ∀ I : Ideal (𝓞 K), χ.IsGood I → χ I = 1 ∨ χ I = -1 := by
  constructor
  · intro h I hI
    have hI2 : (χ ^ 2).IsGood I := by simpa [IsGood, badPrimes_pow _ two_ne_zero] using hI
    have h1 : (χ ^ 2) I = 1 := h.apply_eq_one hI2
    rwa [pow_apply _ two_ne_zero, sq_eq_one_iff] at h1
  · intro h
    have heq : χ ^ 2 = ofBadPrimes χ.badPrimes χ.finite_badPrimes := by
      ext I
      rw [pow_apply _ two_ne_zero, ofBadPrimes_apply]
      by_cases hI : χ.IsGood I
      · have hI' : I.IsPrimeTo χ.badPrimes := hI
        rw [ite_eq_left hI', sq_eq_one_iff]
        exact h I hI
      · have hI' : ¬ I.IsPrimeTo χ.badPrimes := hI
        rw [(χ.apply_eq_zero_iff_not_isGood I).mpr hI, zero_pow two_ne_zero, ite_eq_right hI']
    rw [heq]
    exact isTrivialOnGood_ofBadPrimes χ.finite_badPrimes

/-- A weight has pointwise square trivial on its good ideals exactly when every good height-one
prime takes value `1` or `-1`. -/
theorem isTrivialOnGood_sq_iff_prime {χ : MultiplicativeIdealWeight K} :
    (χ ^ 2).IsTrivialOnGood ↔
      ∀ P : HeightOneSpectrum (𝓞 K), P ∉ χ.badPrimes → χ P.asIdeal = 1 ∨ χ P.asIdeal = -1 := by
  rw [isTrivialOnGood_sq_iff]
  refine ⟨fun h P hP ↦ h P.asIdeal (Ideal.isPrimeTo_asIdeal_iff.mpr hP), fun h I hI ↦ ?_⟩
  refine hI.induction_on (Or.inl χ.apply_top) fun P J hP _ ih ↦ ?_
  rw [_root_.map_mul]
  rcases h P hP with hP1 | hP1 <;> rcases ih with hJ1 | hJ1 <;> simp [hP1, hJ1]

/-- A weight whose pointwise square is trivial on its good ideals takes every ideal to `0`, `1`,
or `-1`. -/
theorem apply_eq_zero_or_one_or_neg_one_of_isTrivialOnGood_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (I : Ideal (𝓞 K)) :
    χ I = 0 ∨ χ I = 1 ∨ χ I = -1 := by
  by_cases hI : χ.IsGood I
  · exact Or.inr (isTrivialOnGood_sq_iff.mp hχ I hI)
  · exact Or.inl ((χ.apply_eq_zero_iff_not_isGood I).mpr hI)

/-- **Untwisting a norm-twisted-square weight.** If `χ ^ 2` agrees with `I ↦ N(I) ^ (u * I)` on
its good ideals, then twisting `χ` by `N(I) ^ (-(u / 2) * I)` produces a weight whose square is
trivial on its good ideals. -/
theorem isTrivialOnGood_sq_normTwist_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K}
    {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) :
    (normTwist (((u / 2 : ℝ) : ℂ) * Complex.I) χ ^ 2).IsTrivialOnGood := by
  rw [normTwist_pow, ← isNormTwistOnGood_zero_iff]
  have hcast : ((2 : ℕ) : ℂ) * (((u / 2 : ℝ) : ℂ) * Complex.I) =
      -(((-u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hcast]
  simpa using hχ.normTwist (-u)

/-- A weight whose square is a purely imaginary norm twist on its good ideals has modulus `1` on
every good ideal. -/
theorem norm_apply_eq_one_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) {I : Ideal (𝓞 K)} (hI : χ.IsGood I) : ‖χ I‖ = 1 := by
  have hI' : I.IsPrimeTo χ.badPrimes := hI
  have hN : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_bot)
  have hval : (χ ^ 2) I = (Ideal.absNorm I : ℂ) ^ ((u : ℂ) * Complex.I) := by
    have heq := congrArg (fun w : MultiplicativeIdealWeight K ↦ w I) (hχ.eq_normTwist rfl)
    simpa [normTwist_apply, ofBadPrimes_apply, hI', badPrimes_pow _ two_ne_zero] using heq
  have hsq : ‖χ I‖ ^ 2 = 1 := by
    rw [← norm_pow, ← pow_apply _ two_ne_zero, hval, Complex.norm_natCast_cpow_of_pos hN]
    simp
  nlinarith [norm_nonneg (χ I)]

/-- A weight whose square is a purely imaginary norm twist on its good ideals is bounded in modulus
by `1` on every ideal. -/
theorem norm_apply_le_one_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) (I : Ideal (𝓞 K)) : ‖χ I‖ ≤ 1 := by
  by_cases hI : χ.IsGood I
  · exact (norm_apply_eq_one_of_isNormTwistOnGood_sq hχ hI).le
  · rw [(χ.apply_eq_zero_iff_not_isGood I).mpr hI, norm_zero]
    exact zero_le_one

/-- A weight whose square is trivial on its good ideals is bounded in modulus by `1` on every
ideal. -/
theorem norm_apply_le_one_of_isTrivialOnGood_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (I : Ideal (𝓞 K)) : ‖χ I‖ ≤ 1 :=
  norm_apply_le_one_of_isNormTwistOnGood_sq ((isNormTwistOnGood_zero_iff _).mpr hχ) I

end MultiplicativeIdealWeight

/-! ### Prime-power values and ideal-level positivity of `1 * χ` -/

/-- At a prime power `𝔭 ^ n`, convolving the everywhere-one function with a completely
multiplicative ideal weight gives the geometric sum `∑ i ∈ Finset.range (n + 1), χ 𝔭 ^ i`. -/
theorem convolution_one_primeIdealPow (χ : MultiplicativeIdealWeight K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) =
      ∑ i ∈ Finset.range (n + 1), χ P.asIdeal ^ i := by
  rw [IdealArithmeticFunction.convolution_primeIdealPow]
  simp only [Pi.one_apply, one_mul, MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
    HeightOneSpectrum.coe_primeIdealPow, map_pow]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ j ↦ χ P.asIdeal ^ j)]
  exact Finset.sum_range_reflect (fun j ↦ χ P.asIdeal ^ j) (n + 1)

/-- At a prime power, `1 * χ` is nonnegative whenever `χ ^ 2` is trivial on its good ideals. -/
private theorem convolution_one_primeIdealPow_nonneg {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    0 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (P.primeIdealPow n) := by
  rw [convolution_one_primeIdealPow]
  rcases χ.apply_eq_zero_or_one_or_neg_one_of_isTrivialOnGood_sq hχ P.asIdeal with h | h | h
  · rw [h, Finset.sum_range_succ']
    simp
  · rw [h]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact Nat.cast_nonneg _
  · rw [h, neg_one_geom_sum]
    split_ifs <;> norm_num

/-- At an even prime power, `1 * χ` is at least `1` whenever `χ ^ 2` is trivial on its good
ideals. -/
private theorem one_le_convolution_one_primeIdealPow_two_mul {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    1 ≤ IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction
      (P.primeIdealPow (2 * k)) := by
  rw [convolution_one_primeIdealPow]
  rcases χ.apply_eq_zero_or_one_or_neg_one_of_isTrivialOnGood_sq hχ P.asIdeal with h | h | h
  · rw [h, Finset.sum_range_succ']
    simp
  · rw [h]
    simp [Complex.le_def]
  · rw [h, neg_one_geom_sum]
    have hodd : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, rfl⟩
    simp [hodd]

omit [NumberField K] in
/-- The nonzero ideal subtype built from `P.asIdeal ^ n` coincides with `P.primeIdealPow n`. -/
private theorem mk_primeIdealPow_eq (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩ : (Ideal (𝓞 K))⁰) =
      P.primeIdealPow n :=
  Subtype.ext (HeightOneSpectrum.coe_primeIdealPow P n).symm

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
  exact Finset.prod_nonneg fun P _ ↦ by
    rw [mk_primeIdealPow_eq]
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
  exact Finset.one_le_prod₀ fun P _ ↦ by
    rw [mk_primeIdealPow_eq]
    exact one_le_convolution_one_primeIdealPow_two_mul hχ P (e P)

/-! ### Norm-coefficient positivity and square comparison -/

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
  have hinj : Function.Injective (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2) := fun A B hAB ↦
    Subtype.ext (pow_left_injective two_ne_zero (by simpa using congrArg Subtype.val hAB))
  have hsub : (normFiber K m).image (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2) ⊆ normFiber K (m ^ 2) := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    rw [mem_normFiber] at hA ⊢
    rw [SubmonoidClass.coe_pow, map_pow, hA]
  calc
    ∑ A ∈ normFiber K m, (1 : IdealArithmeticFunction K) A
      ≤ ∑ A ∈ normFiber K m,
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction (A ^ 2) :=
        Finset.sum_le_sum fun A _ ↦ one_le_convolution_one_sq hχ A
    _ = ∑ B ∈ (normFiber K m).image (fun A : (Ideal (𝓞 K))⁰ ↦ A ^ 2),
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction B :=
        (Finset.sum_image fun _ _ _ _ h ↦ hinj h).symm
    _ ≤ ∑ B ∈ normFiber K (m ^ 2),
          IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction B :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun B _ _ ↦ convolution_one_nonneg hχ B

/-! ### Dirichlet series, divergence at `1 / 2`, abscissa bounds, and real comparison -/

/-- **Product identity on `Re s > 1`.** Whenever the regrouped `L`-series of `f` converges
absolutely at `s` with `1 < Re s`, the regrouped `L`-series of `1 * f` is `ζ_K(s) L(f, s)`. -/
theorem LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul {f : IdealArithmeticFunction K}
    {s : ℂ} (hs : 1 < s.re) (hf : LSeriesSummable (normCoeff K f) s) :
    LSeries (normCoeff K (IdealArithmeticFunction.convolution 1 f)) s =
      dedekindZeta K s * LSeries (normCoeff K f) s := by
  rw [normCoeff_convolution,
    ArithmeticFunction.LSeries_mul' ((LSeriesSummable_normCoeff_one_iff K).mpr hs) hf,
    dedekindZeta_eq_LSeries_normCoeff_one]

/-- The Dirichlet series of `1 * f` converges absolutely on `Re s > 1` whenever `f` is uniformly
bounded on nonzero ideals. -/
theorem LSeriesSummable_normCoeff_convolution_one_of_bounded {f : IdealArithmeticFunction K} {C : ℝ}
    (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (normCoeff K (IdealArithmeticFunction.convolution 1 f)) s := by
  rw [normCoeff_convolution]
  exact ArithmeticFunction.LSeriesSummable_mul ((LSeriesSummable_normCoeff_one_iff K).mpr hs)
    (LSeriesSummable_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re hf hs))

/-- The abscissa of absolute convergence of `1 * f` is at most `1` whenever `f` is uniformly
bounded on nonzero ideals. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_le_one_of_bounded
    {f : IdealArithmeticFunction K} {C : ℝ} (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) :
    LSeries.abscissaOfAbsConv (normCoeff K (IdealArithmeticFunction.convolution 1 f)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy ↦
    LSeriesSummable_normCoeff_convolution_one_of_bounded hf (by simpa using hy)

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
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm2, norm_div, norm_div]
  have hden : ‖((m ^ 2 : ℕ) : ℂ) ^ s‖ = ‖(m : ℂ) ^ (2 * s)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm2),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm), Nat.cast_pow,
      ← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg m)]
    simp
  rw [hden]
  gcongr
  have h1 : 0 ≤ normCoeff K (1 : IdealArithmeticFunction K) m := by
    rw [normCoeff_eq_sum_normFiber]
    exact Finset.sum_nonneg fun _ _ ↦ zero_le_one
  have hle := normCoeff_one_le_normCoeff_convolution_one_sq hχ m
  have h2 : 0 ≤ normCoeff K (IdealArithmeticFunction.convolution 1
      χ.toIdealArithmeticFunction) (m ^ 2) := normCoeff_convolution_one_nonneg hχ (m ^ 2)
  rw [Complex.eq_coe_norm_of_nonneg h1, Complex.eq_coe_norm_of_nonneg h2] at hle
  exact_mod_cast hle

/-- **Summability transfer from `L(1 * χ, s)` to `ζ_K(2s)`.** If `χ ^ 2` is trivial on its good
ideals and `L(1 * χ, s)` converges absolutely at `s`, then `ζ_K(2s)` converges absolutely. -/
theorem LSeriesSummable_normCoeff_one_of_LSeriesSummable_convolution_one
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {s : ℂ}
    (hs : LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) s) :
    LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) := by
  rw [LSeriesSummable, ← summable_norm_iff] at hs ⊢
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_term_normCoeff_one_two_mul_le hχ s)
    (hs.comp_injective (Nat.pow_left_injective two_ne_zero))

/-- **Divergence of `L(1 * χ, s)` on `Re s ≤ 1 / 2`.** If `χ ^ 2` is trivial on its good ideals,
then the Dirichlet series of `1 * χ` does not converge absolutely anywhere in `Re s ≤ 1 / 2`. -/
theorem not_LSeriesSummable_normCoeff_convolution_one_of_re_le_half
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {s : ℂ}
    (hs : s.re ≤ 1 / 2) :
    ¬ LSeriesSummable
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) s := by
  intro hsum
  have h1 := (LSeriesSummable_normCoeff_one_iff K).mp
    (LSeriesSummable_normCoeff_one_of_LSeriesSummable_convolution_one hχ hsum)
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
  have h1_nonneg : 0 ≤ (normCoeff K (1 : IdealArithmeticFunction K) : ℕ → ℂ) := fun n ↦ by
    rw [Pi.zero_apply, normCoeff_eq_sum_normFiber]
    exact Finset.sum_nonneg fun _ _ ↦ zero_le_one
  have h1_sum :
      LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) ((2 * σ : ℝ) : ℂ) := by
    simpa [Complex.ofReal_mul] using
      LSeriesSummable_normCoeff_one_of_LSeriesSummable_convolution_one hχ hσ
  rw [dedekindZeta_eq_LSeries_normCoeff_one,
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg h1_nonneg (2 * σ),
    TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg (normCoeff_convolution_one_nonneg hχ) σ,
    Complex.real_le_real]
  refine (summable_norm_iff.mpr h1_sum).tsum_le_tsum_of_inj (fun m : ℕ ↦ m ^ 2)
    (Nat.pow_left_injective two_ne_zero) (fun _ _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (summable_norm_iff.mpr hσ)
  simpa [Complex.ofReal_mul] using norm_term_normCoeff_one_two_mul_le hχ σ m

/-! ### Sharpness witnesses: the ideal Liouville weight and the trivial weight -/

namespace MultiplicativeIdealWeight

variable (K)

/-- **The ideal Liouville weight** `I ↦ (-1) ^ Ω(I)` on integral ideals of `𝓞 K` (with value `0`
at `⊥`), where `Ω(I)` is the number of prime ideal factors of `I` counted with multiplicity.

It has no bad primes and satisfies `liouville K ^ 2 = 1`, with `L(1 * liouville K, s) = ζ_K(2s)`
having exact abscissa `1 / 2`. This witnesses the sharpness of the lower bound `1 / 2` in
`TauCeti.half_le_abscissaOfAbsConv_normCoeff_convolution_one`. -/
noncomputable def liouville : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom := by
    classical
    refine
      { toFun I := if I = ⊥ then 0 else
            (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card
        map_zero' := by simp
        map_one' := by
          simp only [Ideal.one_eq_top, top_ne_bot, ↓reduceIte]
          rw [← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
          simp
        map_mul' I J := ?_ }
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [hI, hJ, hIJ, ↓reduceIte]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.card_add, pow_add]
  finite_setOf_apply_eq_zero := by
    refine Set.finite_empty.subset fun P hP ↦ ?_
    change (if P.asIdeal = ⊥ then (0 : ℂ) else
      (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors P.asIdeal).card) = 0 at hP
    simp [P.ne_bot] at hP

/-- Defining formula for `liouville K` on nonzero ideals. -/
theorem liouville_apply {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    liouville K I = (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card := by
  change (if I = ⊥ then (0 : ℂ) else
    (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card) = _
  simp [hI]

/-- The ideal Liouville weight takes the value `-1` at every height-one prime. -/
@[simp]
theorem liouville_prime (P : HeightOneSpectrum (𝓞 K)) : liouville K P.asIdeal = -1 := by
  rw [liouville_apply K P.ne_bot,
    UniqueFactorizationMonoid.normalizedFactors_irreducible P.prime.irreducible]
  simp

/-- The ideal Liouville weight has no bad primes. -/
@[simp]
theorem badPrimes_liouville : (liouville K).badPrimes = ∅ := by
  ext P
  simp [mem_badPrimes]

/-- The pointwise square of the ideal Liouville weight is the trivial weight. -/
@[simp]
theorem liouville_sq : liouville K ^ 2 = 1 := by
  apply ext_heightOneSpectrum
  intro P
  simp [pow_apply _ two_ne_zero, one_apply, P.ne_bot]

/-- The square of the ideal Liouville weight is trivial on its good ideals. -/
theorem isTrivialOnGood_liouville_sq : (liouville K ^ 2).IsTrivialOnGood := by
  rw [liouville_sq]
  exact isTrivialOnGood_one

end MultiplicativeIdealWeight

/-- A prime-power factorization `∏ Q ∈ S, Q ^ e Q` is a square ideal only if every exponent `e P`
for `P ∈ S` is even. -/
private theorem even_of_sq_eq_prod_pow {S : Finset (HeightOneSpectrum (𝓞 K))}
    {e : HeightOneSpectrum (𝓞 K) → ℕ} {B : (Ideal (𝓞 K))⁰}
    (hB : ((B ^ 2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = ∏ Q ∈ S, Q.asIdeal ^ e Q)
    {P : HeightOneSpectrum (𝓞 K)} (hPS : P ∈ S) : Even (e P) := by
  classical
  have hprod : UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ S, Q.asIdeal ^ e Q) =
      ∑ Q ∈ S, UniqueFactorizationMonoid.normalizedFactors (Q.asIdeal ^ e Q) := by
    rw [Finset.prod_eq_multiset_prod, UniqueFactorizationMonoid.normalizedFactors_multiset_prod,
      Multiset.map_map, Finset.sum_eq_multiset_sum]
    · rfl
    · simp only [Multiset.mem_map, not_exists, not_and]
      intro Q _
      exact pow_ne_zero (e Q) Q.ne_bot
  have hfac := congrArg (fun I : Ideal (𝓞 K) ↦
    Multiset.count (normalize P.asIdeal) (UniqueFactorizationMonoid.normalizedFactors I))
    (by simpa [SubmonoidClass.coe_pow] using hB :
      (B : Ideal (𝓞 K)) ^ 2 = ∏ Q ∈ S, Q.asIdeal ^ e Q)
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul, hprod,
    Multiset.count_sum'] at hfac
  have hcount (Q : HeightOneSpectrum (𝓞 K)) :
      Multiset.count (normalize P.asIdeal)
        (UniqueFactorizationMonoid.normalizedFactors (Q.asIdeal ^ e Q)) =
        if Q = P then e Q else 0 := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible Q.prime.irreducible,
      Multiset.count_nsmul, Multiset.count_singleton]
    by_cases hQP : Q = P
    · subst hQP; simp
    · have hne : P.asIdeal ≠ Q.asIdeal := fun h ↦ hQP (HeightOneSpectrum.asIdeal_injective h.symm)
      simp [hQP, hne]
  simp_rw [hcount] at hfac
  rw [Finset.sum_ite_eq' S P, ite_eq_left hPS] at hfac
  exact ⟨Multiset.count (normalize P.asIdeal)
    (UniqueFactorizationMonoid.normalizedFactors (B : Ideal (𝓞 K))), by omega⟩

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
  have hlocal (P : HeightOneSpectrum (𝓞 K)) :
      IdealArithmeticFunction.convolution 1
          (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction
          (P.primeIdealPow (e P)) = if Even (e P) then 1 else 0 := by
    rw [convolution_one_primeIdealPow, MultiplicativeIdealWeight.liouville_prime, neg_one_geom_sum]
    by_cases he : Even (e P)
    · simp [he, Nat.not_even_iff_odd.mpr he.add_one]
    · simp [he, (Nat.not_even_iff_odd.mp he).add_one]
  simp_rw [mk_primeIdealPow_eq, hlocal]
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
      exact hPodd (even_of_sq_eq_prod_pow hA hPS)
    rw [ite_eq_right hnsq]
    exact Finset.prod_eq_zero hPS (ite_eq_right hPodd)

open Classical in
/-- The norm coefficients of `1 * λ_K` are `normCoeff K 1 m` at squares `m ^ 2` and `0`
elsewhere. -/
theorem normCoeff_convolution_one_liouville (n : ℕ) :
    normCoeff K (IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction) n =
      if h : ∃ m : ℕ, n = m ^ 2 then
        normCoeff K (1 : IdealArithmeticFunction K) h.choose
      else 0 := by
  rw [normCoeff_eq_sum_normFiber]
  simp_rw [convolution_one_liouville_apply]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := (show ∃ m : ℕ, n = m ^ 2 from hn)
    have hm : hn.choose = m := Nat.pow_left_injective two_ne_zero hn.choose_spec.symm
    rw [hm, normCoeff_eq_sum_normFiber, ← Finset.sum_filter]
    have hinj : Function.Injective (fun B : (Ideal (𝓞 K))⁰ ↦ B ^ 2) := fun B₁ B₂ h ↦
      Subtype.ext (pow_left_injective two_ne_zero (by simpa using congrArg Subtype.val h))
    refine (Finset.sum_nbij (fun B : (Ideal (𝓞 K))⁰ ↦ B ^ 2) ?_ (fun _ _ _ _ h ↦ hinj h) ?_
      (fun _ _ ↦ rfl)).symm
    · intro B hB
      rw [Finset.mem_filter, mem_normFiber]
      exact ⟨by rw [SubmonoidClass.coe_pow, map_pow, (mem_normFiber K).mp hB], ⟨B, rfl⟩⟩
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter, mem_normFiber] at hA
      obtain ⟨B, rfl⟩ := hA.2
      refine ⟨B, ?_, rfl⟩
      rw [Finset.mem_coe, mem_normFiber]
      exact Nat.pow_left_injective two_ne_zero
        (by simpa [SubmonoidClass.coe_pow, map_pow] using hA.1)
  · refine Finset.sum_eq_zero fun A hA ↦ ite_eq_right ?_
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
    normCoeff_convolution_one_liouville, dite_eq_left ⟨m, rfl⟩]
  have hch : (⟨m, rfl⟩ : ∃ k, m ^ 2 = k ^ 2).choose = m :=
    Nat.pow_left_injective two_ne_zero (⟨m, rfl⟩ : ∃ k, m ^ 2 = k ^ 2).choose_spec.symm
  have hpow : ((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s) := by
    simpa [Nat.cast_pow] using (Complex.natCast_cpow_natCast_mul m 2 s).symm
  rw [hch, hpow]

/-- Away from squares, the Dirichlet term of `1 * λ_K` vanishes. -/
private theorem term_normCoeff_convolution_one_liouville_eq_zero_of_notMem_range (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ ↦ m ^ 2)) :
    LSeries.term (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rw [LSeries.term_of_ne_zero hn0, normCoeff_convolution_one_liouville, dite_eq_right, zero_div]
  rintro ⟨m, rfl⟩
  exact hn ⟨m, rfl⟩

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
  change LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) ↔ 1 / 2 < s.re
  rw [LSeriesSummable_normCoeff_one_iff]
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
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
  gcongr
  have h1 : 0 ≤ normCoeff K (1 : IdealArithmeticFunction K) n := by
    rw [normCoeff_eq_sum_normFiber]; exact Finset.sum_nonneg fun _ _ ↦ zero_le_one
  have hle : normCoeff K (1 : IdealArithmeticFunction K) n ≤
      normCoeff K (IdealArithmeticFunction.convolution 1
        (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction) n := by
    rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
    refine Finset.sum_le_sum fun A _ ↦ ?_
    rw [Pi.one_apply, MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
      IdealArithmeticFunction.convolution_one_one_apply]
    exact_mod_cast (Finset.one_le_card.mpr ⟨(1, A), by simp⟩ :
      1 ≤ (Ideal.divisorsAntidiagonal A).card)
  have h2 : 0 ≤ normCoeff K (IdealArithmeticFunction.convolution 1
      (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction) n :=
    normCoeff_convolution_one_nonneg h1sq n
  rw [Complex.eq_coe_norm_of_nonneg h1, Complex.eq_coe_norm_of_nonneg h2] at hle
  exact_mod_cast hle

end TauCeti
