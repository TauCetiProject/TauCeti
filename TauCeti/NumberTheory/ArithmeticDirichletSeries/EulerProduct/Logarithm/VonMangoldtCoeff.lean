/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Convergence
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PowerIndex
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

For general Euler-product data `D`, whose values at higher prime powers are independent, the
coefficient at `𝔭 ^ e` is `log N(𝔭)` times the degree-`e` coefficient of the local series
`X F_𝔭'/F_𝔭`. This defines the von Mangoldt function `Λ_D` of `D`, which is the von Mangoldt
transform of the weight in the completely multiplicative case. Where the local power series are
zero-free on the disks of absolute convergence, `-logDeriv L(s) = ∑' A, Λ_D(A) / N(A) ^ s`, with
absolute convergence.

## Main definitions

* `TauCeti.EulerProductData.vonMangoldt`: the von Mangoldt function `Λ_D` of Euler-product data.

## Main results

* `TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform`: the von Mangoldt
  weighted ideal terms are summable on the half-plane, for any ideal arithmetic function.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`: the
  coefficient identity for a completely multiplicative weight.
* `TauCeti.EulerProductData.vonMangoldt_ofMultiplicativeIdealWeight`: `Λ_D` of a completely
  multiplicative weight is its von Mangoldt transform.
* `TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree` and
  `TauCeti.EulerProductData.LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree`: the coefficient
  identity for general Euler-product data, ideal-indexed and regrouped by norm.

## Implementation notes

Summability is comparison against `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`,
whose weight `log N(I)` dominates `‖Λ(I)‖` by `norm_vonMangoldt_le_log`. Passing from the
`(𝔭, k)`-indexed sum to the ideal-indexed one is
`TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`.

For general `D` the local coefficients of `X F_𝔭'/F_𝔭` are not bounded by those of `F_𝔭`, so the
comparison goes through the majorant `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le`: at
every prime whose prime-power tail has absolute sum at most `1/2`, the local von Mangoldt terms
are at most twice the `log`-weighted terms of `D`. Absolute convergence of `D` leaves only
finitely many other primes, and at each of them zero-freeness gives local convergence.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, for the von Mangoldt function of
  a general Euler product.
-/

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti

namespace IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- **The von Mangoldt weighted ideal terms converge absolutely.** Strictly to the right of the
abscissa of absolute convergence of `χ`, the terms `χ(A) Λ(A) / N(A) ^ s` are summable.

`Λ(A)` is bounded by `log N(A)`, and weighting the ideal terms by `log N(A)` preserves summability
strictly to the right of a point of absolute convergence. -/
theorem summable_idealTerm_vonMangoldtTransform {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    Summable (idealTerm K f.vonMangoldtTransform s) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, Summable (idealTerm K f y) ∧ y < s.re := by
    simpa [idealAbscissaOfAbsConv_def, sInf_lt_iff] using hs
  have hlog := summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re
    (f := f) (s := (y : ℂ)) (s' := s) (h := by simpa using hys) (hs := hy)
  refine hlog.of_norm_bounded fun A ↦ ?_
  have hfac : ‖idealTerm K f.vonMangoldtTransform s A‖
      = ‖(IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) A‖
        * ‖idealTerm K f s A‖ := by
    rw [idealTerm_def, idealTerm_def, IdealArithmeticFunction.vonMangoldtTransform_apply,
      norm_div, norm_div, norm_mul]
    ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_right
    (IdealArithmeticFunction.norm_vonMangoldt_le_log A) (norm_nonneg _)

end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- The von Mangoldt weighted ideal term at `𝔭 ^ (k + 1)` is the `(𝔭, k)` summand of the
prime-power expansion of the logarithmic derivative. -/
private theorem idealTerm_vonMangoldtTransform_prime_pow (s : ℂ)
    (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s
        (P.idealPrimePowerOf k : (Ideal (𝓞 K))⁰)
      = Complex.log (Ideal.absNorm P.asIdeal : ℂ)
          * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (k + 1) := by
  have hmem : P.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hP : Prime (((⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰)) : Ideal (𝓞 K)) :=
    Ideal.prime_of_isPrime P.ne_bot P.isPrime
  have hpow : (P.idealPrimePowerOf k : (Ideal (𝓞 K))⁰)
      = (⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰) ^ (k + 1) := Subtype.ext (by simp)
  have hlog : Complex.log (Ideal.absNorm P.asIdeal : ℂ)
      = ((Real.log (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [idealTerm_def, hpow,
    MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos,
    SubmonoidClass.coe_pow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow, hlog, Nat.succ_eq_add_one]
  ring


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
  have hsum := IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform
    (f := χ.toIdealArithmeticFunction) hs
  have hsupp : Function.support (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s)
      ⊆ {A : (Ideal (𝓞 K))⁰ | IsPrimePow (A : Ideal (𝓞 K))} := by
    intro A hA
    rw [Function.mem_support, idealTerm_def, div_ne_zero_iff] at hA
    exact ((IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff _).mp hA.1).1
  have hcoe : ∀ pe : HeightOneSpectrum (𝓞 K) × ℕ,
      (pe.1.idealPrimePowerOf pe.2 : (Ideal (𝓞 K))⁰)
        = ((idealPrimePowerEquiv pe : IdealPrimePower K) : (Ideal (𝓞 K))⁰) := by
    rintro ⟨P, k⟩
    rw [HeightOneSpectrum.idealPrimePowerEquiv_apply]
  have hinj : Function.Injective
      (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦ (pe.1.idealPrimePowerOf pe.2 : (Ideal (𝓞 K))⁰)) :=
    fun a b hab ↦ idealPrimePowerEquiv.injective
      (Subtype.coe_injective ((hcoe a).symm.trans (hab.trans (hcoe b))))
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

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)

/-- The prime power indexed by `(P, e)` is the nonzero ideal `P ^ (e + 1)`. -/
private theorem coe_idealPrimePowerOf_eq_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (P.idealPrimePowerOf e : (Ideal (𝓞 K))⁰) = P.primeIdealPow (e + 1) :=
  Subtype.ext (by simp)

open Classical in
/-- The **von Mangoldt function** `Λ_D` of Euler-product data. At a prime power `P ^ e` with
`e ≥ 1` it is `log N(P)` times the degree-`e` coefficient of the local logarithmic-derivative
series `X F_P'/F_P`, and it vanishes off the prime powers. These are the Dirichlet coefficients
of `-L'/L` (`TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree`); for a
completely multiplicative weight they are the von Mangoldt transform of the weight. -/
noncomputable def vonMangoldt : IdealArithmeticFunction K := fun A ↦
  if h : IsPrimePow (A : Ideal (𝓞 K)) then
    Real.log (Ideal.absNorm (primePowerBase (⟨A, h⟩ : IdealPrimePower K)).asIdeal) *
      PowerSeries.coeff (primePowerExponent (⟨A, h⟩ : IdealPrimePower K))
        (D.localLogDerivSeries (primePowerBase (⟨A, h⟩ : IdealPrimePower K)))
  else 0

/-- `Λ_D` vanishes off the prime-power ideals. -/
theorem vonMangoldt_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) : D.vonMangoldt A = 0 := by
  rw [vonMangoldt, dite_eq_right hA]

/-- The value of `Λ_D` at `P ^ e` is `log N(P)` times the degree-`e` local
logarithmic-derivative coefficient. For `e = 0` both sides vanish. -/
@[simp]
theorem vonMangoldt_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    D.vonMangoldt (P.primeIdealPow e) =
      Real.log (Ideal.absNorm P.asIdeal) * PowerSeries.coeff e (D.localLogDerivSeries P) := by
  cases e with
  | zero =>
    rw [coeff_zero_localLogDerivSeries, mul_zero]
    refine D.vonMangoldt_eq_zero_of_not_isPrimePow fun h ↦ h.not_isUnit ?_
    simp
  | succ k =>
    rw [← coe_idealPrimePowerOf_eq_primeIdealPow, vonMangoldt,
      dite_eq_left (P.idealPrimePowerOf k).2]
    simp

/-- For completely multiplicative data, `Λ_D` is the von Mangoldt transform `A ↦ χ(A) Λ(A)` of
the weight. -/
theorem vonMangoldt_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).vonMangoldt =
      χ.toIdealArithmeticFunction.vonMangoldtTransform := by
  funext A
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨⟨P, k⟩, hPk⟩ := idealPrimePowerEquiv.surjective (⟨A, hA⟩ : IdealPrimePower K)
    have hA' : A = P.primeIdealPow (k + 1) := by
      rw [HeightOneSpectrum.idealPrimePowerEquiv_apply] at hPk
      rw [← coe_idealPrimePowerOf_eq_primeIdealPow, hPk]
    have hP : Prime ((⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ :
        (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := Ideal.prime_of_isPrime P.ne_bot P.isPrime
    have hpow : P.primeIdealPow (k + 1) =
        (⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ : (Ideal (𝓞 K))⁰) ^ (k + 1) :=
      Subtype.ext (by simp)
    rw [hA', vonMangoldt_primeIdealPow, coeff_localLogDerivSeries_ofMultiplicativeIdealWeight,
      ite_eq_right k.succ_ne_zero, hpow,
      MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos, mul_comm]
  · rw [vonMangoldt_eq_zero_of_not_isPrimePow _ hA]
    by_contra h
    exact hA ((MultiplicativeIdealWeight.vonMangoldtTransform_ne_zero_iff χ).mp (Ne.symm h)).1

section Analytic

variable {σ : ℝ} {s : ℂ}

/-- The ideal term of `Λ_D` at `P ^ e` is `log N(P)` times the `e`-th term of the evaluated
local logarithmic-derivative series. -/
private theorem idealTerm_vonMangoldt_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)
    (e : ℕ) :
    idealTerm K D.vonMangoldt s (P.primeIdealPow e) =
      (Real.log (Ideal.absNorm P.asIdeal) : ℂ) * (PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) := by
  rw [IdealArithmeticFunction.idealTerm_primeIdealPow_eq_mul_cpow_neg, vonMangoldt_primeIdealPow,
    mul_assoc]

/-- The norm of the ideal term of `Λ_D` at `P ^ e`. -/
private theorem norm_idealTerm_vonMangoldt_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)
    (e : ℕ) :
    ‖idealTerm K D.vonMangoldt s (P.primeIdealPow e)‖ =
      Real.log (Ideal.absNorm P.asIdeal) * ‖PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e‖ := by
  rw [idealTerm_vonMangoldt_primeIdealPow, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.log_nonneg (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P).le))]

/-- **The local majorant for `Λ_D`.** If the ideal series of `D` converges absolutely at a real
point `σ < Re(s)` and the prime-power tail of `D` at `P` has absolute sum at most `1/2` at `s`,
then the absolute sum of the terms of `Λ_D` at the powers of `P` is at most twice the
corresponding `log`-weighted sum for `D`. -/
private theorem tsum_norm_idealTerm_vonMangoldt_le
    (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ)) (hs : σ < s.re)
    (P : HeightOneSpectrum (𝓞 K))
    (ht : ∑' e : ℕ, ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ ≤
      1 / 2) :
    ∑' e : ℕ, ‖idealTerm K D.vonMangoldt s (P.primeIdealPow (e + 1))‖ ≤
      2 * ∑' e : ℕ, Real.log (Ideal.absNorm (P.primeIdealPow (e + 1) : Ideal (𝓞 K))) *
        ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ := by
  set F := D.localPowerSeries P
  set r : ℝ := ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖
  set L : ℝ := Real.log (Ideal.absNorm P.asIdeal)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P)
  -- The weighted coefficients of `F` are the ideal terms of `D` along the powers of `P`.
  have hterm (n : ℕ) : ‖PowerSeries.coeff n F‖ * r ^ n =
      ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow n)‖ := by
    rw [IdealArithmeticFunction.idealTerm_primeIdealPow_eq_mul_cpow_neg, norm_mul, norm_pow,
      coeff_localPowerSeries]
  have hlogterm (n : ℕ) : Real.log (Ideal.absNorm (P.primeIdealPow n : Ideal (𝓞 K))) *
      ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow n)‖ =
        L * (n * ‖PowerSeries.coeff n F‖ * r ^ n) := by
    rw [P.absNorm_primeIdealPow, Nat.cast_pow, Real.log_pow, ← hterm]
    ring
  have hlogsum : Summable fun n : ℕ ↦ L * (n * ‖PowerSeries.coeff n F‖ * r ^ n) :=
    ((summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re K (s := (σ : ℂ)) (by simpa using hs)
      hσ).comp_injective P.primeIdealPow_injective).congr hlogterm
  have hsum : Summable fun n : ℕ ↦ n * ‖PowerSeries.coeff n F‖ * r ^ n := by
    simpa [hL.ne'] using hlogsum.mul_left L⁻¹
  have ht' : ∑' n : ℕ, ‖PowerSeries.coeff (n + 1) F‖ * r ^ (n + 1) ≤ 1 / 2 := by
    simpa only [hterm] using ht
  -- The majorant bound for the formal logarithmic derivative of `F`.
  have hmaj := PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le F
    (D.constantCoeff_localPowerSeries P) (norm_nonneg _) hsum (by linarith)
  have hT : 0 ≤ ∑' n : ℕ, n * ‖PowerSeries.coeff n F‖ * r ^ n :=
    tsum_nonneg fun n ↦ by positivity
  have hmaj' : ∑' m : ℕ, ‖PowerSeries.coeff m (PowerSeries.logDeriv F)‖ * r ^ (m + 1) ≤
      2 * ∑' n : ℕ, n * ‖PowerSeries.coeff n F‖ * r ^ n := by
    refine hmaj.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hvm (m : ℕ) : ‖idealTerm K D.vonMangoldt s (P.primeIdealPow (m + 1))‖ =
      L * (‖PowerSeries.coeff m (PowerSeries.logDeriv F)‖ * r ^ (m + 1)) := by
    rw [norm_idealTerm_vonMangoldt_primeIdealPow, localLogDerivSeries_def,
      PowerSeries.coeff_succ_X_mul, norm_mul, norm_pow]
  have hlogT : ∑' e : ℕ, Real.log (Ideal.absNorm (P.primeIdealPow (e + 1) : Ideal (𝓞 K))) *
      ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ =
        L * ∑' n : ℕ, n * ‖PowerSeries.coeff n F‖ * r ^ n := by
    rw [hsum.tsum_eq_zero_add, Nat.cast_zero, zero_mul, zero_mul, zero_add, ← tsum_mul_left]
    exact tsum_congr fun e ↦ by rw [hlogterm]
  rw [tsum_congr hvm, tsum_mul_left, hlogT]
  nlinarith

/-- **Absolute convergence of the von Mangoldt series of an Euler product.** Suppose `σ` lies
strictly to the right of the ideal-indexed abscissa of absolute convergence of `D` and every local
power series is zero-free on the disk of radius `N(P)⁻σ`. Then the ideal-indexed series of `Λ_D`
converges absolutely at every `s` with `σ < Re(s)`. -/
theorem summable_idealTerm_vonMangoldt_of_zeroFree
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    Summable (idealTerm K D.vonMangoldt s) := by
  have hσsum : Summable (idealTerm K D.toIdealArithmeticFunction σ) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (by simpa using hσ)
  have hssum : Summable (idealTerm K D.toIdealArithmeticFunction s) :=
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (hσ.trans (by exact_mod_cast hs))
  -- `Λ_D` lives on the prime powers `P ^ (k + 1)`.
  have hg : Function.Injective fun Pk : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Pk.1.primeIdealPow (Pk.2 + 1) := by
    rintro ⟨P, k⟩ ⟨Q, l⟩ hPQ
    refine idealPrimePowerEquiv.injective (Subtype.ext ?_)
    rw [HeightOneSpectrum.idealPrimePowerEquiv_apply, HeightOneSpectrum.idealPrimePowerEquiv_apply,
      coe_idealPrimePowerOf_eq_primeIdealPow, coe_idealPrimePowerOf_eq_primeIdealPow]
    exact hPQ
  refine (hg.summable_iff fun A hA ↦ ?_).mp ?_
  · rw [idealTerm_def, D.vonMangoldt_eq_zero_of_not_isPrimePow fun h ↦ hA ?_, zero_div]
    obtain ⟨⟨P, k⟩, hPk⟩ := idealPrimePowerEquiv.surjective (⟨A, h⟩ : IdealPrimePower K)
    refine ⟨(P, k), ?_⟩
    rw [HeightOneSpectrum.idealPrimePowerEquiv_apply] at hPk
    beta_reduce
    rw [← coe_idealPrimePowerOf_eq_primeIdealPow, hPk]
  refine Summable.of_norm ((summable_prod_of_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun P ↦ ?_, ?_⟩)
  · -- Each fibre converges by zero-freeness at `P`.
    have hloc := (summable_nat_add_iff 1).mpr
      (D.summable_norm_coeff_localLogDerivSeries_of_zeroFree P
        ((D.abscissaOfAbsConv_localArithmeticFactor_le P).trans_lt hσ) (hne P) hs)
    exact (hloc.mul_left (Real.log (Ideal.absNorm P.asIdeal))).congr fun k ↦
      (D.norm_idealTerm_vonMangoldt_primeIdealPow P s (k + 1)).symm
  · -- Away from finitely many primes, the fibre sums are dominated by the log-weighted terms of
    -- `D`.
    have hB : Summable fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
        Real.log (Ideal.absNorm (P.primeIdealPow (e + 1) : Ideal (𝓞 K))) *
          ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖ := by
      have hlog := summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re K (s := (σ : ℂ))
        (by simpa using hs) hσsum
      refine (summable_tsum_norm_idealPrimePowerOf (g := fun I : (Ideal (𝓞 K))⁰ ↦
        Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) *
          ‖idealTerm K D.toIdealArithmeticFunction s I‖)
        (hlog.congr fun I ↦ (Real.norm_of_nonneg (mul_nonneg (Real.log_natCast_nonneg _)
          (norm_nonneg _))).symm)).congr fun P ↦ tsum_congr fun e ↦ ?_
      rw [Real.norm_of_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (norm_nonneg _)),
        coe_idealPrimePowerOf_eq_primeIdealPow]
    have htail : Filter.Tendsto (fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
        ‖idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow (e + 1))‖)
        Filter.cofinite (nhds 0) := by
      simpa only [coe_idealPrimePowerOf_eq_primeIdealPow] using
        (summable_tsum_norm_idealPrimePowerOf (summable_norm_iff.mpr hssum)).tendsto_cofinite_zero
    refine (hB.mul_left 2).of_norm_bounded_eventually ?_
    filter_upwards [htail.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with P hP
    rw [Real.norm_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
    exact D.tsum_norm_idealTerm_vonMangoldt_le hσsum hs P hP

/-- **The logarithmic derivative of an Euler product as a von Mangoldt series.** Suppose `σ` lies
strictly to the right of the ideal-indexed abscissa of absolute convergence of `D` and every local
power series is zero-free on the disk of radius `N(P)⁻σ`. Then for `σ < Re(s)` the ideal-indexed
series of `Λ_D` converges absolutely to `-L'(s)/L(s)`, where `L` is the `LSeries` of the norm
coefficients of `D`:

`-logDeriv L(s) = ∑' A, Λ_D(A) / N(A) ^ s`. -/
theorem hasSum_idealTerm_vonMangoldt_of_zeroFree
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    HasSum (idealTerm K D.vonMangoldt s)
      (-logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s) := by
  have hsum := D.summable_idealTerm_vonMangoldt_of_zeroFree hσ hne hs
  have hsupp : Function.support (idealTerm K D.vonMangoldt s) ⊆
      {A : (Ideal (𝓞 K))⁰ | IsPrimePow (A : Ideal (𝓞 K))} := fun A hA ↦ by
    by_contra h
    exact hA (by rw [idealTerm_def, D.vonMangoldt_eq_zero_of_not_isPrimePow h, zero_div])
  -- Each prime contributes `log N(P)` times its evaluated local logarithmic-derivative series.
  have hfib (P : HeightOneSpectrum (𝓞 K)) : HasSum
      (fun k : ℕ ↦ idealTerm K D.vonMangoldt s (P.idealPrimePowerOf k : (Ideal (𝓞 K))⁰))
      (-(-Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
        ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e)) := by
    have hloc := (D.summable_coeff_localLogDerivSeries_of_zeroFree P
      ((D.abscissaOfAbsConv_localArithmeticFactor_le P).trans_lt hσ) (hne P) hs).hasSum
    rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one, coeff_zero_localLogDerivSeries, zero_mul,
      sub_zero] at hloc
    rw [neg_mul, neg_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    refine (hloc.mul_left _).congr_fun fun k ↦ ?_
    rw [coe_idealPrimePowerOf_eq_primeIdealPow, idealTerm_vonMangoldt_primeIdealPow]
  convert hsum.hasSum using 1
  rw [tsum_eq_tsum_idealPrimePower_of_support_subset hsum hsupp,
    tsum_congr fun P ↦ (hfib P).tsum_eq, tsum_neg,
    (D.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree hσ hne hs).tsum_eq]

/-- The norm-regrouped form of
`TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree`: the Mathlib `LSeries` of the
norm coefficients of `Λ_D` converges absolutely to `-L'(s)/L(s)`. -/
theorem LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    LSeriesHasSum (normCoeff K D.vonMangoldt) s
      (-logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s) :=
  regroupByNorm K (D.hasSum_idealTerm_vonMangoldt_of_zeroFree hσ hne hs)

/-- **The coefficient identity for the logarithmic derivative of an Euler product.** Under the
hypotheses of `TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree`,

`logDeriv L(s) = -LSeries (normCoeff Λ_D) s`. -/
theorem logDeriv_LSeries_eq_neg_LSeries_normCoeff_vonMangoldt_of_zeroFree
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s =
      -LSeries (normCoeff K D.vonMangoldt) s := by
  rw [(D.LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree hσ hne hs).LSeries_eq, neg_neg]

end Analytic

end EulerProductData

end TauCeti
