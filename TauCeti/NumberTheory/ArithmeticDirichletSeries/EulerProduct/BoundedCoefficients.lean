/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.ExpLog
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# Euler products over the primes of a number field with bounded coefficients

Let `K` be a number field and `a` a complex function on the height-one primes `𝔭` of `𝓞 K` with
`‖a 𝔭‖ ≤ 1`. This file studies the Euler product

`P(a, s) = ∏_𝔭 (1 - a(𝔭) N(𝔭) ^ (-s))⁻¹`,

`TauCeti.primeEulerProduct a s`, on the half-plane `Re s > 1`. The coefficients need not come
from a multiplicative function on ideals, and they may vanish at infinitely many primes, so this
is more general than the Euler products of `TauCeti.MultiplicativeIdealWeight`.

For `Re s > 1` the local ratios `a(𝔭) N(𝔭) ^ (-s)` are absolutely summable and have modulus at
most `1/2`, so the product converges unconditionally, is the exponential of the convergent sum
`∑_𝔭 -log (1 - a(𝔭) N(𝔭) ^ (-s))` of principal logarithms, and is nonzero. For `Re s ≥ 2` that
sum is bounded by `3 [K : ℚ]`, because `‖log (1 + z)‖ ≤ 3/2 ‖z‖` for `‖z‖ ≤ 1/2` and
`∑_𝔭 N(𝔭) ^ (-2) ≤ [K : ℚ]` (`TauCeti.tsum_absNorm_rpow_neg_two_le`). Setting finitely many
coefficients to zero divides the product by the corresponding factors. Finally, when `a(𝔭) = χ(𝔭)`
for a completely multiplicative `χ` on the ideals of `𝓞 K` with `‖χ‖ ≤ 1`, the product is the
Dirichlet series `∑_I χ(I) N(I) ^ (-s)` over the nonzero ideals; this comes from the analytic
Euler product `TauCeti.EulerProductData.hasProd_eulerFactor` already in the library.

## Main definitions

* `TauCeti.primeEulerProduct a s`: the Euler product `∏_𝔭 (1 - a(𝔭) N(𝔭) ^ (-s))⁻¹`.

## Main results

* `TauCeti.hasProd_primeEulerProduct`: unconditional convergence for `Re s > 1`.
* `TauCeti.primeEulerProduct_eq_exp`: the product is `exp (∑_𝔭 -log (1 - a(𝔭) N(𝔭) ^ (-s)))`,
  and `TauCeti.primeEulerProduct_ne_zero`: it does not vanish.
* `TauCeti.continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow` and
  `TauCeti.continuousOn_primeEulerProduct`: the sum of the logarithms and the product are
  continuous in real `s > 1`.
* `TauCeti.abs_log_norm_primeEulerProduct_le`: `|log ‖P(a, s)‖| ≤ 3 [K : ℚ]` for `Re s ≥ 2`.
* `TauCeti.primeEulerProduct_indicator_compl_mul_prod`: deleting the factors at a finite set `Q`
  of primes divides the product by them.
* `TauCeti.hasSum_primeEulerProduct`: for a completely multiplicative `χ` with `‖χ‖ ≤ 1`, the
  Dirichlet series of `χ` over the nonzero ideals sums to `P(χ, s)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/HeckeL/EulerProduct.lean`: `New.eulerProd`, `New.eulerProd_eq_exp`,
`New.hasProd_eulerProd`, `New.eulerProd_erase`, `New.eulerProd_ne_zero_and_abs_log_norm_le` and
`New.hasSum_eulerProd`. Here the product is Mathlib's `tprod` for complex `s`, rather than an
exponential of a sum extended by continuity from real `s > 1`, and the identification with the
Dirichlet series reuses the library's ideal Euler product instead of a sieve.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter XV.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
-/

public section

open NumberField IsDedekindDomain Complex
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The modulus of `x N(𝔭) ^ (-s)` is `‖x‖ N(𝔭) ^ (-Re s)`. -/
theorem IsDedekindDomain.HeightOneSpectrum.norm_div_absNorm_cpow (𝔭 : HeightOneSpectrum (𝓞 K))
    (x s : ℂ) :
    ‖x / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ = ‖x‖ * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s.re) := by
  rw [norm_div, norm_natCast_cpow_of_pos (NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭).pos,
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

namespace TauCeti

/-- **The Euler product with coefficients `a`** over the height-one primes of `𝓞 K`:
`∏_𝔭 (1 - a(𝔭) N(𝔭) ^ (-s))⁻¹`, as Mathlib's unconditional product `tprod`. For `‖a 𝔭‖ ≤ 1` and
`Re s > 1` the product converges (`TauCeti.hasProd_primeEulerProduct`); elsewhere `tprod` takes its
junk value. -/
noncomputable def primeEulerProduct (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏' 𝔭 : HeightOneSpectrum (𝓞 K), (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹

variable {a : HeightOneSpectrum (𝓞 K) → ℂ} {s : ℂ}

/-- The defining formula of `TauCeti.primeEulerProduct`. -/
theorem primeEulerProduct_def (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    primeEulerProduct a s =
      ∏' 𝔭 : HeightOneSpectrum (𝓞 K), (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [primeEulerProduct]

/-- With zero coefficients every Euler factor is `1`, so the Euler product is `1`. -/
@[simp]
theorem primeEulerProduct_zero (s : ℂ) :
    primeEulerProduct (0 : HeightOneSpectrum (𝓞 K) → ℂ) s = 1 := by
  simp [primeEulerProduct_def]

/-- A local ratio `a(𝔭) N(𝔭) ^ (-s)` with `‖a 𝔭‖ ≤ 1` has modulus at most `N(𝔭) ^ (-Re s)`. -/
theorem norm_div_absNorm_cpow_le_rpow_neg {𝔭 : HeightOneSpectrum (𝓞 K)} (ha : ‖a 𝔭‖ ≤ 1) :
    ‖a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s.re) := by
  rw [𝔭.norm_div_absNorm_cpow]
  exact mul_le_of_le_one_left (by positivity) ha

/-- For `Re s ≥ 1` a local ratio `a(𝔭) N(𝔭) ^ (-s)` with `‖a 𝔭‖ ≤ 1` has modulus at most `1/2`,
since `N(𝔭) ≥ 2`. -/
theorem norm_div_absNorm_cpow_le_half {𝔭 : HeightOneSpectrum (𝓞 K)} (ha : ‖a 𝔭‖ ≤ 1)
    (hs : 1 ≤ s.re) : ‖a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ ≤ 1 / 2 :=
  (norm_div_absNorm_cpow_le_rpow_neg ha).trans
    (Real.rpow_neg_le_half (two_le_absNorm_asIdeal_real 𝔭) hs)

/-- For `Re s > 1` and `‖a‖ ≤ 1` the local ratios `a(𝔭) N(𝔭) ^ (-s)` are absolutely summable. -/
theorem summable_norm_div_absNorm_cpow (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ ‖a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ :=
  (summable_absNorm_rpow_primes_of_one_lt hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun 𝔭 ↦ norm_div_absNorm_cpow_le_rpow_neg (ha 𝔭)

/-- For `Re s ≥ 1` and `‖a‖ ≤ 1` the Euler factor `1 - a(𝔭) N(𝔭) ^ (-s)` lies in the slit plane,
where the principal logarithm is continuous. -/
theorem one_sub_div_absNorm_cpow_mem_slitPlane {𝔭 : HeightOneSpectrum (𝓞 K)} (ha : ‖a 𝔭‖ ≤ 1)
    (hs : 1 ≤ s.re) : 1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one
    (by rw [norm_neg]; linarith [norm_div_absNorm_cpow_le_half ha hs])

/-- For `Re s > 1` and `‖a‖ ≤ 1` the logarithms of the Euler factors are summable. -/
theorem summable_neg_log_one_sub_div_absNorm_cpow (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :=
  (summable_norm_div_absNorm_cpow ha hs).of_norm.clog_one_sub.neg

/-- For `Re s ≥ 1`, `σ ≤ Re s` and `‖a 𝔭‖ ≤ 1` the logarithm of the Euler factor at `𝔭` has modulus
at most `3/2 N(𝔭) ^ (-σ)`, since `‖log (1 + z)‖ ≤ 3/2 ‖z‖` for `‖z‖ ≤ 1/2`. -/
theorem norm_neg_log_one_sub_div_absNorm_cpow_le {𝔭 : HeightOneSpectrum (𝓞 K)} (ha : ‖a 𝔭‖ ≤ 1)
    (hs : 1 ≤ s.re) {σ : ℝ} (hσ : σ ≤ s.re) :
    ‖-log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)‖ ≤
      3 / 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ) := by
  rw [norm_neg, sub_eq_add_neg]
  refine (norm_log_one_add_half_le_self
    (by rw [norm_neg]; exact norm_div_absNorm_cpow_le_half ha hs)).trans ?_
  rw [norm_neg]
  refine mul_le_mul_of_nonneg_left ((norm_div_absNorm_cpow_le_rpow_neg ha).trans ?_) (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_two.trans (two_le_absNorm_asIdeal_real 𝔭)) (neg_le_neg hσ)

/-- **Convergence of the Euler product in exponential form.** For `Re s > 1` and `‖a‖ ≤ 1` the
product of the factors `(1 - a(𝔭) N(𝔭) ^ (-s))⁻¹` converges unconditionally to the exponential of
the sum of their principal logarithms. -/
theorem hasProd_exp_tsum_neg_log (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹)
      (exp (∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s))) := by
  have hsum := (summable_neg_log_one_sub_div_absNorm_cpow ha hs).neg
  simp only [neg_neg] at hsum
  have hprod := hasProd_of_hasSum_log
    (fun 𝔭 ↦ slitPlane_ne_zero (one_sub_div_absNorm_cpow_mem_slitPlane (ha 𝔭) hs.le)) hsum.hasSum
  rw [tsum_neg, exp_neg]
  exact hprod.inv₀ (exp_ne_zero _)

/-- **The Euler product converges** for `Re s > 1` and `‖a‖ ≤ 1`. -/
theorem hasProd_primeEulerProduct (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹)
      (primeEulerProduct a s) := by
  rw [primeEulerProduct_def, (hasProd_exp_tsum_neg_log ha hs).tprod_eq]
  exact hasProd_exp_tsum_neg_log ha hs

/-- **The Euler product as an exponential.** For `Re s > 1` and `‖a‖ ≤ 1`,
`P(a, s) = exp (∑_𝔭 -log (1 - a(𝔭) N(𝔭) ^ (-s)))`. -/
theorem primeEulerProduct_eq_exp (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    primeEulerProduct a s = exp (∑' 𝔭 : HeightOneSpectrum (𝓞 K),
      -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)) :=
  (hasProd_exp_tsum_neg_log ha hs).tprod_eq

/-- **The Euler product does not vanish** for `Re s > 1` and `‖a‖ ≤ 1`. -/
theorem primeEulerProduct_ne_zero (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re) :
    primeEulerProduct a s ≠ 0 := by
  rw [primeEulerProduct_eq_exp ha hs]
  exact exp_ne_zero _

/-- The sum of the logarithms of the Euler factors is continuous in real `s > 1`, by dominated
convergence against `∑_𝔭 3/2 N(𝔭) ^ (-σ)` for `1 < σ < s`. -/
theorem continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) :
    ContinuousOn (fun s : ℝ ↦ ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
      -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ))) (Set.Ioi 1) := by
  intro s₀ hs₀
  rw [Set.mem_Ioi] at hs₀
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs₀
  refine ContinuousAt.continuousWithinAt ?_
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun 𝔭 ↦ 3 / 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ))
    ((summable_absNorm_rpow_primes_of_one_lt hσ).mul_left _) (fun 𝔭 ↦ ?_) ?_
  · have hN : (Ideal.absNorm 𝔭.asIdeal : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭).ne_bot
    have hpow : Continuous fun t : ℝ ↦ (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (t : ℂ) :=
      continuous_ofReal.const_cpow (Or.inl hN)
    have hcont : ContinuousAt (fun t : ℝ ↦ 1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (t : ℂ))
        s₀ :=
      (continuous_const.sub (continuous_const.div hpow
        fun t ↦ cpow_ne_zero_iff.mpr (Or.inl hN))).continuousAt
    exact (hcont.clog (one_sub_div_absNorm_cpow_mem_slitPlane (ha 𝔭)
      (by rw [ofReal_re]; exact hs₀.le))).neg
  · filter_upwards [Ici_mem_nhds hσs] with t (ht : σ ≤ t) 𝔭
    exact norm_neg_log_one_sub_div_absNorm_cpow_le (ha 𝔭) (by rw [ofReal_re]; linarith)
      (by rwa [ofReal_re])

/-- **The Euler product is continuous** in real `s > 1`, as the exponential of the continuous sum
of the logarithms of its factors. -/
theorem continuousOn_primeEulerProduct (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) :
    ContinuousOn (fun s : ℝ ↦ primeEulerProduct a s) (Set.Ioi 1) :=
  (continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow ha).cexp.congr fun s (hs : 1 < s) ↦
    primeEulerProduct_eq_exp ha (by rwa [ofReal_re])

/-- **A bound for the Euler product depending only on `K`.** For `Re s ≥ 2` and `‖a‖ ≤ 1`,
`|log ‖P(a, s)‖| ≤ 3 [K : ℚ]`: each logarithm has modulus at most `3/2 N(𝔭) ^ (-2)`, and
`∑_𝔭 N(𝔭) ^ (-2) ≤ [K : ℚ]`. -/
theorem abs_log_norm_primeEulerProduct_le (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 2 ≤ s.re) :
    |Real.log ‖primeEulerProduct a s‖| ≤ 3 * Module.finrank ℚ K := by
  have hs1 : 1 < s.re := one_lt_two.trans_le hs
  have hsum2 := summable_absNorm_rpow_primes_of_one_lt (K := K) one_lt_two
  -- each logarithm is bounded by `3/2 N(𝔭) ^ (-2)`
  have hbound := tsum_of_norm_bounded (hsum2.mul_left (3 / 2)).hasSum
    fun 𝔭 ↦ norm_neg_log_one_sub_div_absNorm_cpow_le (ha 𝔭) hs1.le hs
  rw [tsum_mul_left] at hbound
  rw [primeEulerProduct_eq_exp ha hs1, norm_exp, Real.log_exp]
  calc |(∑' 𝔭 : HeightOneSpectrum (𝓞 K),
          -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)).re|
      ≤ ‖∑' 𝔭 : HeightOneSpectrum (𝓞 K),
          -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)‖ := abs_re_le_norm _
    _ ≤ 3 / 2 * Module.finrank ℚ K :=
        hbound.trans (mul_le_mul_of_nonneg_left tsum_absNorm_rpow_neg_two_le (by norm_num))
    _ ≤ 3 * Module.finrank ℚ K := by
        have : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
        linarith

/-- **Deleting finitely many Euler factors.** For `Re s > 1`, `‖a‖ ≤ 1` and a finite set `Q` of
primes, setting the coefficients at `Q` to zero divides the Euler product by the factors at `Q`:
`P(a 1_{Qᶜ}, s) · ∏_{𝔭 ∈ Q} (1 - a(𝔭) N(𝔭) ^ (-s))⁻¹ = P(a, s)`. -/
theorem primeEulerProduct_indicator_compl_mul_prod (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) (hs : 1 < s.re)
    (Q : Finset (HeightOneSpectrum (𝓞 K))) :
    primeEulerProduct ((Q : Set (HeightOneSpectrum (𝓞 K)))ᶜ.indicator a) s *
        ∏ 𝔭 ∈ Q, (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹ =
      primeEulerProduct a s := by
  classical
  set g : HeightOneSpectrum (𝓞 K) → ℂ := fun 𝔭 ↦ (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)⁻¹
  have ha' (𝔭 : HeightOneSpectrum (𝓞 K)) :
      ‖(Q : Set (HeightOneSpectrum (𝓞 K)))ᶜ.indicator a 𝔭‖ ≤ 1 :=
    (norm_indicator_le_norm_self a 𝔭).trans (ha 𝔭)
  -- the factors at `Q`, and `1` elsewhere
  have hQ : HasProd ((Q : Set (HeightOneSpectrum (𝓞 K))).mulIndicator g) (∏ 𝔭 ∈ Q, g 𝔭) := by
    have h : HasProd ((Q : Set (HeightOneSpectrum (𝓞 K))).mulIndicator g)
        (∏ 𝔭 ∈ Q, (Q : Set (HeightOneSpectrum (𝓞 K))).mulIndicator g 𝔭) :=
      hasProd_prod_of_ne_finset_one fun 𝔭 h𝔭 ↦
        Set.mulIndicator_of_notMem (Finset.mem_coe.not.mpr h𝔭) g
    rwa [Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ Set.mulIndicator_of_mem (Finset.mem_coe.mpr h𝔭) g] at h
  refine ((hasProd_primeEulerProduct ha' hs).mul hQ).unique ?_
  convert hasProd_primeEulerProduct ha hs using 1
  funext 𝔭
  by_cases h𝔭 : 𝔭 ∈ (Q : Set (HeightOneSpectrum (𝓞 K)))
  · simp [g, h𝔭]
  · simp [g, h𝔭]

/-! ### Completely multiplicative coefficients -/

/-- The Euler-product data of a completely multiplicative function on the ideals of `𝓞 K`. -/
private noncomputable def eulerProductDataOf (χ : Ideal (𝓞 K) →*₀ ℂ) : EulerProductData K where
  toIdealArithmeticFunction := IdealArithmeticFunction.restrict χ
  isMultiplicative := ⟨by rw [IdealArithmeticFunction.restrict_apply, OneMemClass.coe_one, map_one],
    fun _ ↦ by simp⟩

/-- The local Euler factor of a completely multiplicative function is geometric. -/
private theorem eulerFactor_eulerProductDataOf (χ : Ideal (𝓞 K) →*₀ ℂ) (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (eulerProductDataOf χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum, ← tsum_geometric_of_norm_lt_one hP]
  refine tsum_congr fun e ↦ ?_
  rw [idealTerm_def]
  simp only [eulerProductDataOf, IdealArithmeticFunction.restrict_apply]
  rw [P.absNorm_primeIdealPow, P.coe_primeIdealPow, map_pow, Nat.cast_pow,
    ← natCast_cpow_natCast_mul, cpow_nat_mul, div_pow]

/-- **The Euler product of a completely multiplicative function.** For a completely
multiplicative `χ` on the ideals of `𝓞 K` with `‖χ‖ ≤ 1` and `Re s > 1`, the Dirichlet series
`∑_I χ(I) N(I) ^ (-s)` over the nonzero ideals sums to the Euler product with coefficients
`χ(𝔭)`. -/
theorem hasSum_primeEulerProduct (χ : Ideal (𝓞 K) →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ ↦ χ I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)
      (primeEulerProduct (fun 𝔭 ↦ χ 𝔭.asIdeal) s) := by
  set D := eulerProductDataOf χ
  have hsum : Summable (idealTerm K D.toIdealArithmeticFunction s) :=
    summable_idealTerm_of_bounded_of_one_lt_re (C := 1)
      (fun I ↦ by simpa [D, eulerProductDataOf] using hχ I) hs
  have hfac (P : HeightOneSpectrum (𝓞 K)) :
      D.eulerFactor P s = (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ :=
    eulerFactor_eulerProductDataOf χ P ((norm_div_absNorm_cpow_le_half
      (a := fun 𝔭 ↦ χ 𝔭.asIdeal) (hχ P.asIdeal) hs.le).trans_lt one_half_lt_one)
  have hprod := D.hasProd_eulerFactor hsum
  simp only [hfac] at hprod
  rw [(hasProd_primeEulerProduct (fun 𝔭 ↦ hχ 𝔭.asIdeal) hs).unique hprod,
    LSeries_normCoeff K hsum]
  exact hsum.hasSum.congr_fun fun I ↦ by
    simp [idealTerm_def, D, eulerProductDataOf]

end TauCeti
