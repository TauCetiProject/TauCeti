/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Northcott.Stieltjes
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation

/-!
# Stieltjes integration by parts and prime counting

The generic Northcott–Stieltjes construction and its measure and integral identities are in
`TauCeti.Order.Northcott.Stieltjes`. This module combines them with Abel summation to obtain
Stieltjes integration by parts. For prime counts of a number field it gives the identities
`π_S(x) = ∫_{(1, x]} dϑ_S(t) / log t` and `ϑ_S(x) = ∫_{(1, x]} log t dπ_S(t)` for every real `x`.

## Main definitions

* `TauCeti.primeThetaStieltjes` and `TauCeti.primeCountStieltjes`: the weighted and unweighted
  prime counts of a set of primes, as Stieltjes functions.

## Main results

* `TauCeti.setIntegral_Ioc_summatoryStieltjes_eq_sub_sub_integral`: Abel summation as Stieltjes
  integration by parts.
* `TauCeti.primeCount_eq_integral_primeThetaStieltjes` and
  `TauCeti.primeTheta_eq_integral_primeCountStieltjes`: `dπ_S = dϑ_S / log t` and
  `dϑ_S = log t dπ_S` in integrated form.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.0.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter
open scoped Topology NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-- **Abel summation as Stieltjes integration by parts.** For real cutoffs `a ≤ b` and a function
`g` with values in `ℝ` or `ℂ`, differentiable on `[a, b]` with integrable derivative,
`∫_{(a, b]} g dA = g(b) A(b) - g(a) A(a) - ∫_a^b g'(t) A(t) dt`, where `A = summatory N w`. -/
theorem setIntegral_Ioc_summatoryStieltjes_eq_sub_sub_integral {𝕜 : Type*} [RCLike 𝕜]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {g : ℝ → 𝕜} {a b : ℝ} (hab : a ≤ b)
    (hg_diff : ∀ t ∈ Icc a b, DifferentiableAt ℝ g t) (hg_int : IntegrableOn (deriv g) (Icc a b)) :
    ∫ t in Ioc a b, g t ∂(summatoryStieltjes N hw).measure =
      g b * summatory N w b - g a * summatory N w a -
        ∫ t in Ioc a b, deriv g t * summatory N w t := by
  have hcast (x : ℝ) : ((summatory N w x : ℝ) : 𝕜) = summatory N (fun i ↦ (w i : 𝕜)) x := by
    simp only [summatory_apply, RCLike.ofReal_sum]
  simp only [setIntegral_Ioc_summatoryStieltjes N hw g hab, RCLike.real_smul_eq_coe_mul, hcast]
  rcases le_or_gt 0 a with ha | ha
  · exact summatory_mul_eq_sub_sub_integral_mul N _ ha hab hg_diff hg_int
  -- Below `0` every summatory function vanishes, so the identity reduces to the one from `0`.
  have hN (i : ι) : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
  rw [summatory_eq_zero_of_lt N hN ha, summatory_eq_zero_of_lt N hN ha, mul_zero, sub_zero,
    sub_zero, summatory_mul_eq_sub_integral_mul_of_le N le_rfl hN _ b
      (fun t ht ↦ hg_diff t ⟨ha.le.trans ht.1, ht.2⟩) (hg_int.mono_set (Icc_subset_Icc_left ha.le))]
  congr 1
  refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet
    (Ioc_subset_Ioc_left ha.le) ?_).symm
  filter_upwards [volume.ae_ne 0] with t ht0 ht
  have ht_neg : t < 0 := lt_of_le_of_ne (not_lt.mp fun h ↦ ht.2 ⟨h, ht.1.2⟩) ht0
  rw [summatory_eq_zero_of_lt N hN ht_neg, mul_zero]

/-! ### The prime counts of a number field -/

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The logarithmically weighted prime count `ϑ_S` of a set `S` of primes, as a Stieltjes
function. -/
noncomputable def primeThetaStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) :
    StieltjesFunction ℝ :=
  summatoryStieltjes (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (w := S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ))
    (indicator_nonneg fun v _ ↦ log_absNorm_asIdeal_nonneg v)

variable (K) in
/-- The prime count `π_S` of a set `S` of primes, as a Stieltjes function. -/
noncomputable def primeCountStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) :
    StieltjesFunction ℝ :=
  summatoryStieltjes (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (w := S.indicator 1) (indicator_nonneg fun _ _ ↦ zero_le_one)

/-- The Stieltjes function `primeThetaStieltjes K S` evaluates to `ϑ_S`. -/
@[simp]
theorem primeThetaStieltjes_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeThetaStieltjes K S x = primeTheta K S x := by
  rw [primeThetaStieltjes, summatoryStieltjes_apply, primeTheta_apply, summatory_apply]

/-- The Stieltjes function `primeCountStieltjes K S` evaluates to `π_S`. -/
@[simp]
theorem primeCountStieltjes_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCountStieltjes K S x = primeCount K S x := by
  rw [primeCountStieltjes, summatoryStieltjes_apply, primeCount_apply, summatory_apply]

/-- Every prime has absolute norm greater than `1`, so integrals from `1` see every prime. -/
private theorem one_lt_absNorm_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ) < Ideal.absNorm v.asIdeal :=
  one_lt_two.trans_le (two_le_absNorm_asIdeal_real v)

/-- **`π_S` from `ϑ_S` as a Stieltjes integral:** `π_S(x) = ∫_{(1, x]} dϑ_S(t) / log t` for every
real cutoff `x`. -/
theorem primeCount_eq_integral_primeThetaStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∫ t in Ioc 1 x, (Real.log t)⁻¹ ∂(primeThetaStieltjes K S).measure := by
  rw [← primeCountStieltjes_apply, primeCountStieltjes, summatoryStieltjes_apply,
    primeThetaStieltjes, setIntegral_Ioc_summatoryStieltjes_of_lt _ _ _ one_lt_absNorm_asIdeal]
  refine congrArg (summatory _ · x) (funext fun v ↦ ?_)
  by_cases hv : v ∈ S
  · rw [indicator_of_mem hv, indicator_of_mem hv, Pi.one_apply, smul_eq_mul,
      mul_inv_cancel₀ (log_absNorm_asIdeal_pos v).ne']
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_smul]

/-- **`ϑ_S` from `π_S` as a Stieltjes integral:** `ϑ_S(x) = ∫_{(1, x]} log t dπ_S(t)` for every
real cutoff `x`. -/
theorem primeTheta_eq_integral_primeCountStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x = ∫ t in Ioc 1 x, Real.log t ∂(primeCountStieltjes K S).measure := by
  rw [← primeThetaStieltjes_apply, primeThetaStieltjes, summatoryStieltjes_apply,
    primeCountStieltjes, setIntegral_Ioc_summatoryStieltjes_of_lt _ _ _ one_lt_absNorm_asIdeal]
  refine congrArg (summatory _ · x) (funext fun v ↦ ?_)
  by_cases hv : v ∈ S
  · rw [indicator_of_mem hv, indicator_of_mem hv, Pi.one_apply, one_smul]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_smul]

end TauCeti
