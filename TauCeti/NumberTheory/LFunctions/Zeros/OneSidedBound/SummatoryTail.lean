/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.Chebyshev.ResidueClass
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ResidueClass
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Summatory tails for the signed prime remainder

The remainder `R_q(y)` is the negative integral over `(y, ∞)` of the summatory error of the
Legendre-weighted von Mangoldt coefficients against `dt / t²`, when that error is absolutely
integrable against this weight. In particular, the subtraction of `Re G_q(1)` in `R_q` removes
exactly the constant at infinity. The tail identity transfers estimates for the unsmoothed
summatory error to the remainder at a large cutoff.

The normalization is that of `New.primeRemainder` in `grh/src/New/Reduction/Zeros/PrimeError.lean`
in [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Complex DirichletCharacter Filter MeasureTheory Set
open scoped Finset Topology

namespace TauCeti.OneSidedBound

variable {d q : ℕ} [Fact d.Prime] [NeZero q]

open Classical in
private theorem sum_logDeriv_entireLFunction_eq (s : ℂ) :
    ∑ ψ : DirichletCharacter ℂ q, logDeriv ψ.entireLFunction s =
      logDeriv (LFunctionTrivChar₁ q) s +
        ∑ ψ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), logDeriv ψ.LFunction s := by
  classical
  rw [← Finset.sum_add_sum_compl ({1} : Finset (DirichletCharacter ℂ q))]
  simp only [Finset.sum_singleton, entireLFunction_one]
  congr 1
  exact Finset.sum_congr rfl fun ψ hψ ↦ by
    rw [entireLFunction_of_ne_one (by simpa using hψ)]

private theorem logDeriv_mul_quadraticChar_eq (ψ : DirichletCharacter ℂ q)
    (hcond : ¬ conductor ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) ∣ q) :
    have : NeZero (q.lcm d) := ⟨fun h ↦ NeZero.ne q (Nat.lcm_eq_zero_iff.mp h |>.resolve_right
      (Fact.out : d.Prime).ne_zero)⟩
    have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    logDeriv (ψ.mul ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))).LFunction 1 =
      logDeriv (quadraticTwist d ψ).entireLFunction 1 := by
  let ξ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  have hcop : q.Coprime d := ((Fact.out : d.Prime).coprime_iff_not_dvd.mpr
    (fun hdq ↦ hcond (ξ.conductor_dvd_level.trans hdq))).symm
  have htw : ∀ (m : ℕ) [NeZero m] (h : q.lcm d = m),
      logDeriv (ψ.mul ξ).LFunction 1 =
        logDeriv (changeLevel (h ▸ Nat.dvd_lcm_left q d) ψ *
          changeLevel (h ▸ Nat.dvd_lcm_right q d) ξ).entireLFunction 1 := by
    intro m hm h
    subst m
    have hne : ψ.mul ξ ≠ 1 :=
      fun h ↦ hcond ((ξ.exists_mul_eq_one_iff_conductor_dvd (q := q)).mp ⟨ψ, h⟩)
    rw [← entireLFunction_of_ne_one hne, DirichletCharacter.mul]
  rw [quadraticTwist_def]
  exact htw (q * d) hcop.lcm_eq_mul

/-- The boundary value in the signed remainder is the right-hand limit of the compensated
Dirichlet series of its coefficients. -/
private theorem tendsto_compensated_primeWeight (hd : d ≠ 2) (hdq : ¬ d ∣ q) :
    (∀ᶠ σ : ℝ in 𝓝[>] 1, LSeriesSummable (fun n ↦ (primeWeight d q n : ℂ)) (σ : ℂ)) ∧
    Tendsto (fun σ : ℝ ↦ LSeries (fun n ↦ (primeWeight d q n : ℂ)) (σ : ℂ) -
      (q.totient : ℂ)⁻¹ * σ / ((σ : ℂ) - 1)) (𝓝[>] 1) (𝓝 (logDerivMean d q 1)) := by
  classical
  have hp : d.Prime := Fact.out
  let : NeZero d := ⟨hp.ne_zero⟩
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) hp.ne_zero⟩
  let ξ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  have hξ : ¬ ξ.conductor ∣ q := by
    have h := conductor_changeLevel_quadraticChar (p := d) (R := ℂ) (by simp) hd (dvd_refl d)
    rw [changeLevel_self] at h
    exact fun hdiv ↦ hdq (h ▸ hdiv)
  let F (s : ℂ) := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod q) s +
    (q.totient : ℂ)⁻¹ * (∑ ψ : DirichletCharacter ℂ q,
      ψ (1 : ZMod q)⁻¹ * logDeriv (ψ.mul ξ).LFunction s) - (q.totient : ℂ)⁻¹
  have hs {s : ℂ} (hre : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s
        (s / ((q.totient : ℂ) * (s - 1)) + F s) := by
    have h := ArithmeticFunction.vonMangoldt.LSeriesHasSum_residueClass_mul_one_sub
      (isUnit_one : IsUnit (1 : ZMod q)) ξ hre
    refine (LSeriesHasSum_congr s _ ?_).mp h
    intro n _
    by_cases hn : (n : ZMod q) = 1 <;>
      simp [primeWeight_def, ArithmeticFunction.vonMangoldt.residueClass, ξ,
        MulChar.ringHomComp_apply, legendreSym, hn]
  have hF : AnalyticAt ℂ F 1 :=
    ArithmeticFunction.vonMangoldt.analyticAt_residueClass_mul_one_sub_logDeriv_one _ ξ hξ
  have hlim : Tendsto (fun σ : ℝ ↦ F (σ : ℂ)) (𝓝[>] 1) (𝓝 (F 1)) := by
    exact (hF.continuousAt.tendsto.comp (continuous_ofReal.tendsto (1 : ℝ))).mono_left
      nhdsWithin_le_nhds
  have hval : F 1 = logDerivMean d q 1 := by
    -- Coprimality identifies the least-common-multiple level with the product level.
    have he (ψ : DirichletCharacter ℂ q) : logDeriv (ψ.mul ξ).LFunction 1 =
        logDeriv (quadraticTwist d ψ).entireLFunction 1 := logDeriv_mul_quadraticChar_eq ψ hξ
    rw [logDerivMean_def, Finset.sum_sub_distrib, sum_logDeriv_entireLFunction_eq]
    simp only [F, ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux, ZMod.inv_one,
      MulChar.map_one, one_mul, he]
    simp only [logDeriv_apply, div_eq_mul_inv]
    ring
  constructor
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact (hs (by simpa using hσ)).LSeriesSummable
  · rw [← hval]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [(hs (by simpa using hσ)).LSeries_eq, div_mul_eq_div_div, mul_comm _ (σ : ℂ),
      div_eq_mul_inv (σ : ℂ) (q.totient : ℂ), add_sub_cancel_left]

private theorem not_integrableOn_of_primeWeight_sum_small
    (hsmall : ∀ᶠ t : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n ≤ (q.totient : ℝ)⁻¹ / 2 * t) :
    ¬ IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) -
      (q.totient : ℝ)⁻¹ * t) / t ^ 2) (Ioi 1) := by
  intro hE
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hsmall.and (eventually_ge_atTop (1 : ℝ)))
  have hc : 0 < (q.totient : ℝ)⁻¹ / 2 := by
    have hq : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
    positivity
  have hmajor : IntegrableOn (fun t : ℝ ↦ ((q.totient : ℝ)⁻¹ / 2) • t⁻¹) (Ioi a) := by
    refine Integrable.mono (hE.mono_set (Ioi_subset_Ioi (ha a le_rfl).2))
      ((measurable_id.inv.const_smul ((q.totient : ℝ)⁻¹ / 2)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ⟨hsmall', ht₁⟩ := ha t (le_of_lt ht)
    have ht₀ := zero_lt_one.trans_le ht₁
    simp only [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_pos hc, abs_inv, abs_of_pos ht₀]
    refine le_trans ?_ (neg_le_abs _)
    rw [← neg_div, neg_sub, ← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos ht₀)]
    calc (q.totient : ℝ)⁻¹ / 2 / t * t ^ 2 = (q.totient : ℝ)⁻¹ / 2 * t := by
           field_simp
         _ ≤ (q.totient : ℝ)⁻¹ * t - ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n := by
           linarith
  exact not_integrableOn_Ioi_inv ((integrable_smul_iff hc.ne' (fun t : ℝ ↦ t⁻¹)).mp hmajor)

omit [NeZero q] in
private theorem primeWeight_eq_zero_of_dvd_level (hdq : d ∣ q) (n : ℕ) :
    primeWeight d q n = 0 := by
  by_cases hn : (n : ZMod q) = 1
  · have hnd : (n : ZMod d) = 1 := by
      have hm := congrArg (ZMod.castHom hdq (ZMod d)) hn
      rw [map_one, ZMod.castHom_apply, ZMod.cast_natCast hdq] at hm
      exact hm
    simp [primeWeight_def, hn, legendreSym, hnd]
  · simp [primeWeight_def, hn]

omit [NeZero q] in
private theorem sum_primeWeight_two_le_log {t : ℝ} (ht : 1 ≤ t) :
    ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight 2 q n ≤ Real.log t := by
  refine le_trans (b := Chebyshev.psiAP 2 0 t) ?_ (Chebyshev.psiAP_zero_le_log Nat.prime_two ht)
  rw [Chebyshev.psiAP_def, Finset.sum_filter, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  by_cases hn : (n : ZMod 2) = 0
  · simp only [primeWeight_def, legendreSym, Int.cast_natCast, hn, quadraticChar_zero,
      Int.cast_zero, sub_zero, mul_one, ite_true]
    split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  · simp [primeWeight_def, legendreSym, hn,
      quadraticChar_eq_one_of_char_two (ZMod.ringChar_zmod_n 2) hn]

private theorem primeRemainder_eq_neg_integral_tail_of_one_le
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) -
      (q.totient : ℝ)⁻¹ * t) / t ^ 2) (Ioi 1)) {y : ℝ} (hy : 1 ≤ y) :
    primeRemainder d q y = -(∫ t in Ioi y,
      ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2) := by
  have he (t : ℝ) : ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (primeWeight d q n : ℂ)) -
      (q.totient : ℂ)⁻¹ * t) / (t : ℂ) ^ 2 =
      (((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2 : ℝ) := by
    push_cast
    rfl
  have hEc : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (primeWeight d q n : ℂ)) -
      (q.totient : ℂ)⁻¹ * t) / (t : ℂ) ^ 2) (Ioi 1) := by
    simp_rw [he]
    exact hE.ofReal
  have hdq : ¬ d ∣ q := by
    intro hdiv
    apply not_integrableOn_of_primeWeight_sum_small (d := d) (q := q) _ hE
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [primeWeight_eq_zero_of_dvd_level hdiv, Finset.sum_const_zero]
    positivity
  have hd : d ≠ 2 := by
    rintro rfl
    apply not_integrableOn_of_primeWeight_sum_small (d := 2) (q := q) _ hE
    have hq : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
    filter_upwards [Real.isLittleO_log_id_atTop.bound (c := (q.totient : ℝ)⁻¹ / 2) (by positivity),
      eventually_ge_atTop (1 : ℝ)] with t ht ht₁
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht₁)] at ht
    exact (sum_primeWeight_two_le_log (q := q) ht₁).trans ((le_abs_self _).trans ht)
  obtain ⟨hs, hc⟩ := tendsto_compensated_primeWeight (q := q) hd hdq
  have h := rieszSum_div_sub_log_sub_eq_neg_integral_of_tendsto hs hEc hc hy
  simp_rw [he, integral_complex_ofReal] at h
  have hsum : rieszSum (fun n ↦ (primeWeight d q n : ℂ)) y / (y : ℂ) =
      ((∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) : ℝ) : ℂ) := by
    rw [rieszSum_def, Finset.sum_div, ofReal_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    push_cast
    field_simp [ofReal_ne_zero.mpr (zero_lt_one.trans_le hy).ne']
  rw [hsum] at h
  simpa only [primeRemainder_def, sub_re, neg_re, ofReal_re, ← ofReal_natCast,
    ← ofReal_log, ← ofReal_inv, ← ofReal_mul, div_eq_inv_mul] using congrArg Complex.re h

/-- The signed prime remainder at a positive cutoff is minus the tail of the summatory
error weighted by `t⁻²`, provided the weighted error is absolutely integrable on `(1, ∞)`. -/
theorem primeRemainder_eq_neg_integral_tail
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) -
      (q.totient : ℝ)⁻¹ * t) / t ^ 2) (Ioi 1)) {y : ℝ} (hy : 0 < y) :
    primeRemainder d q y = -(∫ t in Ioi y,
      ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2) := by
  rcases le_or_gt 1 y with hy₁ | hy₁
  · exact primeRemainder_eq_neg_integral_tail_of_one_le hE hy₁
  let E (t : ℝ) := ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2
  have hfloor : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy₁
  have hzero (t : ℝ) (ht : t ∈ Ioc y 1) : E t = -(q.totient : ℝ)⁻¹ * t⁻¹ := by
    have hsum : ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n = 0 := by
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hn₁ : n = 1 := by
        have h := Finset.mem_Icc.mp hn
        have := Nat.floor_le_floor ht.2
        simp only [Nat.floor_one] at this
        omega
      simp [hn₁, primeWeight_def]
    dsimp only [E]
    rw [hsum]
    field_simp [(hy.trans ht.1).ne']
    ring
  have hi : IntervalIntegrable E volume y 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy₁.le]
    refine IntegrableOn.congr_fun ?_ (fun t ht ↦ (hzero t ht).symm) measurableSet_Ioc
    have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc y 1) :=
      continuousOn_id.inv₀ fun _ ht ↦ (hy.trans_le ht.1).ne'
    exact (hc.const_mul _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail := intervalIntegral.integral_interval_add_Ioi' hi hE
  have h₁ := primeRemainder_eq_neg_integral_tail_of_one_le hE le_rfl
  have hbetween : (∫ t in y..1, E t) = (q.totient : ℝ)⁻¹ * Real.log y := by
    rw [intervalIntegral.integral_of_le hy₁.le, setIntegral_congr_fun measurableSet_Ioc hzero,
      ← intervalIntegral.integral_of_le hy₁.le, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hy zero_lt_one, Real.log_div one_ne_zero hy.ne', Real.log_one]
    ring
  refine Eq.trans ?_ (congrArg Neg.neg htail)
  rw [hbetween, primeRemainder_def, hfloor, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
    Finset.sum_empty]
  have hc₁ : primeRemainder d q 1 = -(logDerivMean d q 1).re := by
    simp [primeRemainder_def]
  rw [hc₁, neg_inj] at h₁
  dsimp only [E]
  rw [div_eq_inv_mul (Real.log y), h₁]
  ring

/-- Absolute integrability of the weighted summatory error makes the signed prime remainder
converge to zero at infinity. -/
theorem tendsto_primeRemainder (hE : IntegrableOn (fun t : ℝ ↦
    ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2) (Ioi 1)) :
    Tendsto (primeRemainder d q) atTop (𝓝 0) := by
  have ht := (tendsto_integral_Ioi_zero (μ := volume) (f := fun t : ℝ ↦
    ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, primeWeight d q n) - (q.totient : ℝ)⁻¹ * t) / t ^ 2)
    tendsto_id).neg
  rw [neg_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (primeRemainder_eq_neg_integral_tail hE hy).symm

end TauCeti.OneSidedBound
