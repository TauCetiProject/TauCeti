/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.ProjIcc
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
import TauCeti.NumberTheory.Mertens.Basic

/-!
# Prime harmonic sums on a logarithmic scale

`tendsto_sum_sdiff_primesLE_rpow_inv` computes the limiting mass on `(x ^ b, x ^ c]` by Mertens.
Via `FiniteMeasure.tendsto_iff_forall_integral_tendsto`,
`tendsto_sum_sdiff_primesLE_rpow_log_div` gives the limit against continuous functions of
`log p / log x`. The density `1 / t` occurs in the Dickman recursion (Hildebrand–Tenenbaum,
*Integers without large prime factors*, J. Théor. Nombres Bordeaux 5 (1993), 411–484).
-/

public section

open Filter Finset MeasureTheory Real Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace TauCeti

/-- The reciprocal sum over primes `x ^ b < p ≤ x ^ c` tends to `log (c / b)` for
`0 < b ≤ c`. -/
theorem tendsto_sum_sdiff_primesLE_rpow_inv {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    Tendsto (fun x : ℝ ↦
      ∑ p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊, (p : ℝ)⁻¹)
      atTop (𝓝 (log (c / b))) := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le
  have hpow := tendsto_rpow_atTop hb
  have hbound : Tendsto (fun x : ℝ ↦ C / log (x ^ b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp hpow)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [eventually_gt_atTop (1 : ℝ), hpow.eventually_ge_atTop 2] with x hx hxb
  have hx0 := zero_lt_one.trans hx
  have hratio : log (x ^ c) / log (x ^ b) = c / b := by
    rw [log_rpow hx0, log_rpow hx0, mul_div_mul_right _ _ (log_pos hx).ne']
  simpa only [Real.norm_eq_abs, hratio] using hC _ _ hxb (rpow_le_rpow_of_exponent_le hx.le hbc)

private noncomputable def primeAtom (x : ℝ) (p : ℕ) : FiniteMeasure ℝ :=
  ⟨Real.toNNReal ((p : ℝ)⁻¹) • Measure.dirac (log p / log x), inferInstance⟩

/-- The discrete harmonic measure of the primes in `(x ^ b, x ^ c]` on a logarithmic scale. -/
private noncomputable def primeMeasure (b c x : ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊, primeAtom x p

private theorem integral_primeMeasure (b c x : ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(primeMeasure b c x : Measure ℝ) =
      ∑ p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊, f (log p / log x) / (p : ℝ) := by
  rw [primeMeasure, FiniteMeasure.toMeasure_sum, integral_finsetSum_measure]
  · refine sum_congr rfl fun p _ ↦ ?_
    rw [primeAtom, FiniteMeasure.toMeasure_mk, integral_smul_nnreal_measure, integral_dirac]
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity),
      div_eq_inv_mul (f (log p / log x)) (p : ℝ)]
  · intro p _
    rw [primeAtom, FiniteMeasure.toMeasure_mk]
    exact (integrable_dirac (by finiteness)).smul_measure_nnreal

/-- The measure with density `1 / t` on the positive interval `(b,c]`. -/
private noncomputable def invMeasure {b : ℝ} (hb : 0 < b) (c : ℝ) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Ioc b c)).withDensity (fun t ↦ ENNReal.ofReal t⁻¹), by
    have h : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc b c) :=
      continuousOn_inv₀.mono fun _ ht ↦ (hb.trans_le ht.1).ne'
    exact isFiniteMeasure_withDensity_ofReal
      ((h.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self).2⟩

private theorem setIntegral_invMeasure {b c : ℝ} (hb : 0 < b)
    (f : ℝ → ℝ) (s : Set ℝ) :
    ∫ t in s, f t ∂(invMeasure hb c : Measure ℝ) = ∫ t in s ∩ Ioc b c, f t / t := by
  rw [invMeasure, FiniteMeasure.toMeasure_mk, setIntegral_withDensity_eq_setIntegral_toReal_smul'
    s (by fun_prop) (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict' measurableSet_Ioc]
  refine integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset inter_subset_right
    (ae_restrict_mem measurableSet_Ioc)).mono fun t ht ↦ ?_)
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (hb.trans ht.1).le), smul_eq_mul, div_eq_inv_mul]

/-- For `x > 1`, the prime cutoff `x ^ b < p ≤ x ^ c` becomes the logarithmic
cutoff `b < log p / log x ≤ c`. -/
theorem mem_sdiff_primesLE_rpow_iff {b c x : ℝ} {p : ℕ} (hx : 1 < x) :
    p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊ ↔
      p.Prime ∧ log p / log x ∈ Ioc b c := by
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  by_cases hp : p.Prime
  · have hx0 := zero_lt_one.trans hx
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [hp, true_and, not_le, Nat.le_floor_iff (rpow_nonneg hx0.le _), Set.mem_Ioc,
      lt_div_iff₀ (log_pos hx), div_le_iff₀ (log_pos hx), ← log_rpow hx0,
      log_lt_log_iff (rpow_pos_of_pos hx0 _) hp0, log_le_log_iff hp0 (rpow_pos_of_pos hx0 _),
      and_comm]
  · simp only [hp, and_false, false_and]

private theorem tendsto_primeMeasure {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Tendsto (primeMeasure b c) atTop (𝓝 (invMeasure hb c)) := by
  classical
  have htest (s : Set ℝ) (hs : MeasurableSet s) (d : ℝ) (hbd : b ≤ d)
      (hcut : s ∩ Ioc b c = Ioc b d) :
      Tendsto (fun x ↦ primeMeasure b c x s) atTop (𝓝 (invMeasure hb c s)) := by
    rw [← NNReal.tendsto_coe]
    simp only [← FiniteMeasure.measureReal_eq_coe_coeFn]
    have htarget : (invMeasure hb c : Measure ℝ).real s = log (d / b) := by
      rw [← mul_one ((invMeasure hb c : Measure ℝ).real s), ← smul_eq_mul, ← setIntegral_const]
      rw [setIntegral_invMeasure hb _ s, hcut, ← intervalIntegral.integral_of_le hbd,
        integral_one_div_of_pos hb (hb.trans_le hbd)]
    rw [htarget]
    refine (tendsto_sum_sdiff_primesLE_rpow_inv hb hbd).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    calc (∑ p ∈ Nat.primesLE ⌊x ^ d⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊, (p : ℝ)⁻¹) =
          ∑ p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊,
            s.indicator (fun _ ↦ (1 : ℝ)) (log p / log x) / (p : ℝ) := by
              have hfilter : (Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊).filter
                  (fun p : ℕ ↦ log p / log x ∈ s) =
                    Nat.primesLE ⌊x ^ d⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊ := by
                ext p
                simp only [mem_filter, mem_sdiff_primesLE_rpow_iff hx, ← hcut, mem_inter_iff]
                tauto
              rw [← hfilter, sum_filter]
              exact sum_congr rfl fun p _ ↦ by
                by_cases hp : log p / log x ∈ s <;> simp [hp, one_div]
      _ = (primeMeasure b c x : Measure ℝ).real s := by
        rw [← integral_primeMeasure, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
  have hclamp (d : ℝ) : Ioc b d = Ioc b (max b d) := by
    rw [← Ioc_union_Ioc_right, Set.Ioc_self, Set.empty_union]
  refine FiniteMeasure.tendsto_of_tendsto_mass_of_tendsto_Iic_rat
    (htest univ MeasurableSet.univ _ (le_max_left _ _) ((Set.univ_inter _).trans (hclamp c))) ?_
  intro q
  refine htest (Iic q) measurableSet_Iic (max b (min c q)) (le_max_left _ _) ?_
  rw [Set.inter_comm, Ioc_inter_Iic, ← hclamp]

/-- The harmonic prime sum on `x ^ b < p ≤ x ^ c` against a continuous test function of
`log p / log x` tends to its integral with density `1 / t` on `(b,c]`. -/
theorem tendsto_sum_sdiff_primesLE_rpow_log_div {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc b c)) :
    Tendsto (fun x : ℝ ↦
      ∑ p ∈ Nat.primesLE ⌊x ^ c⌋₊ \ Nat.primesLE ⌊x ^ b⌋₊, f (log p / log x) / (p : ℝ))
      atTop (𝓝 (∫ t in b..c, f t / t)) := by
  let g₀ := BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Icc b c ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let g : ℝ →ᵇ ℝ := g₀.compContinuous ⟨projIcc b c hbc, continuous_projIcc⟩
  have hg : EqOn g f (Icc b c) := fun t ht ↦ by
    simp only [g, g₀, BoundedContinuousFunction.compContinuous_apply,
      BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, projIcc_of_mem hbc ht]
    rfl
  have hlim := FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 (tendsto_primeMeasure hb c) g
  have htarget : ∫ t, g t ∂(invMeasure hb c : Measure ℝ) = ∫ t in b..c, f t / t := by
    rw [← setIntegral_univ, setIntegral_invMeasure hb g univ, Set.univ_inter,
      intervalIntegral.integral_of_le hbc]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ by
      rw [hg (Ioc_subset_Icc_self ht)]
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [integral_primeMeasure]
  exact sum_congr rfl fun p hp ↦ by
    rw [hg (Ioc_subset_Icc_self ((mem_sdiff_primesLE_rpow_iff hx).1 hp).2)]

end TauCeti
