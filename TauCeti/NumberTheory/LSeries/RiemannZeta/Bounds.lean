/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# Partial-summation continuation and growth of the Riemann zeta function on `Re s > 0`

On `Re s > 1`, partial summation of `∑ n⁻ˢ` gives
`ζ(s) = s / (s - 1) - s ∫_1^∞ {t} t ^ (-(s + 1)) dt`, where `{t} = t - ⌊t⌋₊` is bounded between
`0` and `1`. Because the fractional-part integral is holomorphic on the whole open right half-plane
`Re s > 0`, analytic continuation extends this formula to all `s` with `Re s > 0` and `s ≠ 1`,
yielding the explicit vertical-growth bound `‖ζ(s)‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / Re s` for all
`Re s > 0` (including at `s = 1`, where `‖ζ(1)‖ = |(γ - log(4π)) / 2| < 1`).

## Main results

* `TauCeti.riemannZeta_eq_div_sub_mul_integral`: partial-summation representation of `ζ(s)` on
  `Re s > 0`, `s ≠ 1`.
* `TauCeti.norm_riemannZeta_le_of_re_pos`: `‖ζ(s)‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / Re s` for `Re s > 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 12 and Chapter 21.
-/

public section

open Complex Filter Finset MeasureTheory Asymptotics
open scoped Topology

namespace TauCeti

private lemma norm_sub_natFloor_le_one {t : ℝ} (ht : 0 ≤ t) : ‖(t : ℂ) - ⌊t⌋₊‖ ≤ 1 := by
  have hcast : (t : ℂ) - ⌊t⌋₊ = ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (Nat.floor_le ht))]
  linarith [Nat.lt_floor_add_one t]

private lemma differentiableOn_mellin_fract :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} := by
  let φ : ℝ → ℂ := (Set.Ioi 1).indicator fun t ↦ (t : ℂ) - ⌊t⌋₊
  have hφ_norm (t : ℝ) : ‖φ t‖ ≤ 1 := by
    dsimp only [φ]
    by_cases h1 : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem h1]
      exact norm_sub_natFloor_le_one (zero_lt_one.trans h1).le
    · rw [Set.indicator_of_notMem h1, norm_zero]
      exact zero_le_one
  have hmeas : Measurable φ :=
    (measurable_ofReal.sub
      ((measurable_of_countable (Nat.cast : ℕ → ℂ)).comp Nat.measurable_floor)).indicator
      measurableSet_Ioi
  have hloc : LocallyIntegrableOn φ (Set.Ioi 0) :=
    ((memLp_top_of_bound hmeas.aestronglyMeasurable 1
      (Eventually.of_forall hφ_norm)).locallyIntegrable le_top).locallyIntegrableOn _
  have htop : φ =O[atTop] (· ^ (-(0 : ℝ))) :=
    isBigO_iff.mpr ⟨1, Eventually.of_forall fun t ↦ by simpa using hφ_norm t⟩
  have hbot (b : ℝ) : φ =O[𝓝[>] 0] (· ^ (-b)) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (Set.indicator_of_notMem (Set.notMem_Ioi.mpr ht.2.le) _).symm
  have hm_eq (z : ℂ) :
      ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(z + 1)) = mellin φ (-z) := by
    dsimp only [φ]
    rw [mellin_indicator_Ioi _ zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [smul_eq_mul, mul_comm, neg_add']
  intro s hs
  have hm : DifferentiableAt ℂ (fun z : ℂ ↦ mellin φ (-z)) s :=
    (mellin_differentiableAt_of_isBigO_rpow hloc htop (by simpa using hs)
      (hbot (-s.re - 1)) (by simp)).comp s differentiableAt_id.neg
  exact hm.differentiableWithinAt.congr (fun z _ ↦ hm_eq z) (hm_eq s)

private lemma integral_fract_eq_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(z + 1)) =
      (z - 1)⁻¹ - z⁻¹ * riemannZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hO : (fun n : ℕ ↦ ∑ _k ∈ Icc 1 n, (1 : ℂ)) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) :=
    isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ by simp⟩
  have hint1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-z)) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint2 : IntegrableOn (fun t : ℝ ↦ (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) := by
    simpa using LSeries.integrableOn_sum_mul_cpow_of_isBigO (1 : ℕ → ℂ) hO hz
  have hcongr : Set.EqOn (fun t : ℝ ↦ ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(z + 1)))
      (fun t : ℝ ↦ (t : ℂ) ^ (-z) - (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    dsimp only
    rw [sub_mul]
    congr 1
    have hpow : (t : ℂ) ^ (1 + -(z + 1)) = (t : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
      rw [cpow_add _ _ ht0, cpow_one]
    rw [← hpow]
    congr 1
    ring
  have hL := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hz
    (LSeriesSummable_one_iff.mpr hz) hO
  rw [LSeries_one_eq_riemannZeta hz] at hL
  have hfloor :
      ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)) = z⁻¹ * riemannZeta z := by
    have hL' :
        riemannZeta z = z * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
      simpa using hL
    rw [hL', inv_mul_cancel_left₀ hz0]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub hint1 hint2, hfloor,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  simp only [ofReal_one, one_cpow]
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
  have hz1' : -z + 1 ≠ 0 := fun h ↦ hz1 (by linear_combination -h)
  congr 1
  field_simp [sub_ne_zero.mpr hz1, hz1']
  ring

/-- **Partial-summation continuation of the Riemann zeta function.** On `Re s > 0`, `s ≠ 1`,
`ζ(s) = s / (s - 1) - s ∫_1^∞ (t - ⌊t⌋₊) t ^ (-(s + 1)) dt`. -/
theorem riemannZeta_eq_div_sub_mul_integral {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(s + 1)) := by
  let I : ℂ → ℂ := fun z ↦ ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(z + 1))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (fun z ↦ z - (z - 1) * (z * I z)) {z : ℂ | 0 < z.re} :=
    (differentiableOn_id.sub ((differentiableOn_id.sub_const 1).mul
      (differentiableOn_id.mul differentiableOn_mellin_fract))).analyticOnNhd hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have heq : (fun z ↦ z - (z - 1) * (z * I z)) =ᶠ[𝓝 (2 : ℂ)] riemannZeta₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    dsimp only [I]
    rw [integral_fract_eq_of_one_lt_re hz, riemannZeta_eq_inv_sub_mul hz1]
    field_simp [hsub, hz0]
    ring
  have h := hF.eqOn_of_preconnected_of_eventuallyEq hZ (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs
  dsimp only [I] at h
  rw [riemannZeta_eq_inv_sub_mul hs₁, ← h]
  field_simp [sub_ne_zero.mpr hs₁]

private lemma norm_riemannZeta_one_le_one : ‖riemannZeta 1‖ ≤ 1 := by
  have h4pi : (0 : ℝ) < 4 * Real.pi := by positivity
  have h4pi_eq : (4 : ℂ) * Real.pi = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
  have hcast : riemannZeta 1 =
      (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) := by
    rw [riemannZeta_one, h4pi_eq, ← ofReal_log h4pi.le]
    push_cast
    rfl
  rw [hcast, norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    div_le_one (by norm_num), abs_le]
  have hγ_lt := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ_gt := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15
  have hseq : Real.eulerMascheroniSeq 15 = (harmonic 15 : ℝ) - 4 * Real.log 2 := by
    have h16 : ((15 : ℝ) + 1) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
    rw [Real.eulerMascheroniSeq, Nat.cast_ofNat, h16, Real.log_pow, Nat.cast_ofNat]
  have hh15 : (3318 : ℝ) / 1000 < (harmonic 15 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog4pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', h4, Real.log_pow, Nat.cast_ofNat]
  have hlogpi : Real.log Real.pi < 1156 / 1000 := by
    have hle := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (Real.exp_pos 1))
    rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at hle
    have hdiv : Real.pi / Real.exp 1 < 1156 / 1000 := by
      rw [div_lt_iff₀ (Real.exp_pos 1)]
      linarith [Real.pi_lt_d4, Real.exp_one_gt_d9]
    linarith
  have hlog4pi_pos : 0 < Real.log (4 * Real.pi) :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  exact ⟨by linarith [Real.log_two_lt_d9], by linarith⟩

/-- **Right-half-plane bound for `riemannZeta`.** For every `s` with `Re s > 0`,
`‖ζ(s)‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / Re s`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · simpa using norm_riemannZeta_one_le_one
  rw [riemannZeta_eq_div_sub_mul_integral hs hs₁]
  have hint : ‖∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re := by
    calc
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (norm_sub_natFloor_le_one ht0.le)
      _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        ring
  calc
    ‖s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s / (s - 1)‖ + ‖s * ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) - ⌊t⌋₊) * (t : ℂ) ^ (-(s + 1))‖ :=
        norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
        rw [norm_div, norm_mul]
        gcongr
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by ring

end TauCeti
