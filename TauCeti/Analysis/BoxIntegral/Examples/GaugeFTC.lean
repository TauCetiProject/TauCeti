/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Oriented.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A conditionally integrable derivative

The primitive `t² sin(t⁻²)`, with value zero at zero, has Henstock–Kurzweil derivative integral
`sin 1` on the unit interval. Its oscillations accumulate infinite total variation at zero.
Non-Bochner-integrability follows from Mathlib's
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`: an integrable derivative
would force an absolutely continuous primitive, contradicting its infinite variation.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti.BoxIntegral.Examples

/-- The oscillatory primitive `t² sin(t⁻²)`, including its continuous value at zero. -/
def oscillatoryPrimitive (t : ℝ) : ℝ := t ^ 2 * Real.sin ((t ^ 2)⁻¹)

/-- The formula for the oscillatory primitive on all real parameters. -/
theorem oscillatoryPrimitive_apply (t : ℝ) :
    oscillatoryPrimitive t = t ^ 2 * Real.sin ((t ^ 2)⁻¹) := (rfl)

@[simp]
theorem oscillatoryPrimitive_zero : oscillatoryPrimitive 0 = 0 := by
  simp [oscillatoryPrimitive]

@[simp]
theorem oscillatoryPrimitive_one : oscillatoryPrimitive 1 = Real.sin 1 := by
  simp [oscillatoryPrimitive]

private theorem hasDerivAt_oscillatoryPrimitive_zero :
    HasDerivAt oscillatoryPrimitive 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply squeeze_zero_norm (a := fun t : ℝ ↦ ‖t‖)
  · intro t
    rw [slope_def_field, oscillatoryPrimitive_zero, sub_zero, sub_zero]
    by_cases ht : t = 0
    · simp [ht]
    have heq : oscillatoryPrimitive t / t = t * Real.sin ((t ^ 2)⁻¹) := by
      rw [oscillatoryPrimitive_apply]
      field_simp
    rw [heq, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((t ^ 2)⁻¹))
  · simpa using (continuous_norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- The canonical derivative exists everywhere, including the endpoint zero. -/
theorem hasDerivAt_oscillatoryPrimitive (t : ℝ) :
    HasDerivAt oscillatoryPrimitive
      (2 * t * Real.sin ((t ^ 2)⁻¹) - 2 * t⁻¹ * Real.cos ((t ^ 2)⁻¹)) t := by
  by_cases ht : t = 0
  · simpa only [ht, mul_zero, zero_mul, inv_zero, sub_zero] using
      hasDerivAt_oscillatoryPrimitive_zero
  have hpow : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).fun_pow 2
  convert hpow.fun_mul ((hpow.fun_inv (pow_ne_zero 2 ht)).sin) using 1
  · rfl
  · field_simp
    ring

/-- The derivative has Henstock–Kurzweil integral `sin 1` on the unit interval. -/
theorem hasHenstockIntervalIntegral_deriv_oscillatoryPrimitive :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (deriv oscillatoryPrimitive) 0 1
      (Real.sin 1) := by
  have hd (t : ℝ) : HasDerivAt oscillatoryPrimitive (deriv oscillatoryPrimitive t) t :=
    (hasDerivAt_oscillatoryPrimitive t).differentiableAt.hasDerivAt
  have hc : Continuous oscillatoryPrimitive := continuous_iff_continuousAt.mpr
    (fun t ↦ (hd t).continuousAt)
  simpa only [oscillatoryPrimitive_zero, oscillatoryPrimitive_one, sub_zero] using
    TauCeti.BoxIntegral.hasHenstockIntervalIntegral_of_hasDerivAt_off_countable
      (a := 0) (b := 1) (s := ∅) countable_empty hc.continuousOn (fun t _ ↦ hd t)

/-- The same conditional derivative has the negative gauge value on the reversed interval. -/
theorem hasHenstockIntervalIntegral_deriv_oscillatoryPrimitive_reverse :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (deriv oscillatoryPrimitive) 1 0
      (-Real.sin 1) :=
  hasHenstockIntervalIntegral_deriv_oscillatoryPrimitive.symm

/-- The primitive is strictly positive at the endpoint one. -/
theorem oscillatoryPrimitive_one_pos : 0 < oscillatoryPrimitive 1 := by
  rw [oscillatoryPrimitive_one]
  exact Real.sin_pos_of_pos_of_lt_pi zero_lt_one (by linarith [Real.two_le_pi])

private def phase (n : ℕ) : ℝ := (n + 1 : ℕ) * Real.pi + Real.pi / 2

private theorem phase_pos (n : ℕ) : 0 < phase n := by
  dsimp [phase]
  positivity

private def sampleTime (n : ℕ) : ℝ := (Real.sqrt (phase n))⁻¹

private theorem sampleTime_mem (n : ℕ) : sampleTime n ∈ Icc (0 : ℝ) 1 := by
  have hp : 1 ≤ phase n := by
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    dsimp [phase]
    nlinarith [Real.two_le_pi]
  have hs : 1 ≤ Real.sqrt (phase n) := (Real.one_le_sqrt).mpr hp
  exact ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), by
    simpa only [one_div, inv_one, sampleTime] using
      one_div_le_one_div_of_le zero_lt_one hs⟩

private theorem sampleTime_antitone : Antitone sampleTime := by
  intro i j hij
  have hp : phase i ≤ phase j := by
    dsimp [phase]
    have h : ((i + 1 : ℕ) : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hij 1
    exact add_le_add (mul_le_mul_of_nonneg_right h Real.pi_pos.le) le_rfl
  simpa only [one_div, sampleTime] using
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (phase_pos i)) (Real.sqrt_le_sqrt hp)

private theorem oscillatoryPrimitive_sampleTime (n : ℕ) :
    oscillatoryPrimitive (sampleTime n) = (phase n)⁻¹ * (-1) ^ (n + 1) := by
  have hsq : sampleTime n ^ 2 = (phase n)⁻¹ := by
    rw [sampleTime, inv_pow, Real.sq_sqrt (phase_pos n).le]
  rw [oscillatoryPrimitive_apply, hsq, inv_inv]
  rw [phase, add_comm, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]

private theorem amplitude_le_sample_increment (n : ℕ) :
    (phase n)⁻¹ ≤
      ‖oscillatoryPrimitive (sampleTime (n + 1)) - oscillatoryPrimitive (sampleTime n)‖ := by
  have heq : oscillatoryPrimitive (sampleTime (n + 1)) - oscillatoryPrimitive (sampleTime n) =
      (-1) ^ (n + 1) * -((phase (n + 1))⁻¹ + (phase n)⁻¹) := by
    rw [oscillatoryPrimitive_sampleTime, oscillatoryPrimitive_sampleTime, pow_succ]
    ring
  rw [heq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_neg,
    Real.norm_eq_abs, abs_of_nonneg (add_nonneg (inv_nonneg.mpr (phase_pos _).le)
      (inv_nonneg.mpr (phase_pos _).le))]
  exact le_add_of_nonneg_left (inv_nonneg.mpr (phase_pos _).le)

private theorem scaled_harmonic_le_sample_increment (n : ℕ) :
    (2 * Real.pi)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹ ≤
      ‖oscillatoryPrimitive (sampleTime (n + 1)) - oscillatoryPrimitive (sampleTime n)‖ := by
  have hp : phase n ≤ (2 * Real.pi) * (n + 1 : ℕ) := by
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    dsimp [phase]
    nlinarith [Real.pi_pos]
  have h := one_div_le_one_div_of_le (phase_pos n) hp
  have h' : (2 * Real.pi)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (phase n)⁻¹ := by
    simpa only [one_div, mul_inv_rev, mul_comm] using h
  exact h'.trans (amplitude_le_sample_increment n)

/-- The oscillatory primitive has infinite total variation on the unit interval. -/
theorem not_boundedVariationOn_oscillatoryPrimitive :
    ¬BoundedVariationOn oscillatoryPrimitive (Icc (0 : ℝ) 1) := by
  intro hBV
  let V := (eVariationOn oscillatoryPrimitive (Icc (0 : ℝ) 1)).toReal
  have hvar : eVariationOn (oscillatoryPrimitive ∘ sampleTime) (univ : Set ℕ) ≤
      eVariationOn oscillatoryPrimitive (Icc (0 : ℝ) 1) :=
    eVariationOn.comp_le_of_antitoneOn oscillatoryPrimitive sampleTime
      (sampleTime_antitone.antitoneOn _) (fun n _ ↦ sampleTime_mem n)
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N,
        ‖oscillatoryPrimitive (sampleTime (n + 1)) - oscillatoryPrimitive (sampleTime n)‖) ≤ V := by
    have h := (eVariationOn.sum_le (f := oscillatoryPrimitive ∘ sampleTime)
      (n := N) (u := id) monotone_id (fun n ↦ mem_univ n)).trans hvar
    have hr := ENNReal.toReal_mono hBV h
    rw [ENNReal.toReal_sum (fun _ _ ↦ edist_ne_top _ _)] at hr
    simp only [Function.comp_apply, id_eq, edist_dist, dist_eq_norm] at hr
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hr
  have hH (N : ℕ) : (harmonic N : ℝ) ≤ (2 * Real.pi) * V := by
    have hh := (Finset.sum_le_sum (fun n _ ↦ scaled_harmonic_le_sample_increment n)).trans (hsum N)
    have heq : ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ = (harmonic N : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Finset.mul_sum, heq] at hh
    exact (inv_mul_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp hh
  have hlim : Tendsto (fun N : ℕ ↦ Real.log (N + 1 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_gt_atTop ((2 * Real.pi) * V))).exists
  exact (not_lt_of_ge ((log_add_one_le_harmonic N).trans (hH N))) hN

/-- Although its gauge integral exists, the derivative of `t² sin(t⁻²)` is not Bochner integrable
on the unit interval. -/
theorem not_intervalIntegrable_deriv_oscillatoryPrimitive :
    ¬IntervalIntegrable (deriv oscillatoryPrimitive) volume 0 1 := by
  intro hi
  have hAC := hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hEq : EqOn (fun t ↦ ∫ x in (0 : ℝ)..t, deriv oscillatoryPrimitive x)
      oscillatoryPrimitive (uIcc (0 : ℝ) 1) := by
    intro t ht
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ (hasDerivAt_oscillatoryPrimitive x).differentiableAt.hasDerivAt)
      (hi.mono_set (uIcc_subset_uIcc left_mem_uIcc ht))
    simpa only [oscillatoryPrimitive_zero, sub_zero] using h
  have h := (hAC.congr hEq).boundedVariationOn
  rw [uIcc_of_le zero_le_one] at h
  exact not_boundedVariationOn_oscillatoryPrimitive h

end TauCeti.BoxIntegral.Examples
