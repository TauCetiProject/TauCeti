/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
public import TauCeti.Analysis.MellinTransform.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Growth bounds for Mellin tails with exponential decay

The tail over `(1, ∞)` of `u^R exp(-c u^α) du/u` converges for every real `R` and
`c, α > 0`, and is bounded by the positive Gamma moment at `(R+1)/α` when `R > -1`.
In particular this bound remains finite at `R = 0`. These estimates provide the quantitative
ingredient for the split Mellin method of proving order-one growth for completed L-functions.
On a half-plane `Re s ≤ R` the upper Mellin integral is bounded by the tail at the fixed
exponent `R`, independently of `Im s`; this gives boundedness on vertical strips.
A kernel continuous on `[1, ∞)` with an eventual bound `O(exp (-p u ^ α))` satisfies the
stretched-exponential bound `C exp (-p u ^ α)` on all of `[1, ∞)` (and `(1, ∞)`) that these
estimates take; more generally, for any kernel locally integrable on `(0, ∞)` whose exponential
bound holds only above an arbitrary threshold `T`, splitting `(1, ∞)` at `max 1 T` recovers
integrability, half-plane boundedness, and global `exp (C (1 + ‖s‖) log (2 + ‖s‖))` growth.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Real Set MeasureTheory Filter Topology Asymptotics

namespace TauCeti
/-- The exponentially decaying Mellin-tail majorant over `(1, ∞)` is integrable for every real
power. -/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_div {R c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    IntegrableOn (fun u : ℝ ↦ u ^ R * exp (-c * u ^ α) / u) (Ioi 1) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith [abs_nonneg R] : -1 < |R|) hα hc
  apply (hg.mono_set (Ioi_subset_Ioi zero_le_one)).mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun u : ℝ ↦ u ^ R * exp (-c * u ^ α) / u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      u ^ R * exp (-c * u ^ α) / u ≤ u ^ R * exp (-c * u ^ α) :=
        div_le_self (by positivity) (le_of_lt hu)
      _ ≤ u ^ |R| * exp (-c * u ^ α) := by
        gcongr
        · exact hu.le
        · exact le_abs_self R

/-- A Mellin-tail moment is bounded by the shifted Gamma moment for every exponent `R > -1`,
including exponent zero. -/
theorem integral_rpow_mul_exp_neg_mul_rpow_div_le_Gamma {R c α : ℝ}
    (hR : -1 < R) (hc : 0 < c) (hα : 0 < α) :
    (∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u) ≤
      c ^ (-(R + 1) / α) * Gamma ((R + 1) / α) / α := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow hR hα hc
  calc
    (∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u) ≤
        ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) := by
      apply setIntegral_mono_on (integrableOn_rpow_mul_exp_neg_mul_rpow_div hc hα)
        (hg.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
      intro u hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu
      exact div_le_self (by positivity) (le_of_lt hu)
    _ ≤ ∫ u in Ioi 0, u ^ R * exp (-c * u ^ α) := by
      apply setIntegral_mono_set hg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        positivity
      · exact Eventually.of_forall (fun u hu ↦ lt_trans zero_lt_one hu)
    _ = _ := by
      rw [integral_rpow_mul_exp_neg_mul_rpow hα hR hc]
      ring


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_mellinIntegrand_le {f : ℝ → E} {C₀ c α : ℝ}
    {s : ℂ} {u : ℝ} (hu : 1 < u)
    (hbound : ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ‖(u : ℂ) ^ (s - 1) • f u‖ ≤ C₀ * (u ^ ‖s‖ * exp (-c * u ^ α) / u) := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
    rpow_sub hu0, rpow_one]
  calc
    u ^ (s.re) / u * ‖f u‖ ≤ (u ^ ‖s‖ / u) * (C₀ * exp (-c * u ^ α)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right
          (rpow_le_rpow_of_exponent_le hu.le (Complex.re_le_norm s)) hu0.le
      · exact hbound
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

/-- Exponential tail decay makes the upper Mellin integral absolutely convergent at every
complex argument. -/
theorem integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow {f : ℝ → E}
    {C₀ c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi 1) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_rpow_div (R := ‖s‖) hc hα).const_mul C₀
  apply hi.mono' ?_ ?_
  · have hcpow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1)) (Ioi 1) := by
      apply ContinuousOn.cpow_const (by fun_prop)
      intro u hu
      exact Or.inl (by simpa using (zero_lt_one.trans hu))
    exact hcpow.aestronglyMeasurable measurableSet_Ioi |>.smul hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_mellinIntegrand_le hu (hbound u hu)

/-- The norm of the upper Mellin integral is bounded by its positive Gamma moment. -/
theorem norm_integral_cpow_smul_le_mul_Gamma {f : ℝ → E} {C₀ c α : ℝ}
    (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) := by
  calc
    _ ≤ ∫ u in Ioi 1, C₀ * (u ^ ‖s‖ * exp (-c * u ^ α) / u) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_rpow_mul_exp_neg_mul_rpow_div (R := ‖s‖) hc hα).const_mul C₀)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_mellinIntegrand_le hu (hbound u hu)
    _ = C₀ * ∫ u in Ioi 1, u ^ ‖s‖ * exp (-c * u ^ α) / u := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_rpow_mul_exp_neg_mul_rpow_div_le_Gamma (by linarith [norm_nonneg s]) hc hα) hC₀

/-- On the half-plane `Re s ≤ R`, the upper Mellin integral of an exponentially decaying kernel
is bounded by the tail moment at the fixed exponent `R`, uniformly in `Im s`. -/
theorem norm_integral_cpow_smul_le_of_re_le {f : ℝ → E} {C₀ c α R : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) {s : ℂ} (hs : s.re ≤ R) :
    ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      C₀ * ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((integrableOn_rpow_mul_exp_neg_mul_rpow_div (R := R) hc hα).const_mul C₀)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
    rpow_sub hu0, rpow_one]
  calc
    u ^ s.re / u * ‖f u‖ ≤ (u ^ R / u) * (C₀ * exp (-c * u ^ α)) := by
      apply mul_le_mul _ (hbound u hu) (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_right (rpow_le_rpow_of_exponent_le hu.le hs) hu0.le
    _ = _ := by ring

/-- A function continuous on `[1, ∞)` with an eventual bound `O(exp (-p u ^ α))` satisfies
`‖f u‖ ≤ C exp (-p u ^ α)` for every `u ≥ 1`, with `C ≥ 0`. No sign condition on `p` or `α` is
needed since `u > 0` on `[1, ∞)`. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {p α : ℝ} (hf : ContinuousOn f (Ici 1))
    (h : f =O[atTop] fun u ↦ exp (-p * u ^ α)) :
    ∃ C ≥ 0, ∀ u ∈ Ici 1, ‖f u‖ ≤ C * exp (-p * u ^ α) := by
  have hg : ContinuousOn (fun u : ℝ ↦ exp (-p * u ^ α)) (Ici 1) :=
    continuous_exp.comp_continuousOn <| continuousOn_const.mul <|
      continuousOn_id.rpow_const fun u hu ↦ Or.inl (zero_lt_one.trans_le hu).ne'
  obtain ⟨C, hC⟩ := isBigO_principal.mp (h.isBigO_principal_Ici_of_continuousOn hf
    hg fun u _ ↦ (exp_pos _).ne')
  refine ⟨max C 0, le_max_right _ _, fun u hu ↦ ?_⟩
  have hCu := hC u hu
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)] at hCu
  exact hCu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)

/-- Strict-ray form of `exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO`, matching the
domain `(1, ∞)` of the upper Mellin integral estimates. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_of_isBigO {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {p α : ℝ} (hf : ContinuousOn f (Ici 1))
    (h : f =O[atTop] fun u ↦ exp (-p * u ^ α)) :
    ∃ C ≥ 0, ∀ u ∈ Ioi 1, ‖f u‖ ≤ C * exp (-p * u ^ α) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO hf h
  exact ⟨C, hC, fun u hu ↦ hb u (mem_Ici.mpr hu.le)⟩

/-- Promotes an eventual pointwise stretched-exponential bound at `∞` on a continuous function to
all of `[1, ∞)`. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_eventually {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {C₀ p α : ℝ} (hf : ContinuousOn f (Ici 1))
    (h : ∀ᶠ u in atTop, ‖f u‖ ≤ C₀ * exp (-p * u ^ α)) :
    ∃ C ≥ 0, ∀ u ∈ Ici 1, ‖f u‖ ≤ C * exp (-p * u ^ α) := by
  refine exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO hf (IsBigO.of_bound C₀ ?_)
  filter_upwards [h] with u hu
  rwa [Real.norm_eq_abs, abs_of_pos (exp_pos _)]

/-- A function continuous on `[1, ∞)` with an eventual bound `O(exp (-p u))` satisfies
`‖f u‖ ≤ C exp (-p u ^ 1)` for every `u > 1`, with `C ≥ 0`. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {p : ℝ} (hf : ContinuousOn f (Ici 1)) (h : f =O[atTop] fun u ↦ exp (-p * u)) :
    ∃ C ≥ 0, ∀ u ∈ Ioi 1, ‖f u‖ ≤ C * exp (-p * u ^ (1 : ℝ)) :=
  exists_norm_le_mul_exp_neg_mul_rpow_of_isBigO hf (by simpa [rpow_one] using h)

/-- An exponentially decaying kernel gives logarithmic-exponential growth of its upper Mellin
integral, uniformly over the whole complex plane. -/
theorem exists_norm_integral_cpow_smul_le_exp_mul_log {f : ℝ → E} {C₀ c α : ℝ}
    (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ∃ C > 0, ∀ s : ℂ, ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hCG⟩ := exists_rpow_mul_Gamma_div_le_exp_mul_log hc hα
  refine ⟨C + 2 * C₀, by positivity, fun s ↦ ?_⟩
  calc
    _ ≤ C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) :=
      norm_integral_cpow_smul_le_mul_Gamma hC₀ hc hα hbound s
    _ ≤ exp C₀ * exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
      mul_le_mul (by linarith [add_one_le_exp C₀]) (hCG ‖s‖ (norm_nonneg s))
        (by positivity) (by positivity)
    _ = exp (C₀ + C * (1 + ‖s‖) * log (2 + ‖s‖)) := (exp_add _ _).symm
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (one_half_le_one_add_mul_log_two_add (norm_nonneg s))
        hC₀]

/-- The upper Mellin transform of an exponentially decaying complex kernel has order at most
one. -/
theorem orderLE_integral_cpow_mul_of_norm_le_exp_neg_mul_rpow {f : ℝ → ℂ}
    {C₀ c α : ℝ} (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    OrderLE (fun s ↦ ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) * f u) 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hC₀ hc hα hbound
  exact orderLE_one_of_norm_le_exp_mul_log hC

private theorem integrableOn_indicator_Ioc_of_locallyIntegrableOn {F : Type*}
    [NormedAddCommGroup F] {f : ℝ → F} (hf : LocallyIntegrableOn f (Ioi 0)) (M : ℝ) :
    IntegrableOn ((Ioc 1 M).indicator f) (Ioi 1) :=
  (integrableOn_indicator_iff measurableSet_Ioc.nullMeasurableSet).mpr
    ((hf.integrableOn_compact_subset (t := Icc 1 M) (fun _ hu ↦ zero_lt_one.trans_le hu.1)
      isCompact_Icc).mono_set (inter_subset_left.trans Ioc_subset_Icc_self))

private theorem norm_cpow_smul_indicator_Ioc_le {f : ℝ → E} {M R : ℝ}
    (hR : 0 ≤ R) {s : ℂ} (hs : s.re ≤ R) (u : ℝ) :
    ‖(u : ℂ) ^ (s - 1) • (Ioc 1 M).indicator f u‖ ≤ M ^ R * ‖(Ioc 1 M).indicator f u‖ := by
  by_cases hu : u ∈ Ioc 1 M
  · have hu0 : 0 < u := zero_lt_one.trans hu.1
    rw [indicator_of_mem hu, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hexp : (s - 1).re ≤ R := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact (rpow_le_rpow_of_exponent_le hu.1.le hexp).trans (rpow_le_rpow hu0.le hu.2 hR)
  · simp [indicator_of_notMem hu]

private theorem integrableOn_cpow_smul_indicator_Ioc {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioi 0)) (M : ℝ) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (Ioc 1 M).indicator f u) (Ioi 1) := by
  have hf₁ := integrableOn_indicator_Ioc_of_locallyIntegrableOn hf M
  refine (hf₁.norm.const_mul (M ^ ‖s‖)).mono' ?_ ?_
  · have hcpow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1)) (Ioi 1) :=
      ContinuousOn.cpow_const (by fun_prop) fun u hu ↦
        Or.inl (by simpa using (zero_lt_one.trans hu))
    exact (hcpow.aestronglyMeasurable measurableSet_Ioi).smul hf₁.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
    exact norm_cpow_smul_indicator_Ioc_le (norm_nonneg s) (Complex.re_le_norm s) u

private theorem norm_indicator_Ioi_le_exp_neg_mul_rpow {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {M C₀ c α : ℝ}
    (hbound : ∀ u ∈ Ioi M, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ∀ u ∈ Ioi 1, ‖(Ioi M).indicator f u‖ ≤ C₀ * exp (-c * u ^ α) := by
  have hC₀ : 0 ≤ C₀ := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound (M + 1) (lt_add_one M))) (exp_pos _)
  intro u _
  by_cases hu : u ∈ Ioi M
  · simpa only [indicator_of_mem hu] using hbound u hu
  · simp only [indicator_of_notMem hu, norm_zero]
    positivity

private theorem eqOn_add_indicator_Ioc_Ioi {F : Type*} [AddZeroClass F] (f : ℝ → F) (M : ℝ) :
    EqOn f (fun u ↦ (Ioc 1 M).indicator f u + (Ioi M).indicator f u) (Ioi 1) := by
  intro u hu
  dsimp only
  rcases le_or_gt u M with huM | huM
  · rw [indicator_of_mem (mem_Ioc.mpr ⟨hu, huM⟩), indicator_of_notMem (notMem_Ioi.mpr huM),
      add_zero]
  · rw [indicator_of_notMem (fun h ↦ huM.not_ge (mem_Ioc.mp h).2), indicator_of_mem huM, zero_add]

private theorem integral_cpow_smul_eq_add_indicator {f : ℝ → E} {T C₀ c α : ℝ}
    (hf : LocallyIntegrableOn f (Ioi 0)) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u) =
      (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioc 1 (max 1 T)).indicator f u) +
        ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioi (max 1 T)).indicator f u := by
  let M := max 1 T
  have hf₂_meas : AEStronglyMeasurable ((Ioi M).indicator f) (volume.restrict (Ioi 1)) :=
    ((hf.mono_set (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable).indicator measurableSet_Ioi
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  rw [setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ by
    rw [eqOn_add_indicator_Ioc_Ioi f M hu, smul_add]]
  exact integral_add (integrableOn_cpow_smul_indicator_Ioc hf M s)
    (integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc hα hf₂_meas hboundM s)

/-- A kernel locally integrable on `(0, ∞)` with a stretched-exponential bound above an arbitrary
threshold `T` has an absolutely convergent upper Mellin integral at every complex argument. -/
theorem integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow_of_gt {f : ℝ → E}
    {T C₀ c α : ℝ} (hf : LocallyIntegrableOn f (Ioi 0))
    (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi 1) := by
  let M := max 1 T
  have hf₂_meas : AEStronglyMeasurable ((Ioi M).indicator f) (volume.restrict (Ioi 1)) :=
    ((hf.mono_set (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable).indicator measurableSet_Ioi
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  refine ((integrableOn_cpow_smul_indicator_Ioc hf M s).add
    (integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc hα hf₂_meas hboundM s)).congr_fun
    (fun u hu ↦ ?_) measurableSet_Ioi
  rw [Pi.add_apply, eqOn_add_indicator_Ioc_Ioi f M hu, smul_add]

/-- On any half-plane `Re s ≤ R`, the upper Mellin integral of a locally integrable kernel with an
exponential bound above `T` is uniformly bounded independently of `Im s`. -/
theorem exists_norm_integral_cpow_smul_le_of_re_le_of_gt {f : ℝ → E}
    {T C₀ c α : ℝ} (hf : LocallyIntegrableOn f (Ioi 0))
    (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (R : ℝ) :
    ∃ B ≥ 0, ∀ s : ℂ, s.re ≤ R → ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤ B := by
  have hC₀ : 0 ≤ C₀ := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound (T + 1) (lt_add_one T))) (exp_pos _)
  let M := max 1 T
  have _ : 0 < M := zero_lt_one.trans_le (le_max_left 1 T)
  let f₁ := (Ioc 1 M).indicator f
  have hf₁ := integrableOn_indicator_Ioc_of_locallyIntegrableOn hf M
  have _ : 0 ≤ ∫ u in Ioi 1, ‖f₁ u‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have _ : 0 ≤ ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu ↦ by
      have hu0 : 0 < u := zero_lt_one.trans hu
      positivity
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  refine ⟨M ^ max R 0 * (∫ u in Ioi 1, ‖f₁ u‖) +
    C₀ * ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u, by positivity, fun s hs ↦ ?_⟩
  rw [integral_cpow_smul_eq_add_indicator hf hc hα hbound s]
  refine (norm_add_le _ _).trans (add_le_add ?_
    (norm_integral_cpow_smul_le_of_re_le hc hα hboundM hs))
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf₁.norm.const_mul (M ^ max R 0)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
  exact norm_cpow_smul_indicator_Ioc_le (le_max_right R 0) (hs.trans (le_max_left R 0)) u

/-- A kernel locally integrable on `(0, ∞)` with a stretched-exponential bound above an arbitrary
threshold `T` gives global logarithmic-exponential growth of its upper Mellin integral. -/
theorem exists_norm_integral_cpow_smul_le_exp_mul_log_of_gt {f : ℝ → E}
    {T C₀ c α : ℝ} (hf : LocallyIntegrableOn f (Ioi 0))
    (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ∃ C > 0, ∀ s : ℂ, ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  let M := max 1 T
  have hM1 : 1 ≤ M := le_max_left 1 T
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have hlogM : 0 ≤ log M := log_nonneg hM1
  let f₁ := (Ioc 1 M).indicator f
  have hf₁ := integrableOn_indicator_Ioc_of_locallyIntegrableOn hf M
  let I₁ := ∫ u in Ioi 1, ‖f₁ u‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ ↦ norm_nonneg _
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  obtain ⟨B, hB, hF₂⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hC₀ hc hα hboundM
  let K := B + 2 * log M
  let D := 1 + I₁
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + 2 * D, by dsimp [K]; positivity, fun s ↦ ?_⟩
  have hW : 0 ≤ (1 + ‖s‖) * log (2 + ‖s‖) :=
    mul_nonneg (by positivity) (log_nonneg (by linarith [norm_nonneg s]))
  have hF₁ : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f₁ u‖ ≤
      I₁ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    have hint : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f₁ u‖ ≤ M ^ ‖s‖ * I₁ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hf₁.norm.const_mul (M ^ ‖s‖)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact norm_cpow_smul_indicator_Ioc_le (norm_nonneg s) (Complex.re_le_norm s) u
    refine hint.trans ?_
    rw [rpow_def_of_pos hM0, mul_comm]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hI₁
    have hlog := one_half_le_log_two_add (norm_nonneg s)
    have hns : ‖s‖ ≤ 2 * ((1 + ‖s‖) * log (2 + ‖s‖)) := by nlinarith [norm_nonneg s]
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hns hlogM, mul_nonneg hB.le hW]
  have hF₂' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioi M).indicator f u‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) :=
    (hF₂ s).trans (exp_le_exp.mpr (by nlinarith [mul_nonneg hlogM hW]))
  rw [integral_cpow_smul_eq_add_indicator hf hc hα hbound s]
  calc
    _ ≤ I₁ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) + exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) :=
      (norm_add_le _ _).trans (add_le_add hF₁ hF₂')
    _ = D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by dsimp [D]; ring
    _ ≤ exp D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
      gcongr
      linarith [add_one_le_exp D]
    _ = exp (D + K * (1 + ‖s‖) * log (2 + ‖s‖)) := (exp_add _ _).symm
    _ ≤ _ := exp_le_exp.mpr <| by
      nlinarith [mul_le_mul_of_nonneg_left (one_half_le_one_add_mul_log_two_add (norm_nonneg s))
        hD.le]

end TauCeti
