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
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Growth bounds for Mellin tails with exponential decay

The tail over `(1, ∞)` of `u^R exp(-c u^α) du/u` converges for every real `R` and
`c, α > 0`, and is bounded by the positive Gamma moment at `(R+1)/α` when `R > -1`.
In particular this bound remains finite at `R = 0`. These estimates provide the quantitative
ingredient for the split Mellin method of proving order-one growth for completed L-functions.
On a half-plane `Re s ≤ R` the upper Mellin integral is bounded by the tail at the fixed
exponent `R`, independently of `Im s`; this gives boundedness on vertical strips.
More generally, for any kernel locally integrable on `[1, ∞)` with stretched-exponential decay
`f =O[atTop] fun u ↦ exp (-c * u ^ α)`, splitting `(1, ∞)` at an eventual threshold recovers
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

private theorem nonneg_of_norm_le_mul_exp_on_Ioi {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {T C₀ c α : ℝ}
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) : 0 ≤ C₀ :=
  nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound (T + 1) (lt_add_one T))) (exp_pos _)

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
    (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) := by
  have hC₀ := nonneg_of_norm_le_mul_exp_on_Ioi hbound
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

/-- An exponentially decaying kernel gives logarithmic-exponential growth of its upper Mellin
integral, uniformly over the whole complex plane. -/
theorem exists_norm_integral_cpow_smul_le_exp_mul_log {f : ℝ → E} {C₀ c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ∃ C > 0, ∀ s : ℂ, ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hC₀ := nonneg_of_norm_le_mul_exp_on_Ioi hbound
  obtain ⟨C, hC, hCG⟩ := exists_rpow_mul_Gamma_div_le_exp_mul_log hc hα
  refine ⟨C + 2 * C₀, by positivity, fun s ↦ ?_⟩
  calc
    _ ≤ C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) :=
      norm_integral_cpow_smul_le_mul_Gamma hc hα hbound s
    _ ≤ C₀ * exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
      mul_le_mul_of_nonneg_left (hCG ‖s‖ (norm_nonneg s)) hC₀
    _ ≤ _ := Real.mul_exp_mul_one_add_mul_log_two_add_le hC₀ (norm_nonneg s)

/-- The upper Mellin transform of an exponentially decaying complex kernel has order at most
one. -/
theorem orderLE_integral_cpow_mul_of_norm_le_exp_neg_mul_rpow {f : ℝ → ℂ}
    {C₀ c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    OrderLE (fun s ↦ ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) * f u) 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hc hα hbound
  exact orderLE_one_of_norm_le_exp_mul_log hC

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

private theorem norm_integral_cpow_smul_indicator_Ioc_le {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ici 1)) (M : ℝ) {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : s.re ≤ R) :
    ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioc 1 M).indicator f u‖ ≤
      M ^ R * ∫ u in Ioi 1, ‖(Ioc 1 M).indicator f u‖ := by
  rw [← integral_const_mul]
  have hf₁ : IntegrableOn ((Ioc 1 M).indicator f) (Ioi 1) :=
    ((hf.integrableOn_Ioc_of_Ici M).integrable_indicator measurableSet_Ioc).integrableOn
  refine norm_integral_le_of_norm_le (hf₁.norm.const_mul (M ^ R)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
  exact norm_cpow_smul_indicator_Ioc_le hR hs u

private theorem integrableOn_cpow_smul_indicator_Ioc {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ici 1)) (M : ℝ) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (Ioc 1 M).indicator f u) (Ioi 1) := by
  have hf₁ : IntegrableOn ((Ioc 1 M).indicator f) (Ioi 1) :=
    ((hf.integrableOn_Ioc_of_Ici M).integrable_indicator measurableSet_Ioc).integrableOn
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
  have hC₀ := nonneg_of_norm_le_mul_exp_on_Ioi hbound
  intro u _
  by_cases hu : u ∈ Ioi M
  · simpa only [indicator_of_mem hu] using hbound u hu
  · simp only [indicator_of_notMem hu, norm_zero]
    positivity

private theorem integrableOn_cpow_smul_indicator_Ioi {f : ℝ → E} {T C₀ c α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 1)) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (Ioi (max 1 T)).indicator f u) (Ioi 1) := by
  have hf₂_meas : AEStronglyMeasurable ((Ioi (max 1 T)).indicator f) (volume.restrict (Ioi 1)) :=
    ((hf.mono_set Ioi_subset_Ici_self).aestronglyMeasurable).indicator measurableSet_Ioi
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  exact integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc hα hf₂_meas hboundM s

private theorem integral_cpow_smul_eq_add_indicator {f : ℝ → E} {T C₀ c α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 1)) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u) =
      (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioc 1 (max 1 T)).indicator f u) +
        ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioi (max 1 T)).indicator f u := by
  rw [← integral_add (integrableOn_cpow_smul_indicator_Ioc hf (max 1 T) s)
    (integrableOn_cpow_smul_indicator_Ioi hf hc hα hbound s)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  rw [← smul_add, ← congr_fun (indicator_union_of_disjoint Ioc_disjoint_Ioi_same f) u,
    indicator_of_mem (Ioi_subset_Ioc_union_Ioi hu)]

private theorem exists_Ioi_norm_le_exp_neg_mul_rpow {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {c α : ℝ} (hf_top : f =O[atTop] fun u ↦ exp (-c * u ^ α)) :
    ∃ T C₀ : ℝ, ∀ u ∈ Ioi T, ‖f u‖ ≤ C₀ * exp (-c * u ^ α) := by
  obtain ⟨C₀, hC₀⟩ := hf_top.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC₀
  refine ⟨T, C₀, fun u hu ↦ ?_⟩
  simpa [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hT u hu.le

/-- A kernel locally integrable on `[1, ∞)` with stretched-exponential decay
`f =O[atTop] fun u ↦ exp (-c * u ^ α)` has an absolutely convergent upper Mellin integral at every
complex argument. -/
theorem integrableOn_cpow_smul_of_isBigO_exp_neg_mul_rpow {f : ℝ → E} {c α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 1)) (hc : 0 < c) (hα : 0 < α)
    (hf_top : f =O[atTop] fun u ↦ exp (-c * u ^ α)) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi 1) := by
  obtain ⟨T, C₀, hbound⟩ := exists_Ioi_norm_le_exp_neg_mul_rpow hf_top
  refine ((integrableOn_cpow_smul_indicator_Ioc hf (max 1 T) s).add
    (integrableOn_cpow_smul_indicator_Ioi hf hc hα hbound s)).congr_fun
    (fun u hu ↦ ?_) measurableSet_Ioi
  rw [Pi.add_apply, ← smul_add,
    ← congr_fun (indicator_union_of_disjoint Ioc_disjoint_Ioi_same f) u,
    indicator_of_mem (Ioi_subset_Ioc_union_Ioi hu)]

/-- On any half-plane `Re s ≤ R`, the upper Mellin integral of a kernel locally integrable on
`[1, ∞)` with stretched-exponential decay `f =O[atTop] fun u ↦ exp (-c * u ^ α)` is uniformly
bounded independently of `Im s`. -/
theorem exists_norm_integral_cpow_smul_le_of_re_le_of_isBigO {f : ℝ → E} {c α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 1)) (hc : 0 < c) (hα : 0 < α)
    (hf_top : f =O[atTop] fun u ↦ exp (-c * u ^ α)) (R : ℝ) :
    ∃ B ≥ 0, ∀ s : ℂ, s.re ≤ R → ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤ B := by
  obtain ⟨T, C₀, hbound⟩ := exists_Ioi_norm_le_exp_neg_mul_rpow hf_top
  have hC₀ := nonneg_of_norm_le_mul_exp_on_Ioi hbound
  let M := max 1 T
  have _ : 0 < M := zero_lt_one.trans_le (le_max_left 1 T)
  have _ : 0 ≤ ∫ u in Ioi 1, ‖(Ioc 1 M).indicator f u‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have _ : 0 ≤ ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu ↦ by
      have hu0 : 0 < u := zero_lt_one.trans hu
      positivity
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  refine ⟨M ^ max R 0 * (∫ u in Ioi 1, ‖(Ioc 1 M).indicator f u‖) +
    C₀ * ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u, by positivity, fun s hs ↦ ?_⟩
  rw [integral_cpow_smul_eq_add_indicator hf hc hα hbound s]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_integral_cpow_smul_indicator_Ioc_le hf M (le_max_right R 0) (hs.trans (le_max_left R 0)))
    (norm_integral_cpow_smul_le_of_re_le hc hα hboundM hs))

/-- A kernel locally integrable on `[1, ∞)` with stretched-exponential decay
`f =O[atTop] fun u ↦ exp (-c * u ^ α)` gives global logarithmic-exponential growth of its upper
Mellin integral. -/
theorem exists_norm_integral_cpow_smul_le_exp_mul_log_of_isBigO {f : ℝ → E} {c α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 1)) (hc : 0 < c) (hα : 0 < α)
    (hf_top : f =O[atTop] fun u ↦ exp (-c * u ^ α)) :
    ∃ C > 0, ∀ s : ℂ, ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨T, C₀, hbound⟩ := exists_Ioi_norm_le_exp_neg_mul_rpow hf_top
  let M := max 1 T
  have hM1 : 1 ≤ M := le_max_left 1 T
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have hlogM : 0 ≤ log M := log_nonneg hM1
  let I₁ := ∫ u in Ioi 1, ‖(Ioc 1 M).indicator f u‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ ↦ norm_nonneg _
  have hboundM := norm_indicator_Ioi_le_exp_neg_mul_rpow fun u hu ↦
    hbound u ((le_max_right 1 T).trans_lt hu)
  obtain ⟨B, hB, hF₂⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hc hα hboundM
  let K := B + 2 * log M
  let D := 1 + I₁
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + 2 * D, by dsimp [K]; positivity, fun s ↦ ?_⟩
  have hF₁ : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioc 1 M).indicator f u‖ ≤
      I₁ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    refine (norm_integral_cpow_smul_indicator_Ioc_le hf M (norm_nonneg s)
      (Complex.re_le_norm s)).trans ?_
    rw [rpow_def_of_pos hM0, mul_comm]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hI₁
    have hlog := one_half_le_log_two_add (norm_nonneg s)
    have hns : ‖s‖ ≤ 2 * ((1 + ‖s‖) * log (2 + ‖s‖)) := by nlinarith [norm_nonneg s]
    have hW : 0 ≤ (1 + ‖s‖) * log (2 + ‖s‖) :=
      mul_nonneg (by positivity) (by linarith)
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hns hlogM, mul_nonneg hB.le hW]
  have hF₂' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (Ioi M).indicator f u‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) :=
    (hF₂ s).trans (Real.exp_mul_one_add_mul_log_two_add_le_of_le (by dsimp [K]; linarith)
      (norm_nonneg s))
  rw [integral_cpow_smul_eq_add_indicator hf hc hα hbound s]
  calc
    _ ≤ I₁ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) + exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) :=
      (norm_add_le _ _).trans (add_le_add hF₁ hF₂')
    _ = D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by dsimp [D]; ring
    _ ≤ _ := Real.mul_exp_mul_one_add_mul_log_two_add_le hD.le (norm_nonneg s)

end TauCeti
