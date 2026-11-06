/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Decomposition
public import TauCeti.Probability.Distributions.Stable.IntegrableExpMul
import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Stable.Transforms
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.CompoundPoisson.Transforms
import TauCeti.Probability.Distributions.Pareto.Basic
import TauCeti.Probability.Moments.Basic

/-!
# Exact exponential domains of scalar stable laws

A positive-scale non-Gaussian stable law has no nonzero exponential moments unless it is
fully skewed. At skewness `1` its domain is `(-∞, 0]`, and at skewness `-1` it is `[0, ∞)`.
Gaussian and zero-scale laws have all exponential moments.

`TauCeti.Probability.integrable_exp_mul_stableMeasure_iff` gives an integrability criterion,
and `TauCeti.Probability.integrableExpSet_id_stableMeasure` gives the domain as a set.
The divergence argument uses the independent large-jump factor: its positive and negative
jump tails are Pareto tails, which preclude exponential moments in the corresponding direction.
Thus the result does not require asymptotic tail estimates for the limiting stable law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 25 (exponential moments and the large-jump measure).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β t : ℝ}

private lemma not_integrable_exp_mul_cond_stableLevyMeasure
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hβneg : -1 < β) (ht : 0 < t) :
    ¬ Integrable (fun x ↦ exp (t * x))
      (ProbabilityTheory.cond (stableLevyMeasure α β) {x : ℝ | 1 < |x|}) := by
  intro h
  have hmass := stableLevyMeasure_abs_gt_pos hα hβ (by norm_num : (0 : ℝ) < 1)
  have hfinite := stableLevyMeasure_abs_gt_ne_top
    (α := α) (β := β) (by norm_num : (0 : ℝ) < 1)
  have hrestrict : IntegrableOn (fun x ↦ exp (t * x)) {x : ℝ | 1 < |x|}
      (stableLevyMeasure α β) :=
    (integrable_inv_smul_measure hmass.ne' hfinite).mp h
  have htail : IntegrableOn (fun x ↦ exp (t * x)) (Ioi 1) (stableLevyMeasure α β) :=
    hrestrict.mono_set fun x hx ↦ hx.trans_le (le_abs_self x)
  rw [IntegrableOn, stableLevyMeasure_restrict_Ioi hα hβ (by norm_num)] at htail
  have hc : 0 < Gamma (1 + α) * sin (π * α / 2) / π * (1 + β) /
      (α * (1 : ℝ) ^ α) :=
    div_pos (mul_pos (stableLevyDensity_coefficient_pos hα) (by linarith))
      (mul_pos hα.1 (by positivity))
  have hpareto := (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hc)
    ENNReal.ofReal_ne_top).mp htail
  exact (not_le_of_gt ht) ((integrable_exp_mul_id_paretoMeasure_iff
    (by norm_num : (0 : ℝ) < 1) hα.1 t).mp hpareto)

private lemma not_integrable_exp_mul_stableMeasure_one_zero
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hβneg : -1 < β) (ht : 0 < t) :
    ¬ Integrable (fun x ↦ exp (t * x)) (stableMeasure α β 1 0) := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableMeasure ⟨hα.1, hα.2.le⟩ hβ 1 0
  have hpos := mgf_pos' (X := id) (IsProbabilityMeasure.ne_zero _) h
  rw [← hρ, TauCeti.mgf_id_conv, Pi.mul_apply] at hpos
  have hlarge : Integrable (fun x ↦ exp (t * x))
      (stableCompensatedPoissonMeasure α β 1) :=
    mgf_pos_iff.mp (pos_of_mul_pos_right hpos mgf_nonneg)
  have hdomain : t ∈ integrableExpSet id (stableCompensatedPoissonMeasure α β 1) := by
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using hlarge
  rw [stableCompensatedPoissonMeasure_def] at hdomain
  -- The compensation is a translation, so affine transport removes it from the domain.
  have htranslate : (fun x : ℝ ↦ x - ∫ y in {y : ℝ | 1 < |y|}, sin y
      ∂stableLevyMeasure α β) =
      (fun x ↦ -(∫ y in {y : ℝ | 1 < |y|}, sin y ∂stableLevyMeasure α β) + 1 * x) := by
    funext x
    ring
  rw [htranslate, integrableExpSet_id_map_affine] at hdomain
  simp only [mem_preimage, one_mul] at hdomain
  have hrate : ((stableLevyMeasure α β) {x : ℝ | 1 < |x|}).toNNReal ≠ 0 := by
    exact ENNReal.toNNReal_ne_zero.mpr
      ⟨(stableLevyMeasure_abs_gt_pos hα hβ (by norm_num)).ne',
        stableLevyMeasure_abs_gt_ne_top (by norm_num)⟩
  have hjump := (integrable_exp_mul_compoundPoissonMeasure_iff hrate
    (f := AddMonoidHom.id ℝ) measurable_id t).mp
      (by simpa only [integrableExpSet, mem_ofPred_eq, id_eq, AddMonoidHom.id_apply]
        using hdomain)
  exact not_integrable_exp_mul_cond_stableLevyMeasure hα hβ hβneg ht hjump

private lemma integrable_exp_mul_stableMeasure_one_zero_iff
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Integrable (fun x ↦ exp (t * x)) (stableMeasure α β 1 0) ↔
      t = 0 ∨ |β| = 1 ∧ β * t ≤ 0 := by
  let _ := isProbabilityMeasure_stableMeasure ⟨hα.1, hα.2.le⟩ hβ 1 0
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases lt_trichotomy t 0 with ht | rfl | ht
    · have hreflect : Integrable (fun x ↦ exp ((-t) * x))
          (stableMeasure α (-β) 1 0) := by
        have hmap := stableMeasure_map_neg α β 1 0
        simp only [neg_zero] at hmap
        rw [← hmap, integrable_map_measure (by fun_prop) measurable_neg.aemeasurable]
        simpa only [Function.comp_def, neg_mul_neg] using h
      have hb : β = 1 := by
        by_contra hb
        exact not_integrable_exp_mul_stableMeasure_one_zero hα (by simpa using hβ)
          (by grind [abs_le]) (neg_pos.mpr ht) hreflect
      exact Or.inr ⟨by simp [hb], by simp [hb, ht.le]⟩
    · exact Or.inl rfl
    · have hb : β = -1 := by
        by_contra hb
        exact not_integrable_exp_mul_stableMeasure_one_zero hα hβ
          (by grind [abs_le]) ht h
      exact Or.inr ⟨by simp [hb], by simp [hb, ht.le]⟩
  · rintro (rfl | ⟨hb, ht⟩)
    · simp
    · exact integrable_exp_mul_stableMeasure hb 1 0 ht

/-- The exact exponential-moment criterion for a valid scalar stable law, including Gaussian
and Dirac boundaries. For positive scale and shape below two, only zero is allowed unless
the law is fully skewed, when the half-line opposite to its jumps is allowed. -/
@[simp]
theorem integrable_exp_mul_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m t : ℝ) :
    Integrable (fun x ↦ exp (t * x)) (stableMeasure α β s m) ↔
      s = 0 ∨ α = 2 ∨ t = 0 ∨ |β| = 1 ∧ β * t ≤ 0 := by
  rcases eq_zero_or_pos s with rfl | hs
  · have hmem : t ∈ integrableExpSet id (stableMeasure α β 0 m) := by
      rw [integrableExpSet_id_stableMeasure_zero_scale hα hβ]
      exact mem_univ t
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq, true_or, iff_true] using hmem
  rcases hα.2.eq_or_lt with rfl | hα2
  · have hmem : t ∈ integrableExpSet id (stableMeasure 2 β s m) := by
      rw [integrableExpSet_id_stableMeasure_two hβ]
      exact mem_univ t
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq, true_or, or_true, iff_true] using hmem
  have hmem := mem_integrableExpSet_id_stableMeasure_iff_one_zero (α := α) (β := β)
    (m := m) (t := t) hs
  simp only [integrableExpSet, mem_ofPred_eq, id_eq] at hmem
  rw [hmem, integrable_exp_mul_stableMeasure_one_zero_iff ⟨hα.1, hα2⟩ hβ]
  have hsign : β * ((s : ℝ) * t) ≤ 0 ↔ β * t ≤ 0 := by
    rw [mul_left_comm]
    exact ⟨fun h ↦ nonpos_of_mul_nonpos_right h (NNReal.coe_pos.mpr hs),
      mul_nonpos_of_nonneg_of_nonpos s.2⟩
  simp only [mul_eq_zero, NNReal.coe_eq_zero, hs.ne', false_or, hsign, hα2.ne]

/-- The exponential-integrability domain of a valid stable law: all of `ℝ` for Gaussian
or zero-scale laws, the appropriate closed half-line at full skewness, and `{0}` otherwise. -/
@[simp]
theorem integrableExpSet_id_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) :
    integrableExpSet id (stableMeasure α β s m) =
      if s = 0 ∨ α = 2 then univ else
        if β = 1 then Iic 0 else if β = -1 then Ici 0 else {0} := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq,
    integrable_exp_mul_stableMeasure_iff hα hβ]
  split_ifs <;> simp_all [mem_Iic, mem_Ici] <;> grind [abs_eq_max_neg]

end TauCeti.Probability
