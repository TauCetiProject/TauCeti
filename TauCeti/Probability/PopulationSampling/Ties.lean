/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.RepeatedValues

/-!
# Sampling discrepancy for random populations with ties

Draw a random population with law `ρ` on `κ → α` and sample `m = |ι|` of its values, once without
and once with replacement. Write `n = |κ|`, `p = n.descFactorial m / n ^ m` for the probability
that a uniform index map `ι → κ` is injective, and `t = m.descFactorial 2 / n.descFactorial 2`.
For every random population the two sampling laws differ on each event by at most the collision
probability `1 - p` (`sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision`).

A deterministic population with a repeated value does better: its two sampling laws differ on each
event, in either direction, by at most `1 - p - t * min p (1 - p)`
(`sampleWithoutReplacement_le_sampleWithReplacement_dirac_add_of_not_injective`). Averaging over
`ρ`, this file shows that if `S` is a measurable set of populations with a repeated value, the two
sampling laws of `ρ` differ on every event, in either direction, by at most
`1 - p - t * min p (1 - p) * ρ(S)`. The improvement over `1 - p` grows linearly with the
probability that the drawn population has a tie. For `S = ∅` this is the collision bound; if the
population has a repeated value almost surely, it is the one-pair error.

The bounds hold for every sample size: when `m > n`, sampling without replacement is the zero
measure, `p = 0`, and the error is `1`.

## Main statements

* `sampleWithoutReplacement_le_sampleWithReplacement_add_ties`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add_ties`: the eventwise mixture bounds with
  ties, in both directions;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_ties`: their total-variation form.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α]

/-- **Pointwise errors.** Sampling a deterministic population `x` without and with replacement
differ on each event, in either direction, by at most `1 - p - t * min p (1 - p)` if `x` lies in a
set `S` of non-injective populations, and by at most `1 - p` otherwise. -/
private theorem dirac_le_add_tieError {S : Set (κ → α)} (hSx : ∀ x ∈ S, ¬ Injective x)
    (x : κ → α) (A : Set (ι → α)) :
    let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ) ^ Fintype.card ι
    let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
    let g : (κ → α) → ℝ≥0∞ := S.indicator (fun _ => ENNReal.ofReal (1 - p - t * min p (1 - p))) +
      Sᶜ.indicator (fun _ => ENNReal.ofReal (1 - p))
    sampleWithoutReplacement (Measure.dirac x) A ≤
        sampleWithReplacement (Measure.dirac x) A + g x ∧
      sampleWithReplacement (Measure.dirac x) A ≤
        sampleWithoutReplacement (Measure.dirac x) A + g x := by
  classical
  intro p t g
  by_cases hx : x ∈ S
  · have hg : g x = ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
      simp [g, hx]
    rw [hg]
    exact ⟨sampleWithoutReplacement_le_sampleWithReplacement_dirac_add_of_not_injective
        (hSx x hx) A,
      sampleWithReplacement_le_sampleWithoutReplacement_dirac_add_of_not_injective (hSx x hx) A⟩
  · have hg : g x = ENNReal.ofReal (1 - p) := by
      simp [g, hx]
    rw [hg, ← one_sub_descFactorial_div_pow_eq_ofReal]
    exact ⟨sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision A,
      sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision A⟩

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- **Averaging the pointwise errors.** The `ρ`-average of the pointwise errors of
`dirac_le_add_tieError` is `1 - p - t * min p (1 - p) * ρ(S)`. -/
private theorem lintegral_tieError (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ]
    {S : Set (κ → α)} (hS : MeasurableSet S) :
    let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ) ^ Fintype.card ι
    let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
    ∫⁻ x, (S.indicator (fun _ => ENNReal.ofReal (1 - p - t * min p (1 - p))) +
        Sᶜ.indicator (fun _ => ENNReal.ofReal (1 - p))) x ∂ρ =
      ENNReal.ofReal (1 - p - t * min p (1 - p) * (ρ S).toReal) := by
  intro p t
  have hp1 : p ≤ 1 := descFactorial_div_pow_le_one _ _
  have he : 0 ≤ 1 - p - t * min p (1 - p) :=
    one_sub_descFactorial_div_pow_sub_mul_min_nonneg _ _
  set s := (ρ S).toReal
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs1 : s ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hρS : ρ S = ENNReal.ofReal s := (ENNReal.ofReal_toReal (measure_ne_top ρ S)).symm
  have hρSc : ρ Sᶜ = ENNReal.ofReal (1 - s) := by
    rw [prob_compl_eq_one_sub hS, hρS, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hs0]
  rw [Pi.add_def, lintegral_add_left (measurable_const.indicator hS),
    lintegral_indicator_const hS, lintegral_indicator_const hS.compl, hρSc, hρS,
    ← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul (sub_nonneg.2 hp1),
    ← ENNReal.ofReal_add (mul_nonneg he hs0) (mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hs1))]
  congr 1
  ring

/-- **The mixture bound with ties, without replacement to with replacement.** Let `S` be a
measurable set of populations with a repeated value. For a random population with law `ρ`, every
event has mass under sampling without replacement at most its mass under sampling with
replacement plus `1 - p - t * min p (1 - p) * ρ(S)`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add_ties
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] {S : Set (κ → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Injective x) (A : Set (ι → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p) * (ρ S).toReal) := by
  rw [← lintegral_tieError (ι := ι) ρ hS, sampleWithoutReplacement_def, sampleWithReplacement_def]
  refine samplePopulation_le_add_lintegral (fun B _ => ae_of_all _ fun x => ?_) A
  simpa only [sampleWithoutReplacement_def, sampleWithReplacement_def] using
    (dirac_le_add_tieError hSx x B).1

/-- **The mixture bound with ties, with replacement to without replacement.** Let `S` be a
measurable set of populations with a repeated value. For a random population with law `ρ`, every
event has mass under sampling with replacement at most its mass under sampling without replacement
plus `1 - p - t * min p (1 - p) * ρ(S)`, where `p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and
`t = |ι|.descFactorial 2 / |κ|.descFactorial 2`. When `|ι| > |κ|` the error is `1`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_ties
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] {S : Set (κ → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Injective x) (A : Set (ι → α)) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p) * (ρ S).toReal) := by
  rw [← lintegral_tieError (ι := ι) ρ hS, sampleWithoutReplacement_def, sampleWithReplacement_def]
  refine samplePopulation_le_add_lintegral (fun B _ => ae_of_all _ fun x => ?_) A
  simpa only [sampleWithoutReplacement_def, sampleWithReplacement_def] using
    (dirac_le_add_tieError hSx x B).2

/-- **The mixture bound with ties, total-variation form.** Let `S` be a measurable set of
populations with a repeated value. For a random population with law `ρ`, Mathlib's extended total
variation distance between sampling without and with replacement is at most
`2 * ENNReal.ofReal (1 - p - t * min p (1 - p) * ρ(S))`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_ties
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] {S : Set (κ → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Injective x) :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p) * (ρ S).toReal) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ => sampleWithoutReplacement_le_sampleWithReplacement_add_ties ρ hS hSx A)
    (fun A _ => sampleWithReplacement_le_sampleWithoutReplacement_add_ties ρ hS hSx A)

end TauCeti.Probability
