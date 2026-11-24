/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.PopulationSampling.Finite

/-!
# Total-variation and excess bounds for finite population sampling

For a random population `ρ : Measure (κ → α)`, `sampleWithoutReplacement ρ` and
`sampleWithReplacement ρ` are both instances of `samplePopulation` along uniform selection laws on
`ι → κ`. Conditioning on the drawn population integrates deterministic-population collision bounds
into bounds on eventwise excess, extended total variation distance (`etvDist`), real total
variation distance (`tvDist`), and real event probabilities (`Measure.real`).

This file develops random-population collision bounds for `sampleWithoutReplacement ρ` against
`sampleWithReplacement ρ`: one-sided measurable-event excesses, `etvDist`, `tvDist`, and real
eventwise differences `|P.real A - Q.real A|` in the collision-event form, the exact
falling-factorial form `1 - (|κ|)_|ι| / |κ| ^ |ι|`, and the pairwise union-bound form
`choose |ι| 2 / |κ|`, with no nonemptiness or embedding assumptions needed on the upper bounds.

## Main declarations

* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision`,
  `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_exact_collision`,
  `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le` (and reversed companions):
  measurable-event excess bounds;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le`: random-population `etvDist` bounds,
  together with their `tvDist` and `Measure.real` companions.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section CollisionBounds

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ] [MeasurableSpace α]

omit [Fintype κ] in
/-- The largest measurable-event excess of `sampleWithoutReplacement ρ` over
`sampleWithReplacement ρ` is at most the uniform-measure mass of colliding selections. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A) ≤
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} :=
  iSup₂_le fun A _ =>
    tsub_le_iff_left.2 (sampleWithoutReplacement_le_sampleWithReplacement_add_collision A)

omit [Fintype κ] in
/-- The largest measurable-event excess of `sampleWithReplacement ρ` over
`sampleWithoutReplacement ρ` is at most the uniform-measure mass of colliding selections. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithReplacement (ι := ι) ρ A - sampleWithoutReplacement (ι := ι) ρ A) ≤
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} :=
  iSup₂_le fun A _ =>
    tsub_le_iff_left.2 (sampleWithReplacement_le_sampleWithoutReplacement_add_collision A)

/-- Exact-collision upper bound on the largest measurable-event excess of
`sampleWithoutReplacement ρ` over `sampleWithReplacement ρ`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A) ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision ρ).trans
    uniformOn_not_injective_le_one_sub_descFactorial_div_pow

/-- Exact-collision upper bound on the largest measurable-event excess of
`sampleWithReplacement ρ` over `sampleWithoutReplacement ρ`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithReplacement (ι := ι) ρ A - sampleWithoutReplacement (ι := ι) ρ A) ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision ρ).trans
    uniformOn_not_injective_le_one_sub_descFactorial_div_pow

/-- Pairwise union-bound form of the excess of `sampleWithoutReplacement ρ` over
`sampleWithReplacement ρ`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A) ≤
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision ρ).trans
    uniformOn_not_injective_le

/-- Pairwise union-bound form of the excess of `sampleWithReplacement ρ` over
`sampleWithoutReplacement ρ`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithReplacement (ι := ι) ρ A - sampleWithoutReplacement (ι := ι) ρ A) ≤
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision ρ).trans
    uniformOn_not_injective_le

omit [Fintype κ] in
/-- **Total-variation collision bound for random populations.** For any probability population law
`ρ`, `etvDist` between sampling without and with replacement is at most twice the uniform-measure
mass of colliding selections. No embedding `ι ↪ κ` is needed: when none exists,
`sampleWithoutReplacement ρ` is zero and the collision mass is `1` (or `0` when `ι → κ` is empty),
so the inequality still holds. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ => sampleWithoutReplacement_le_sampleWithReplacement_add_collision A)
    (fun A _ => sampleWithReplacement_le_sampleWithoutReplacement_add_collision A)

/-- **Exact-collision `etvDist` bound for random populations.** For any probability population law
`ρ`, `etvDist` between sampling without and with replacement is at most
`2 * (1 - (|κ|)_|ι| / |κ| ^ |ι|)`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision ρ).trans
    (mul_le_mul_of_nonneg_left uniformOn_not_injective_le_one_sub_descFactorial_div_pow zero_le)

/-- **Pairwise union-bound `etvDist` bound for random populations.** For any probability population
law `ρ`, `etvDist` between sampling without and with replacement is at most
`2 * (choose |ι| 2 / |κ|)`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((Fintype.card ι).choose 2 / Fintype.card κ) :=
  (etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision ρ).trans
    (mul_le_mul_of_nonneg_left uniformOn_not_injective_le zero_le)

omit [Fintype κ] in
/-- Real total-variation (`tvDist`) form of
`etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * (uniformOn (Set.univ : Set (ι → κ))).real {k | ¬ Function.Injective k} := by
  have hr := ENNReal.toReal_mono (by finiteness)
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision (ι := ι) ρ)
  simpa [tvDist, measureReal_def] using hr

/-- Real total-variation (`tvDist`) form of
`etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) :=
  (tvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision ρ).trans
    (mul_le_mul_of_nonneg_left
      uniformOn_real_not_injective_le_one_sub_descFactorial_div_pow zero_le_two)

/-- Real total-variation (`tvDist`) form of
`etvDist_sampleWithoutReplacement_sampleWithReplacement_le`. No `[Nonempty κ]` assumption is
needed: when `κ` is empty, either `ι` is empty and both sampling laws coincide, or `ι` is nonempty
and both sampling laws vanish while division by `0` in `ℝ` evaluates to `0`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((Fintype.card ι).choose 2 / (Fintype.card κ : ℝ)) :=
  (tvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision ρ).trans
    (mul_le_mul_of_nonneg_left uniformOn_real_not_injective_le zero_le_two)

omit [Fintype κ] in
/-- For every subset `A` (measurable or not), the real masses of `A` under sampling without and
with replacement differ by at most the real collision mass — without the factor of `2` present in
Mathlib's `tvDist`. -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      (uniformOn (Set.univ : Set (ι → κ))).real {k | ¬ Function.Injective k} := by
  simp only [abs_sub_le_iff, sub_le_iff_le_add', measureReal_def]
  exact ⟨ENNReal.toReal_le_add
      (sampleWithoutReplacement_le_sampleWithReplacement_add_collision (ρ := ρ) A)
      (by finiteness) (by finiteness),
    ENNReal.toReal_le_add
      (sampleWithReplacement_le_sampleWithoutReplacement_add_collision (ρ := ρ) A)
      (by finiteness) (by finiteness)⟩

/-- Real eventwise bound with the exact falling-factorial collision error (factor `1`, for
arbitrary subsets `A`). -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι :=
  (abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_collision ρ A).trans
    uniformOn_real_not_injective_le_one_sub_descFactorial_div_pow

/-- Real eventwise bound with the pairwise union-bound error `choose |ι| 2 / |κ|` (factor `1`, for
arbitrary subsets `A` and without `[Nonempty κ]`). -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      (Fintype.card ι).choose 2 / (Fintype.card κ : ℝ) :=
  (abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_collision ρ A).trans
    uniformOn_real_not_injective_le

end CollisionBounds

end TauCeti.Probability

end
