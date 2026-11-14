/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.PopulationSampling.Finite

/-!
# Total variation distance between sampling with and without replacement

For a random finite population `x : κ → α` with law `ρ`, sampling without replacement and sampling
with replacement differ on each event by at most the uniform-measure mass of colliding index
selections (`sampleWithoutReplacement_le_sampleWithReplacement_add_collision`,
`sampleWithReplacement_le_sampleWithoutReplacement_add_collision`). This file turns those eventwise
estimates into bounds on the one-sided excesses over measurable events and on Mathlib's total
variation distance `MeasureTheory.etvDist`.

With Mathlib's signed-measure normalization `etvDist P Q = ‖P - Q‖`, the total variation distance
between two probability measures is twice the largest one-sided excess `⨆ A, P A - Q A`. When an
embedding `ι ↪ κ` exists, both sampling laws preserve the total mass of any finite population law
`ρ`, so `etvDist` is twice the excess even before normalizing `ρ`
(`etvDist_sampleWithoutReplacement_sampleWithReplacement_eq_two_mul_iSup_sub`).

For any probability population law `ρ`, neither the excess bounds nor the `etvDist` bounds need an
embedding `ι ↪ κ` or a nonempty selection space `ι → κ`: when `ι → κ` is empty both sampling laws
are zero, and when `|ι| > |κ| > 0` every index map collides so the collision mass is one. Both the
exact collision formula `1 - (|κ|)_{|ι|} / |κ|^{|ι|}` and the pairwise union bound
`choose |ι| 2 / |κ|` therefore hold unconditionally. Sharpness for deterministic populations of
distinct values is proved in `TauCeti.Probability.PopulationSampling.Distinct`.

## Main declarations

* `etvDist_sampleWithoutReplacement_sampleWithReplacement_eq_two_mul_iSup_sub`: when an embedding
  `ι ↪ κ` exists, `etvDist` is twice the largest measurable-event excess;
* `sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision`: closed-form eventwise
  exact-collision bounds;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision`,
  `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_exact_collision`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_exact_collision`: excess bounds;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le`: total-variation bounds.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ α : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace α]

/-- When an injective selection exists, sampling without and with replacement give a finite
population law the same total mass, so Mathlib's total variation distance `etvDist` is twice the
largest excess over measurable events. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_eq_two_mul_iSup_sub
    [Fintype ι] [Finite κ] (ρ : Measure (κ → α)) [IsFiniteMeasure ρ] (e : ι ↪ κ) :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) =
      2 * ⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A := by
  let : Nonempty (ι → κ) := ⟨e⟩
  exact etvDist_eq_two_mul_iSup_sub
    ((sampleWithoutReplacement_univ ρ e).trans (sampleWithReplacement_univ ρ).symm)

section Collision

variable [Fintype ι] [Finite κ] {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ]

/-- The largest excess of sampling without replacement over sampling with replacement is at most
the uniform-measure mass of colliding index selections. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A) ≤
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} :=
  iSup₂_le fun A _ =>
    tsub_le_iff_left.mpr (sampleWithoutReplacement_le_sampleWithReplacement_add_collision A)

/-- The largest excess of sampling with replacement over sampling without replacement is at most
the uniform-measure mass of colliding index selections. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (ι := ι) ρ A - sampleWithoutReplacement (ι := ι) ρ A) ≤
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} :=
  iSup₂_le fun A _ =>
    tsub_le_iff_left.mpr (sampleWithReplacement_le_sampleWithoutReplacement_add_collision A)

/-- Mathlib's total variation distance between sampling without and with replacement from a random
finite population is at most twice the uniform-measure mass of colliding index selections. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ => sampleWithoutReplacement_le_sampleWithReplacement_add_collision A)
    (fun A _ => sampleWithReplacement_le_sampleWithoutReplacement_add_collision A)

end Collision

section Fintype

variable [Fintype ι] [Fintype κ]

private theorem uniformOn_not_injective_le_one_sub :
    uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty (ι → κ) with h | h
  · simp [Set.eq_empty_of_isEmpty (Set.univ : Set (ι → κ))]
  · exact uniformOn_not_injective_apply_eq.le

variable {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ]

/-- **Exact-collision finite sampling bound, without replacement to with replacement.** For every
event, sampling without replacement exceeds sampling with replacement by at most
`1 - (|κ|)_{|ι|} / |κ|^{|ι|}`. No nonemptiness assumption on `ι → κ` is needed. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision (A : Set (ι → α)) :
    sampleWithoutReplacement (ι := ι) ρ A ≤ sampleWithReplacement (ι := ι) ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (sampleWithoutReplacement_le_sampleWithReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le_one_sub)

/-- **Exact-collision finite sampling bound, with replacement to without replacement.** For every
event, sampling with replacement exceeds sampling without replacement by at most
`1 - (|κ|)_{|ι|} / |κ|^{|ι|}`. No nonemptiness assumption on `ι → κ` is needed. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision (A : Set (ι → α)) :
    sampleWithReplacement (ι := ι) ρ A ≤ sampleWithoutReplacement (ι := ι) ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (sampleWithReplacement_le_sampleWithoutReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le_one_sub)

/-- The largest excess of sampling without replacement over sampling with replacement is at most
`1 - (|κ|)_{|ι|} / |κ|^{|ι|}`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_exact_collision :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) ρ A - sampleWithReplacement (ι := ι) ρ A) ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  iSup_sampleWithoutReplacement_sub_sampleWithReplacement_le_collision.trans
    uniformOn_not_injective_le_one_sub

/-- The largest excess of sampling with replacement over sampling without replacement is at most
`1 - (|κ|)_{|ι|} / |κ|^{|ι|}`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_exact_collision :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (ι := ι) ρ A - sampleWithoutReplacement (ι := ι) ρ A) ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  iSup_sampleWithReplacement_sub_sampleWithoutReplacement_le_collision.trans
    uniformOn_not_injective_le_one_sub

/-- **Exact-collision total-variation bound for finite population sampling.** Mathlib's total
variation distance `etvDist` between sampling without and with replacement from a random finite
population is at most `2 * (1 - (|κ|)_{|ι|} / |κ|^{|ι|})`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision.trans
    (mul_le_mul_right uniformOn_not_injective_le_one_sub 2)

/-- **Quantitative total-variation bound for finite population sampling.** Mathlib's total
variation distance `etvDist` between sampling without and with replacement from a random finite
population is at most `2 * (choose |ι| 2 / |κ|)`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((Fintype.card ι).choose 2 / Fintype.card κ) :=
  etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision.trans
    (mul_le_mul_right uniformOn_not_injective_le 2)

end Fintype

end TauCeti.Probability
