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
`ι → κ`. Conditioning on the drawn population integrates deterministic-population discrepancy bounds
into bounds on eventwise excess, extended total variation distance (`etvDist`), real total
variation distance (`tvDist`), and real event probabilities (`Measure.real`).

This file develops:

1. **Population-mixture discrepancy bounds** for general `samplePopulation σ₁ ρ` and
   `samplePopulation σ₂ ρ`, including two-regime mixtures over a measurable population event `S`
   and its complement `Sᶜ`, both in `ℝ≥0∞` and in the real-saving form `C - δ * (ρ S).toReal`.
2. **Vanishing-discrepancy regimes**: subsingleton samples (`|ι| ≤ 1`) and constant deterministic
   populations, where sampling without and with replacement coincide.
3. **Random-population collision bounds** for `sampleWithoutReplacement ρ` against
   `sampleWithReplacement ρ`: one-sided measurable-event excesses, `etvDist`, `tvDist`, and real
   eventwise differences `|P.real A - Q.real A|` in the collision-event form, the exact
   falling-factorial form `1 - (|κ|)_|ι| / |κ| ^ |ι|`, and the pairwise union-bound form
   `choose |ι| 2 / |κ|`, with no nonemptiness or embedding assumptions needed on the upper bounds.
4. **Constant-population mixture sharpening**: when an embedding `ι ↪ κ` exists and `ρ` places
   mass on a measurable set `S` of constant populations, the collision error scales by `ρ Sᶜ`
   (equivalently `1 - (ρ S).toReal`).

## Main declarations

* `iSup_samplePopulation_sub_le_lintegral`, `etvDist_samplePopulation_le_lintegral_add_lintegral`,
  `etvDist_samplePopulation_le_two_mul_lintegral`: population-mixture excess and total-variation
  bounds;
* `etvDist_samplePopulation_le_two_mul_ofReal_sub_mul_toReal`,
  `tvDist_samplePopulation_le_two_mul_sub_mul_toReal`: two-regime mixture bounds with real savings;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le`: random-population `etvDist` bounds,
  together with their `tvDist` and `Measure.real` companions;
* `sampleWithoutReplacement_le_sampleWithReplacement_add_mul_compl_of_const`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_le_two_mul_compl_of_const`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_le_two_mul_compl_of_const`: sharpening
  when the population is constant on a measurable event.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section SamplePopulation

variable {ι κ α : Type*} [MeasurableSpace κ] [MeasurableSpace α]

section Mixture

variable [Countable κ] [MeasurableSingletonClass κ]

/-- Integrating populationwise upper bounds across an s-finite population law bounds the largest
measurable-event excess between the two sampled laws. -/
theorem iSup_samplePopulation_sub_le_lintegral
    {σ₁ σ₂ : Measure (ι → κ)} [SFinite σ₁] [SFinite σ₂] {ρ : Measure (κ → α)} [SFinite ρ]
    {g : (κ → α) → ℝ≥0∞}
    (h : ∀ A, MeasurableSet A → ∀ᵐ x ∂ρ,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + g x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      samplePopulation σ₁ ρ A - samplePopulation σ₂ ρ A) ≤ ∫⁻ x, g x ∂ρ :=
  iSup₂_le fun A hA =>
    tsub_le_iff_left.2 (samplePopulation_le_add_lintegral_of_measurableSet hA (h A hA))

/-- Integrating populationwise upper bounds in both directions bounds `etvDist` between two
sampled laws, without assuming equal total mass of the selection laws. -/
theorem etvDist_samplePopulation_le_lintegral_add_lintegral
    {σ₁ σ₂ : Measure (ι → κ)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    {ρ : Measure (κ → α)} [IsFiniteMeasure ρ] {g₁ g₂ : (κ → α) → ℝ≥0∞}
    (h₁ : ∀ A, MeasurableSet A → ∀ᵐ x ∂ρ,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + g₁ x)
    (h₂ : ∀ A, MeasurableSet A → ∀ᵐ x ∂ρ,
      samplePopulation σ₂ (Measure.dirac x) A ≤
        samplePopulation σ₁ (Measure.dirac x) A + g₂ x) :
    etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) ≤
      (∫⁻ x, g₁ x ∂ρ) + ∫⁻ x, g₂ x ∂ρ :=
  etvDist_le_of_forall_le_add
    (fun A hA => samplePopulation_le_add_lintegral_of_measurableSet hA (h₁ A hA))
    (fun A hA => samplePopulation_le_add_lintegral_of_measurableSet hA (h₂ A hA))

/-- When two finite selection laws have equal total mass, one-sided populationwise event bounds
suffice to bound `etvDist` between the sampled laws by twice the integrated error. -/
theorem etvDist_samplePopulation_le_two_mul_lintegral
    {σ₁ σ₂ : Measure (ι → κ)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    {ρ : Measure (κ → α)} [IsFiniteMeasure ρ] (hσ : σ₁ Set.univ = σ₂ Set.univ)
    {g : (κ → α) → ℝ≥0∞}
    (h : ∀ A, MeasurableSet A → ∀ᵐ x ∂ρ,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + g x) :
    etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) ≤ 2 * ∫⁻ x, g x ∂ρ := by
  have huniv : samplePopulation σ₁ ρ Set.univ = samplePopulation σ₂ ρ Set.univ := by
    simp [samplePopulation_apply_population MeasurableSet.univ, hσ]
  exact (etvDist_le_two_mul_iff huniv).2 fun A hA =>
    samplePopulation_le_add_lintegral_of_measurableSet hA (h A hA)

/-- Two-regime total-variation mixture bound: for selection laws of equal total mass, one-sided
deterministic bounds `c₁` on a measurable set `S` of populations and `c₂` on `Sᶜ` bound `etvDist`
by `2 * (c₁ * ρ S + c₂ * ρ Sᶜ)`. -/
theorem etvDist_samplePopulation_le_two_mul_add_compl
    {σ₁ σ₂ : Measure (ι → κ)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    {ρ : Measure (κ → α)} [IsFiniteMeasure ρ] (hσ : σ₁ Set.univ = σ₂ Set.univ)
    {S : Set (κ → α)} (hS : MeasurableSet S) {c₁ c₂ : ℝ≥0∞}
    (h₁ : ∀ A, MeasurableSet A → ∀ x ∈ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + c₁)
    (h₂ : ∀ A, MeasurableSet A → ∀ x ∉ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + c₂) :
    etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) ≤
      2 * (c₁ * ρ S + c₂ * ρ Sᶜ) := by
  have huniv : samplePopulation σ₁ ρ Set.univ = samplePopulation σ₂ ρ Set.univ := by
    simp [samplePopulation_apply_population MeasurableSet.univ, hσ]
  exact (etvDist_le_two_mul_iff huniv).2 fun A hA =>
    samplePopulation_le_add_mul_measure_add_compl_of_measurableSet hS hA (h₁ A hA) (h₂ A hA)

/-- Real-saving `etvDist` mixture bound for a probability population law and selection laws of
equal total mass: improving a universal upper bound `C ≥ 0` by `δ ≤ C` on a measurable set `S`
gives `etvDist ≤ 2 * ENNReal.ofReal (C - δ * (ρ S).toReal)`. -/
theorem etvDist_samplePopulation_le_two_mul_ofReal_sub_mul_toReal
    {σ₁ σ₂ : Measure (ι → κ)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (hσ : σ₁ Set.univ = σ₂ Set.univ)
    {S : Set (κ → α)} (hS : MeasurableSet S) {C δ : ℝ} (hC : 0 ≤ C) (hδC : δ ≤ C)
    (h₁ : ∀ A, MeasurableSet A → ∀ x ∈ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + ENNReal.ofReal (C - δ))
    (h₂ : ∀ A, MeasurableSet A → ∀ x ∉ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + ENNReal.ofReal C) :
    etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) ≤
      2 * ENNReal.ofReal (C - δ * (ρ S).toReal) := by
  have huniv : samplePopulation σ₁ ρ Set.univ = samplePopulation σ₂ ρ Set.univ := by
    simp [samplePopulation_apply_population MeasurableSet.univ, hσ]
  exact (etvDist_le_two_mul_iff huniv).2 fun A hA =>
    samplePopulation_le_add_ofReal_sub_mul_toReal_of_measurableSet hS hC hδC hA
      (h₁ A hA) (h₂ A hA)

/-- Real total-variation (`tvDist`) companion to
`etvDist_samplePopulation_le_two_mul_ofReal_sub_mul_toReal`. -/
theorem tvDist_samplePopulation_le_two_mul_sub_mul_toReal
    {σ₁ σ₂ : Measure (ι → κ)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (hσ : σ₁ Set.univ = σ₂ Set.univ)
    {S : Set (κ → α)} (hS : MeasurableSet S) {C δ : ℝ} (hC : 0 ≤ C) (hδC : δ ≤ C)
    (h₁ : ∀ A, MeasurableSet A → ∀ x ∈ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + ENNReal.ofReal (C - δ))
    (h₂ : ∀ A, MeasurableSet A → ∀ x ∉ S,
      samplePopulation σ₁ (Measure.dirac x) A ≤
        samplePopulation σ₂ (Measure.dirac x) A + ENNReal.ofReal C) :
    tvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) ≤
      2 * (C - δ * (ρ S).toReal) := by
  have hq_le : (ρ S).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := S))
  have hnonneg : 0 ≤ C - δ * (ρ S).toReal := by
    have : δ * (ρ S).toReal ≤ C * (ρ S).toReal + (C - C * (ρ S).toReal) := by
      have h1 : δ * (ρ S).toReal ≤ C * (ρ S).toReal :=
        mul_le_mul_of_nonneg_right hδC ENNReal.toReal_nonneg
      have h2 : 0 ≤ C * (1 - (ρ S).toReal) := mul_nonneg hC (sub_nonneg.2 hq_le)
      linarith
    linarith
  have hetv := etvDist_samplePopulation_le_two_mul_ofReal_sub_mul_toReal (ρ := ρ) hσ hS hC hδC
    h₁ h₂
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
    hetv
  simpa [tvDist, ENNReal.toReal_ofReal hnonneg] using hr

end Mixture

section Vanishing

/-- On a subsingleton sample index, `etvDist` between sampling without and with replacement is
zero for every finite population law. -/
@[simp]
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_of_subsingleton
    [Fintype ι] [Subsingleton ι] (ρ : Measure (κ → α)) [IsFiniteMeasure ρ] :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) = 0 := by
  simp [sampleWithoutReplacement_eq_sampleWithReplacement]

/-- On a subsingleton sample index, `tvDist` between sampling without and with replacement is
zero for every finite population law. -/
@[simp]
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_of_subsingleton
    [Fintype ι] [Subsingleton ι] (ρ : Measure (κ → α)) [IsFiniteMeasure ρ] :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) = 0 := by
  simp [tvDist]

/-- For a constant deterministic population and an embedding `ι ↪ κ`, `etvDist` between sampling
without and with replacement vanishes. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_of_const
    [Fintype ι] [Finite κ] [MeasurableSingletonClass κ] {x : κ → α}
    (hx : ∀ k₁ k₂, x k₁ = x k₂) (e : ι ↪ κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
      (sampleWithReplacement (ι := ι) (Measure.dirac x)) = 0 := by
  rw [sampleWithoutReplacement_dirac_eq_sampleWithReplacement_dirac_of_const hx e]
  simp

/-- For a constant deterministic population and an embedding `ι ↪ κ`, `tvDist` between sampling
without and with replacement vanishes. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_of_const
    [Fintype ι] [Finite κ] [MeasurableSingletonClass κ] {x : κ → α}
    (hx : ∀ k₁ k₂, x k₁ = x k₂) (e : ι ↪ κ) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
      (sampleWithReplacement (ι := ι) (Measure.dirac x)) = 0 := by
  rw [tvDist, etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_of_const hx e]
  simp

end Vanishing

end SamplePopulation

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
        (Fintype.card κ : ℝ) ^ Fintype.card ι) := by
  have hfin : (2 : ℝ≥0∞) * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hr := ENNReal.toReal_mono hfin
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision (ι := ι) ρ)
  simpa [tvDist, toReal_one_sub_descFactorial_div_pow] using hr

/-- Real total-variation (`tvDist`) form of
`etvDist_sampleWithoutReplacement_sampleWithReplacement_le`. No `[Nonempty κ]` assumption is
needed: when `κ` is empty, either `ι` is empty and both sampling laws coincide, or `ι` is nonempty
and both sampling laws vanish while division by `0` in `ℝ` evaluates to `0`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((Fintype.card ι).choose 2 / (Fintype.card κ : ℝ)) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    · have : IsEmpty (ι ↪ κ) := ⟨fun e => isEmptyElim (e (Classical.arbitrary ι))⟩
      have : IsEmpty (ι → κ) := ⟨fun f => isEmptyElim (f (Classical.arbitrary ι))⟩
      simp [tvDist]
  · have hfin : (2 : ℝ≥0∞) * ((Fintype.card ι).choose 2 / Fintype.card κ) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Fintype.card_ne_zero]))
    have hr := ENNReal.toReal_mono hfin
      (etvDist_sampleWithoutReplacement_sampleWithReplacement_le (ι := ι) ρ)
    simpa [tvDist] using hr

omit [Fintype κ] in
/-- For every subset `A` (measurable or not), the real masses of `A` under sampling without and
with replacement differ by at most the real collision mass — without the factor of `2` present in
Mathlib's `tvDist`. -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_collision [Finite κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      (uniformOn (Set.univ : Set (ι → κ))).real {k | ¬ Function.Injective k} := by
  rw [abs_sub_le_iff]
  constructor
  · have h := ENNReal.toReal_mono (by finiteness)
      (sampleWithoutReplacement_le_sampleWithReplacement_add_collision (ρ := ρ) A)
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    simpa [measureReal_def] using sub_le_iff_le_add'.2 h
  · have h := ENNReal.toReal_mono (by finiteness)
      (sampleWithReplacement_le_sampleWithoutReplacement_add_collision (ρ := ρ) A)
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    simpa [measureReal_def] using sub_le_iff_le_add'.2 h

/-- Real eventwise bound with the exact falling-factorial collision error (factor `1`, for
arbitrary subsets `A`). -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_exact_collision
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι := by
  have hc : (1 : ℝ≥0∞) - (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [abs_sub_le_iff]
  constructor
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨by finiteness, hc⟩)
      (sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision (ρ := ρ) A)
    rw [ENNReal.toReal_add (by finiteness) hc, toReal_one_sub_descFactorial_div_pow] at h
    simpa [measureReal_def] using sub_le_iff_le_add'.2 h
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨by finiteness, hc⟩)
      (sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision (ρ := ρ) A)
    rw [ENNReal.toReal_add (by finiteness) hc, toReal_one_sub_descFactorial_div_pow] at h
    simpa [measureReal_def] using sub_le_iff_le_add'.2 h

/-- Real eventwise bound with the pairwise union-bound error `choose |ι| 2 / |κ|` (factor `1`, for
arbitrary subsets `A` and without `[Nonempty κ]`). -/
theorem abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    |(sampleWithoutReplacement (ι := ι) ρ).real A -
        (sampleWithReplacement (ι := ι) ρ).real A| ≤
      (Fintype.card ι).choose 2 / (Fintype.card κ : ℝ) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [sampleWithoutReplacement_eq_sampleWithReplacement]
    · have : IsEmpty (ι ↪ κ) := ⟨fun e => isEmptyElim (e (Classical.arbitrary ι))⟩
      have : IsEmpty (ι → κ) := ⟨fun f => isEmptyElim (f (Classical.arbitrary ι))⟩
      simp
  · have hc : ((Fintype.card ι).choose 2 : ℝ≥0∞) / Fintype.card κ ≠ ∞ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Fintype.card_ne_zero])
    rw [abs_sub_le_iff]
    constructor
    · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨by finiteness, hc⟩)
        (sampleWithoutReplacement_le_sampleWithReplacement_add (ρ := ρ) A)
      rw [ENNReal.toReal_add (by finiteness) hc] at h
      simpa [measureReal_def] using sub_le_iff_le_add'.2 h
    · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨by finiteness, hc⟩)
        (sampleWithReplacement_le_sampleWithoutReplacement_add (ρ := ρ) A)
      rw [ENNReal.toReal_add (by finiteness) hc] at h
      simpa [measureReal_def] using sub_le_iff_le_add'.2 h

section ConstantPopulationMixture

/-- When an embedding `ι ↪ κ` exists and `S` is a measurable set of constant populations, sampling
without replacement exceeds sampling with replacement on any event by at most the exact collision
probability weighted by `ρ Sᶜ`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add_mul_compl_of_const
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (e : ι ↪ κ)
    {S : Set (κ → α)} (hS : MeasurableSet S) (hS' : ∀ x ∈ S, ∀ k₁ k₂, x k₁ = x k₂)
    (A : Set (ι → α)) :
    sampleWithoutReplacement (ι := ι) ρ A ≤ sampleWithReplacement (ι := ι) ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) * ρ Sᶜ := by
  let c := 1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn]
  calc
    samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A
        ≤ samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A + (0 * ρ S + c * ρ Sᶜ) :=
          samplePopulation_le_add_mul_measure_add_compl hS
            (fun B _ x hx => by
              have heq := sampleWithoutReplacement_dirac_eq_sampleWithReplacement_dirac_of_const
                (hS' x hx) e
              rw [sampleWithoutReplacement_def,
                sampleWithReplacement_eq_samplePopulation_uniformOn] at heq
              simp [heq])
            (fun B _ x _ => by
              simpa [sampleWithoutReplacement_def,
                sampleWithReplacement_eq_samplePopulation_uniformOn, c] using
                sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision
                  (ρ := Measure.dirac x) B)
            A
    _ = samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A + c * ρ Sᶜ := by simp

/-- Converse of `sampleWithoutReplacement_le_sampleWithReplacement_add_mul_compl_of_const`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_mul_compl_of_const
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (e : ι ↪ κ)
    {S : Set (κ → α)} (hS : MeasurableSet S) (hS' : ∀ x ∈ S, ∀ k₁ k₂, x k₁ = x k₂)
    (A : Set (ι → α)) :
    sampleWithReplacement (ι := ι) ρ A ≤ sampleWithoutReplacement (ι := ι) ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) * ρ Sᶜ := by
  let c := 1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn]
  calc
    samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A
        ≤ samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A +
            (0 * ρ S + c * ρ Sᶜ) :=
          samplePopulation_le_add_mul_measure_add_compl hS
            (fun B _ x hx => by
              have heq := sampleWithoutReplacement_dirac_eq_sampleWithReplacement_dirac_of_const
                (hS' x hx) e
              rw [sampleWithoutReplacement_def,
                sampleWithReplacement_eq_samplePopulation_uniformOn] at heq
              simp [heq])
            (fun B _ x _ => by
              simpa [sampleWithoutReplacement_def,
                sampleWithReplacement_eq_samplePopulation_uniformOn, c] using
                sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision
                  (ρ := Measure.dirac x) B)
            A
    _ = samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A + c * ρ Sᶜ := by simp

/-- Total-variation (`etvDist`) sharpening when `ρ` places mass on a measurable set `S` of
constant populations. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_le_two_mul_compl_of_const
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (e : ι ↪ κ)
    {S : Set (κ → α)} (hS : MeasurableSet S) (hS' : ∀ x ∈ S, ∀ k₁ k₂, x k₁ = x k₂) :
    etvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) * ρ Sᶜ) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ => sampleWithoutReplacement_le_sampleWithReplacement_add_mul_compl_of_const
      ρ e hS hS' A)
    (fun A _ => sampleWithReplacement_le_sampleWithoutReplacement_add_mul_compl_of_const
      ρ e hS hS' A)

/-- Real total-variation (`tvDist`) sharpening when `ρ` places mass on a measurable set `S` of
constant populations: the exact collision bound scales by `1 - (ρ S).toReal`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_le_two_mul_compl_of_const
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (e : ι ↪ κ)
    {S : Set (κ → α)} (hS : MeasurableSet S) (hS' : ∀ x ∈ S, ∀ k₁ k₂, x k₁ = x k₂) :
    tvDist (sampleWithoutReplacement (ι := ι) ρ) (sampleWithReplacement (ι := ι) ρ) ≤
      2 * ((1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) * (1 - (ρ S).toReal)) := by
  let _ : Nonempty (ι → κ) := ⟨e⟩
  let _ : IsProbabilityMeasure (uniformOn {k : ι → κ | Function.Injective k}) :=
    isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨e, e.injective⟩
  let C : ℝ := 1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ) ^ Fintype.card ι
  have hC_eq : ENNReal.ofReal C = 1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
    dsimp only [C]
    rw [← toReal_one_sub_descFactorial_div_pow,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  have hC : 0 ≤ C := by
    dsimp only [C]
    rw [← toReal_one_sub_descFactorial_div_pow]
    exact ENNReal.toReal_nonneg
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn]
  have h := tvDist_samplePopulation_le_two_mul_sub_mul_toReal
    (σ₁ := uniformOn {k : ι → κ | Function.Injective k})
    (σ₂ := uniformOn (Set.univ : Set (ι → κ))) (ρ := ρ)
    (by simp) hS hC le_rfl
    (fun A _ x hx => by
      have heq := sampleWithoutReplacement_dirac_eq_sampleWithReplacement_dirac_of_const
        (hS' x hx) e
      rw [sampleWithoutReplacement_def,
        sampleWithReplacement_eq_samplePopulation_uniformOn] at heq
      simp [heq])
    (fun A _ x _ => by
      rw [hC_eq]
      simpa [sampleWithoutReplacement_def,
        sampleWithReplacement_eq_samplePopulation_uniformOn] using
        sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision
          (ρ := Measure.dirac x) A)
  exact h.trans_eq (by ring)

end ConstantPopulationMixture

end CollisionBounds

end TauCeti.Probability

end
