/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Map
public import TauCeti.Probability.PopulationSampling.Distinct
import TauCeti.Logic.Function.Update
import TauCeti.MeasureTheory.MeasurableSpace.Embedding

/-!
# Sampling discrepancy under observations and repeated-value factorizations

Observing population values through a measurable map `g : α → β` commutes with
`TauCeti.Probability.samplePopulation` (`samplePopulation_map`, `samplePopulation_dirac_comp`).
Combined with pushforward contraction of eventwise excess and total variation
(`MeasureTheory.iSup_measure_map_sub_le`, `MeasureTheory.etvDist_map_le`), observing a population
cannot increase the sampling discrepancy between any two selection laws `σ₁` and `σ₂`, and in
particular between sampling without replacement and sampling with replacement.

When the sample index `ι` is countable and `g` is a measurable embedding, coordinatewise
postcomposition `(fun y i => g (y i)) = Pi.map (fun _ => g)` is again a measurable embedding
(`MeasurableEmbedding.piMap`), so both the eventwise excess and `etvDist` are preserved with
equality. In particular, when the value space `α` has measurable singletons, any injective
deterministic population `x : κ → α` on a countable index type is a measurable embedding, so its
sampling discrepancy along arbitrary selection laws equals that of the canonical index population
`id : κ → κ`. For finite sampling with and without replacement this recovers the exact collision
excess and total variation distance without assuming measurability of the all-distinct event
`{f : ι → α | Function.Injective f}` on `ι → α` (which can fail on uncountable spaces with
measurable singletons whose product lacks a measurable diagonal).

Conversely, for an arbitrary measurable space `α` with no separation or singleton assumptions, if
a deterministic population `x : κ → α` identifies two indices (`x a = x b`), then `x` factors as
`x ∘ Function.update id b a` (`Function.comp_update_id_eq_self_iff`) and is automatically
measurable because `κ` is countable with measurable singletons. Both sampling laws of `x` are
therefore pushforwards along `f ↦ x ∘ f` of those of the one-pair population
`Function.update id b a : κ → κ`, contracting excess in both directions and `etvDist` to the
one-pair case.

## Main statements

* `iSup_samplePopulation_map_sub_le`, `etvDist_samplePopulation_map_le`: measurable observations
  contract sampling excess and `etvDist` for s-finite population laws;
* `iSup_samplePopulation_map_sub_eq`, `etvDist_samplePopulation_map_eq`: measurable-embedding
  observations over a countable sample index preserve them;
* `iSup_samplePopulation_dirac_sub_eq_id`, `etvDist_samplePopulation_dirac_eq_id`: an injective
  deterministic population into a space with measurable singletons has the same discrepancy as
  `id : κ → κ`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_of_injective`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective`: exact finite
  sampling discrepancy for injective populations into a space with measurable singletons, without
  a diagonal-measurability hypothesis;
* `samplePopulation_dirac_eq_map_update_id`, `iSup_samplePopulation_dirac_sub_le_update_id`,
  `etvDist_samplePopulation_dirac_le_update_id`: factorization and discrepancy reduction to
  `Function.update id b a` whenever `x a = x b`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_update_id`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_update_id`: both one-sided
  excesses and `etvDist` between finite sampling without and with replacement are bounded by the
  one-pair population whenever `x a = x b`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section SamplePopulation

variable {ι κ α β : Type*} [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α] [MeasurableSpace β]

/-- Observing population values through a measurable map contracts the largest eventwise excess
between `samplePopulation` along any two selection laws. -/
theorem iSup_samplePopulation_map_sub_le (σ₁ σ₂ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [SFinite ρ] {g : α → β} (hg : Measurable g) :
    (⨆ (B : Set (ι → β)) (_ : MeasurableSet B),
        samplePopulation σ₁ (ρ.map fun x i => g (x i)) B -
          samplePopulation σ₂ (ρ.map fun x i => g (x i)) B) ≤
      ⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ ρ A - samplePopulation σ₂ ρ A := by
  rw [samplePopulation_map σ₁ ρ hg, samplePopulation_map σ₂ ρ hg]
  exact iSup_measure_map_sub_le _ _ (by fun_prop)

/-- Observing population values through a measurable map contracts the extended total variation
distance between `samplePopulation` along any two selection laws. -/
theorem etvDist_samplePopulation_map_le (σ₁ σ₂ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [SFinite ρ] {g : α → β} (hg : Measurable g) :
    etvDist (samplePopulation σ₁ (ρ.map fun x i => g (x i)))
        (samplePopulation σ₂ (ρ.map fun x i => g (x i))) ≤
      etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) := by
  rw [samplePopulation_map σ₁ ρ hg, samplePopulation_map σ₂ ρ hg]
  exact etvDist_map_le _ _ (by fun_prop)

/-- Over a countable sample index, observing population values through a measurable embedding
preserves the largest eventwise excess between `samplePopulation` along any two selection laws. -/
theorem iSup_samplePopulation_map_sub_eq [Countable ι] (σ₁ σ₂ : Measure (ι → κ))
    (ρ : Measure (κ → α)) [SFinite ρ] {g : α → β} (hg : MeasurableEmbedding g) :
    (⨆ (B : Set (ι → β)) (_ : MeasurableSet B),
        samplePopulation σ₁ (ρ.map fun x i => g (x i)) B -
          samplePopulation σ₂ (ρ.map fun x i => g (x i)) B) =
      ⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ ρ A - samplePopulation σ₂ ρ A := by
  rw [samplePopulation_map σ₁ ρ hg.measurable, samplePopulation_map σ₂ ρ hg.measurable]
  exact (MeasurableEmbedding.piMap fun _ : ι => hg).iSup_measure_map_sub _ _

/-- Over a countable sample index, observing population values through a measurable embedding
preserves the extended total variation distance between `samplePopulation` along any two selection
laws. -/
theorem etvDist_samplePopulation_map_eq [Countable ι] (σ₁ σ₂ : Measure (ι → κ))
    (ρ : Measure (κ → α)) [SFinite ρ] {g : α → β} (hg : MeasurableEmbedding g) :
    etvDist (samplePopulation σ₁ (ρ.map fun x i => g (x i)))
        (samplePopulation σ₂ (ρ.map fun x i => g (x i))) =
      etvDist (samplePopulation σ₁ ρ) (samplePopulation σ₂ ρ) := by
  rw [samplePopulation_map σ₁ ρ hg.measurable, samplePopulation_map σ₂ ρ hg.measurable]
  exact (MeasurableEmbedding.piMap fun _ : ι => hg).etvDist_map _ _

/-- Composing a deterministic population with a measurable map contracts the largest eventwise
excess between `samplePopulation` along any two selection laws, without s-finiteness assumptions
on the selection laws. -/
theorem iSup_samplePopulation_dirac_comp_sub_le (σ₁ σ₂ : Measure (ι → κ)) (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    (⨆ (B : Set (ι → β)) (_ : MeasurableSet B),
        samplePopulation σ₁ (Measure.dirac (g ∘ x)) B -
          samplePopulation σ₂ (Measure.dirac (g ∘ x)) B) ≤
      ⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ (Measure.dirac x) A - samplePopulation σ₂ (Measure.dirac x) A := by
  rw [samplePopulation_dirac_comp σ₁ x hg, samplePopulation_dirac_comp σ₂ x hg]
  exact iSup_measure_map_sub_le _ _ (by fun_prop)

/-- Composing a deterministic population with a measurable map contracts the extended total
variation distance between `samplePopulation` along any two selection laws. -/
theorem etvDist_samplePopulation_dirac_comp_le (σ₁ σ₂ : Measure (ι → κ)) (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    etvDist (samplePopulation σ₁ (Measure.dirac (g ∘ x)))
        (samplePopulation σ₂ (Measure.dirac (g ∘ x))) ≤
      etvDist (samplePopulation σ₁ (Measure.dirac x)) (samplePopulation σ₂ (Measure.dirac x)) := by
  rw [samplePopulation_dirac_comp σ₁ x hg, samplePopulation_dirac_comp σ₂ x hg]
  exact etvDist_map_le _ _ (by fun_prop)

/-- Over a countable sample index, composing a deterministic population with a measurable
embedding preserves the largest eventwise excess between `samplePopulation` along any two
selection laws. -/
theorem iSup_samplePopulation_dirac_comp_sub_eq [Countable ι] (σ₁ σ₂ : Measure (ι → κ))
    (x : κ → α) {g : α → β} (hg : MeasurableEmbedding g) :
    (⨆ (B : Set (ι → β)) (_ : MeasurableSet B),
        samplePopulation σ₁ (Measure.dirac (g ∘ x)) B -
          samplePopulation σ₂ (Measure.dirac (g ∘ x)) B) =
      ⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ (Measure.dirac x) A - samplePopulation σ₂ (Measure.dirac x) A := by
  rw [samplePopulation_dirac_comp σ₁ x hg.measurable,
    samplePopulation_dirac_comp σ₂ x hg.measurable]
  exact (MeasurableEmbedding.piMap fun _ : ι => hg).iSup_measure_map_sub _ _

/-- Over a countable sample index, composing a deterministic population with a measurable
embedding preserves the extended total variation distance between `samplePopulation` along any two
selection laws. -/
theorem etvDist_samplePopulation_dirac_comp_eq [Countable ι] (σ₁ σ₂ : Measure (ι → κ))
    (x : κ → α) {g : α → β} (hg : MeasurableEmbedding g) :
    etvDist (samplePopulation σ₁ (Measure.dirac (g ∘ x)))
        (samplePopulation σ₂ (Measure.dirac (g ∘ x))) =
      etvDist (samplePopulation σ₁ (Measure.dirac x)) (samplePopulation σ₂ (Measure.dirac x)) := by
  rw [samplePopulation_dirac_comp σ₁ x hg.measurable,
    samplePopulation_dirac_comp σ₂ x hg.measurable]
  exact (MeasurableEmbedding.piMap fun _ : ι => hg).etvDist_map _ _

/-- Over a countable sample index and a value space with measurable singletons, an injective
deterministic population has the same largest eventwise excess along any two selection laws as the
canonical index population `id : κ → κ`. -/
theorem iSup_samplePopulation_dirac_sub_eq_id [Countable ι] [MeasurableSingletonClass α]
    (σ₁ σ₂ : Measure (ι → κ)) {x : κ → α} (hx : Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ (Measure.dirac x) A - samplePopulation σ₂ (Measure.dirac x) A) =
      ⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        samplePopulation σ₁ (Measure.dirac id) A - samplePopulation σ₂ (Measure.dirac id) A := by
  simpa only [Function.comp_id] using
    iSup_samplePopulation_dirac_comp_sub_eq σ₁ σ₂ id
      (MeasurableEmbedding.of_injective_of_countable (measurable_of_countable x) hx)

/-- Over a countable sample index and a value space with measurable singletons, an injective
deterministic population has the same extended total variation distance along any two selection
laws as the canonical index population `id : κ → κ`. -/
theorem etvDist_samplePopulation_dirac_eq_id [Countable ι] [MeasurableSingletonClass α]
    (σ₁ σ₂ : Measure (ι → κ)) {x : κ → α} (hx : Function.Injective x) :
    etvDist (samplePopulation σ₁ (Measure.dirac x)) (samplePopulation σ₂ (Measure.dirac x)) =
      etvDist (samplePopulation σ₁ (Measure.dirac id))
        (samplePopulation σ₂ (Measure.dirac id)) := by
  simpa only [Function.comp_id] using
    etvDist_samplePopulation_dirac_comp_eq σ₁ σ₂ id
      (MeasurableEmbedding.of_injective_of_countable (measurable_of_countable x) hx)

end SamplePopulation

section DistinctMeasurableSingletons

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- When the value space has measurable singletons, the largest excess between sampling a
distinct-valued finite population without and with replacement equals the collision probability
`1 - (n)_m / n^m`, without requiring measurability of `{f : ι → α | Function.Injective f}` in the
product space `ι → α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_of_injective
    {x : κ → α} (hx : Function.Injective x) (e : ι ↪ κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_def,
    iSup_samplePopulation_dirac_sub_eq_id _ _ hx, ← sampleWithoutReplacement_def,
    ← sampleWithReplacement_def]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq Function.injective_id e
    (Set.to_countable _).measurableSet

/-- When the value space has measurable singletons, the extended total variation distance between
sampling a distinct-valued finite population without and with replacement is twice the collision
probability, without requiring measurability of `{f : ι → α | Function.Injective f}` in `ι → α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective
    {x : κ → α} (hx : Function.Injective x) (e : ι ↪ κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_def,
    etvDist_samplePopulation_dirac_eq_id _ _ hx, ← sampleWithoutReplacement_def,
    ← sampleWithReplacement_def]
  exact etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq Function.injective_id e
    (Set.to_countable _).measurableSet

/-- When the value space has measurable singletons, the real total variation distance between
sampling a distinct-valued finite population without and with replacement is twice the collision
probability, without requiring measurability of `{f : ι → α | Function.Injective f}` in `ι → α`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective
    {x : κ → α} (hx : Function.Injective x) (e : ι ↪ κ) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_def, tvDist,
    etvDist_samplePopulation_dirac_eq_id _ _ hx, ← tvDist, ← sampleWithoutReplacement_def,
    ← sampleWithReplacement_def]
  exact tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq Function.injective_id e
    (Set.to_countable _).measurableSet

end DistinctMeasurableSingletons

section RepeatedValues

variable {ι κ α : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace α]

/-- If a deterministic population `x : κ → α` assigns the same value to indices `a` and `b`,
sampling `x` along any selection law pushes forward the sampling law of the one-pair population
`Function.update id b a` along `f ↦ x ∘ f`. No separation or singleton hypothesis on `α` and no
s-finiteness hypothesis on `σ` are required. -/
theorem samplePopulation_dirac_eq_map_update_id [Countable κ] [DecidableEq κ]
    (σ : Measure (ι → κ)) {x : κ → α} {a b : κ} (hxab : x a = x b) :
    samplePopulation σ (Measure.dirac x) =
      (samplePopulation σ (Measure.dirac (Function.update id b a))).map (fun f i => x (f i)) := by
  simpa only [Function.comp_update_id_eq_self_iff.2 hxab] using
    samplePopulation_dirac_comp σ (Function.update id b a) (measurable_of_countable x)

/-- If `x a = x b`, the largest eventwise excess between `samplePopulation` of `Measure.dirac x`
along any two selection laws is at most that of the one-pair population
`Function.update id b a`. -/
theorem iSup_samplePopulation_dirac_sub_le_update_id [Countable κ] [DecidableEq κ]
    (σ₁ σ₂ : Measure (ι → κ)) {x : κ → α} {a b : κ} (hxab : x a = x b) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        samplePopulation σ₁ (Measure.dirac x) A - samplePopulation σ₂ (Measure.dirac x) A) ≤
      ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
        samplePopulation σ₁ (Measure.dirac (Function.update id b a)) B -
          samplePopulation σ₂ (Measure.dirac (Function.update id b a)) B := by
  have hx := measurable_of_countable x
  rw [samplePopulation_dirac_eq_map_update_id σ₁ hxab,
    samplePopulation_dirac_eq_map_update_id σ₂ hxab]
  exact iSup_measure_map_sub_le _ _ (by fun_prop)

/-- If `x a = x b`, the extended total variation distance between `samplePopulation` of
`Measure.dirac x` along any two selection laws is at most that of the one-pair population
`Function.update id b a`. -/
theorem etvDist_samplePopulation_dirac_le_update_id [Countable κ] [DecidableEq κ]
    (σ₁ σ₂ : Measure (ι → κ)) {x : κ → α} {a b : κ} (hxab : x a = x b) :
    etvDist (samplePopulation σ₁ (Measure.dirac x)) (samplePopulation σ₂ (Measure.dirac x)) ≤
      etvDist (samplePopulation σ₁ (Measure.dirac (Function.update id b a)))
        (samplePopulation σ₂ (Measure.dirac (Function.update id b a))) := by
  have hx := measurable_of_countable x
  rw [samplePopulation_dirac_eq_map_update_id σ₁ hxab,
    samplePopulation_dirac_eq_map_update_id σ₂ hxab]
  exact etvDist_map_le _ _ (by fun_prop)

/-- If `x a = x b`, the largest eventwise excess of sampling `x` without replacement over sampling
`x` with replacement is at most that of the one-pair population `Function.update id b a`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id
    [Fintype ι] [Countable κ] [DecidableEq κ] {x : κ → α} {a b : κ} (hxab : x a = x b) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) ≤
      ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
        sampleWithoutReplacement (Measure.dirac (Function.update id b a)) B -
          sampleWithReplacement (Measure.dirac (Function.update id b a)) B := by
  simp only [sampleWithoutReplacement_def, sampleWithReplacement_def]
  exact iSup_samplePopulation_dirac_sub_le_update_id _ _ hxab

/-- When an embedding `ι ↪ κ` exists and `x a = x b`, the largest eventwise excess of sampling `x`
with replacement over sampling `x` without replacement is also at most the without-over-with excess
of the one-pair population `Function.update id b a`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_update_id
    [Fintype ι] [Finite κ] [DecidableEq κ] (e : ι ↪ κ) {x : κ → α} {a b : κ}
    (hxab : x a = x b) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (Measure.dirac x) A -
          sampleWithoutReplacement (Measure.dirac x) A) ≤
      ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
        sampleWithoutReplacement (Measure.dirac (Function.update id b a)) B -
          sampleWithReplacement (Measure.dirac (Function.update id b a)) B := by
  let : Nonempty (ι → κ) := ⟨fun _ => a⟩
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac x) e
  let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
  rw [iSup_measure_sub_comm (by rw [measure_univ, measure_univ])]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id hxab

/-- If `x a = x b`, the extended total variation distance between sampling `x` without and with
replacement is at most that of the one-pair population `Function.update id b a`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_update_id
    [Fintype ι] [Countable κ] [DecidableEq κ] {x : κ → α} {a b : κ} (hxab : x a = x b) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (Function.update id b a)))
        (sampleWithReplacement (ι := ι) (Measure.dirac (Function.update id b a))) := by
  simp only [sampleWithoutReplacement_def, sampleWithReplacement_def]
  exact etvDist_samplePopulation_dirac_le_update_id _ _ hxab

end RepeatedValues

end TauCeti.Probability
