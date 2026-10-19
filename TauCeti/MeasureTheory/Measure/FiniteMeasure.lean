/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Finite measures

When the underlying σ-algebra is countably generated, singletons are measurable in
`FiniteMeasure α` and in `ProbabilityMeasure α`.

On a finite measurable space, a probability measure is the sum of its singleton masses.

Narrow convergence of finite measures `μs i → μ` tests against a fixed bounded continuous function.
It also passes to integrands `fs i` converging uniformly to a bounded continuous `f`:
`∫ fs i dμs i → ∫ f dμ`. This is what makes `t ↦ ∫ u (t, x) dμₜ(x)` continuous along a narrowly
continuous curve of finite measures when `u` is bounded continuous and uniformly continuous in time.

## Main results

* `MeasureTheory.FiniteMeasure.instMeasurableSingletonClass`
* `MeasureTheory.ProbabilityMeasure.instMeasurableSingletonClass`
* `MeasureTheory.Measure.sum_singleton_eq_one`
* `MeasureTheory.FiniteMeasure.tendsto_integral_of_tendstoUniformly`: narrow convergence against
  uniformly convergent integrands.

## Implementation

The statement is really about *finite* measures; the probability-measure form is the subtype
corollary. Countable generation is exactly what the proof consumes — `StandardBorelSpace α` implies
it, but is stronger than needed.

A countable generating family need not be closed under intersection, so it is replaced by the set
algebra it generates (`MeasureTheory.generateSetAlgebra`), which is still countable, is a π-system,
and generates the same σ-algebra. A finite measure is then pinned down by its values there
(`ext_of_generate_finite`, with `Set.univ` supplied by the algebra), so `{μ}` is the countable
intersection of the equalizers `{ν | ν s = μ s}`. Each equalizer is measurable because evaluation at
a fixed measurable set is.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Evaluation at a fixed measurable set is measurable on `FiniteMeasure α`. Private: it exists
only to prove the instance below. -/
private theorem FiniteMeasure.measurable_coe_toMeasure {s : Set α} (hs : MeasurableSet s) :
    Measurable fun ν : FiniteMeasure α => (ν : Measure α) s :=
  (Measure.measurable_coe hs).comp measurable_subtype_coe

/-- **Singletons are measurable in the space of finite measures**, when the σ-algebra on `α` is
countably generated. -/
instance FiniteMeasure.instMeasurableSingletonClass [CountablyGenerated α] :
    MeasurableSingletonClass (FiniteMeasure α) where
  measurableSet_singleton μ := by
    classical
    set 𝒜 := generateSetAlgebra (countableGeneratingSet α) with h𝒜
    have hcount : 𝒜.Countable :=
      countable_generateSetAlgebra countable_countableGeneratingSet
    have halg : IsSetAlgebra 𝒜 := isSetAlgebra_generateSetAlgebra
    have hgen : ‹MeasurableSpace α› = generateFrom 𝒜 := by
      rw [h𝒜, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]
    have hmeas : ∀ s ∈ 𝒜, MeasurableSet s := fun s hs => hgen ▸ measurableSet_generateFrom hs
    have hset : ({μ} : Set (FiniteMeasure α))
        = ⋂ s ∈ 𝒜, {ν : FiniteMeasure α | (ν : Measure α) s = (μ : Measure α) s} := by
      ext ν
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      refine ⟨fun h s _ => by rw [h], fun h => ?_⟩
      have := ν.2
      refine Subtype.ext ?_
      exact ext_of_generate_finite 𝒜 hgen
        (fun s hs t ht _ => halg.inter_mem hs ht) (fun s hs => h s hs) (h _ halg.univ_mem)
    rw [hset]
    exact MeasurableSet.biInter hcount fun s hs =>
      (FiniteMeasure.measurable_coe_toMeasure (hmeas s hs)) (measurableSet_singleton _)

/-- **Singletons are measurable in the space of probability measures** whenever they are measurable
in the space of finite measures, as they are when the σ-algebra on `α` is countably generated
(`FiniteMeasure.instMeasurableSingletonClass`). -/
instance ProbabilityMeasure.instMeasurableSingletonClass
    [MeasurableSingletonClass (FiniteMeasure α)] :
    MeasurableSingletonClass (ProbabilityMeasure α) where
  measurableSet_singleton μ := by
    have hmap : Measurable (ProbabilityMeasure.toFiniteMeasure (Ω := α)) :=
      measurable_subtype_coe.subtype_mk
    have hpre : ({μ} : Set (ProbabilityMeasure α))
        = ProbabilityMeasure.toFiniteMeasure ⁻¹' {μ.toFiniteMeasure} := by
      ext ν
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h], fun h =>
        Subtype.ext (congrArg (fun x : FiniteMeasure α => (x : Measure α)) h)⟩
    rw [hpre]
    exact hmap (measurableSet_singleton _)

/-- The singleton masses of a probability measure on a finite measurable space sum to one. -/
theorem Measure.sum_singleton_eq_one {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ν : Measure κ) [IsProbabilityMeasure ν] :
    ∑ k, ν {k} = 1 := by
  rw [sum_measure_singleton, Finset.coe_univ, measure_univ]

section NarrowConvergence

open Filter Topology
open scoped BoundedContinuousFunction

/-- **Narrow convergence against uniformly convergent integrands.** If the finite measures `μs i`
converge narrowly to `μ` and the functions `fs i`, eventually almost everywhere strongly
measurable, converge uniformly to a bounded continuous function `f`, then
`∫ fs i dμs i` converges to `∫ f dμ`. -/
theorem FiniteMeasure.tendsto_integral_of_tendstoUniformly [TopologicalSpace α]
    [OpensMeasurableSpace α] {ι : Type*} {l : Filter ι} {μs : ι → FiniteMeasure α}
    {μ : FiniteMeasure α} (hμ : Tendsto μs l (𝓝 μ)) {fs : ι → α → ℝ} {f : α →ᵇ ℝ}
    (hf : TendstoUniformly fs f l) (hfs : ∀ᶠ i in l, AEStronglyMeasurable (fs i) (μs i)) :
    Tendsto (fun i ↦ ∫ x, fs i x ∂(μs i : Measure α)) l (𝓝 (∫ x, f x ∂(μ : Measure α))) := by
  -- It suffices that `∫ (fs i - f) dμs i → 0`, which is bounded by `sup ‖fs i - f‖ * mass`.
  suffices h : Tendsto (fun i ↦ ∫ x, fs i x ∂(μs i : Measure α) - ∫ x, f x ∂(μs i : Measure α))
      l (𝓝 0) by
    simpa using h.add (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hμ f)
  have hmass : Tendsto (fun i ↦ ((μs i).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp ((FiniteMeasure.continuous_mass.tendsto μ).comp hμ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : 0 < (μ.mass : ℝ) + 1 := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hf (ε / ((μ.mass : ℝ) + 1)) (by positivity),
    hmass.eventually (eventually_lt_nhds (lt_add_one (μ.mass : ℝ))), hfs] with i hi hmi hfi
  have hbound : ∀ x, ‖fs i x - f x‖ ≤ ε / ((μ.mass : ℝ) + 1) := fun x ↦ by
    rw [← dist_eq_norm, dist_comm]
    exact (hi x).le
  have hint : Integrable (fs i) (μs i : Measure α) :=
    ((integrable_const (‖f‖ + ε / ((μ.mass : ℝ) + 1))).mono' hfi (ae_of_all _ fun x ↦
      (norm_le_norm_add_norm_sub' (fs i x) (f x)).trans
        (add_le_add (f.norm_coe_le_norm x) (hbound x))))
  rw [dist_zero_right, ← integral_sub hint (f.integrable _)]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hbound)).trans_lt ?_
  rw [measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal, div_mul_eq_mul_div,
    div_lt_iff₀ hK]
  exact mul_lt_mul_of_pos_left hmi hε

end NarrowConvergence

end MeasureTheory
