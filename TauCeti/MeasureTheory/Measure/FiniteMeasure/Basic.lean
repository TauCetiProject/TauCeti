/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Module.Ball.Retraction

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
* `MeasureTheory.Measure.measureReal_finset_eq_zero`
* `MeasureTheory.FiniteMeasure.tendsto_integral_of_tendstoUniformly`: narrow convergence against
  uniformly convergent `RCLike`-valued integrands.
* `MeasureTheory.FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall`: the same for
  measures carried by a closed ball of a proper normed space, against `RCLike`-valued integrands
  that are only continuous, and converge uniformly, on the ball.

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

/-- A finite measure vanishes on a finite set if it vanishes on every point of that set. -/
theorem Measure.measureReal_finset_eq_zero (μ : Measure α) [IsFiniteMeasure μ]
    [MeasurableSingletonClass α] (s : Finset α) (hzero : ∀ i ∈ s, μ.real {i} = 0) :
    μ.real s = 0 := by
  rw [← sum_measureReal_singleton]
  exact Finset.sum_eq_zero hzero

section NarrowConvergence

open Filter Topology
open scoped BoundedContinuousFunction

/-- **Narrow convergence against uniformly convergent integrands.** If the finite measures `μs i`
converge narrowly to `μ` and the `RCLike`-valued functions `fs i`, eventually almost everywhere
strongly measurable, converge uniformly to a bounded continuous function `f`, then
`∫ fs i dμs i` converges to `∫ f dμ`. -/
theorem FiniteMeasure.tendsto_integral_of_tendstoUniformly [TopologicalSpace α]
    [OpensMeasurableSpace α] {ι 𝕜 : Type*} [RCLike 𝕜] {l : Filter ι} {μs : ι → FiniteMeasure α}
    {μ : FiniteMeasure α} (hμ : Tendsto μs l (𝓝 μ)) {fs : ι → α → 𝕜} {f : α →ᵇ 𝕜}
    (hf : TendstoUniformly fs f l) (hfs : ∀ᶠ i in l, AEStronglyMeasurable (fs i) (μs i)) :
    Tendsto (fun i ↦ ∫ x, fs i x ∂(μs i : Measure α)) l (𝓝 (∫ x, f x ∂(μ : Measure α))) := by
  -- It suffices that `∫ (fs i - f) dμs i → 0`, which is bounded by `sup ‖fs i - f‖ * mass`.
  suffices h : Tendsto (fun i ↦ ∫ x, fs i x ∂(μs i : Measure α) - ∫ x, f x ∂(μs i : Measure α))
      l (𝓝 0) by
    simpa using h.add ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 hμ f)
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

/-- **Narrow convergence of measures carried by a closed ball.** Let finite measures `μs i` on a
proper real normed space converge narrowly to `μ`, all carried by the closed ball `closedBall 0 r`
(then `μ` is carried by it too).
If functions `fs i`, continuous on that ball, converge uniformly on it to a function `f` continuous
on it, then `∫ fs i dμs i` converges to `∫ f dμ`. Nothing is assumed off the ball: there `fs i`
and `f` may be unbounded or discontinuous. -/
theorem FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall {E 𝕜 ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    [RCLike 𝕜] {l : Filter ι} {μs : ι → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμ : Tendsto μs l (𝓝 μ)) {r : ℝ}
    (hμsr : ∀ᶠ i in l, (μs i : Measure E) (Metric.closedBall 0 r)ᶜ = 0)
    {fs : ι → E → 𝕜} {f : E → 𝕜}
    (hfs : ∀ i, ContinuousOn (fs i) (Metric.closedBall 0 r))
    (hf : ContinuousOn f (Metric.closedBall 0 r))
    (hfsf : TendstoUniformlyOn fs f l (Metric.closedBall 0 r)) :
    Tendsto (fun i ↦ ∫ x, fs i x ∂(μs i : Measure E)) l (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  rcases l.eq_or_neBot with rfl | hne
  · exact tendsto_bot
  -- The limit is carried by the ball too: its mass is the limit of the masses of the `μs i`, which
  -- equal their masses on the closed ball, and the limsup of those is at most `μ (closedBall 0 r)`.
  have hμr : (μ : Measure E) (Metric.closedBall 0 r)ᶜ = 0 := by
    have hmass : Tendsto (fun i ↦ (μs i : Measure E) univ) l (𝓝 ((μ : Measure E) univ)) := by
      simp only [← FiniteMeasure.ennreal_mass]
      exact ENNReal.tendsto_coe.2 ((FiniteMeasure.continuous_mass.tendsto μ).comp hμ)
    have heq : (fun i ↦ (μs i : Measure E) (Metric.closedBall 0 r)) =ᶠ[l]
        fun i ↦ (μs i : Measure E) univ := hμsr.mono fun i hi ↦ by
      simp only
      rw [← measure_add_measure_compl Metric.isClosed_closedBall.measurableSet, hi, add_zero]
    have hle := FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ
      (Metric.isClosed_closedBall (x := (0 : E)) (ε := r))
    rw [limsup_congr heq, hmass.limsup_eq] at hle
    rw [measure_compl Metric.isClosed_closedBall.measurableSet (measure_ne_top _ _)]
    exact tsub_eq_zero_of_le hle
  have hae {ν : Measure E} (hν : ν (Metric.closedBall 0 r)ᶜ = 0) :
      ∀ᵐ x ∂ν, x ∈ Metric.closedBall 0 r :=
    mem_ae_iff.2 hν
  rcases lt_or_ge r 0 with hr | hr
  · have h0 {ν : Measure E} (hν : ν (Metric.closedBall 0 r)ᶜ = 0) : ν = 0 := by
      rwa [Metric.closedBall_eq_empty.2 hr, compl_empty, Measure.measure_univ_eq_zero] at hν
    rw [h0 hμr, integral_zero_measure]
    exact tendsto_const_nhds.congr' (hμsr.mono fun i hi ↦ by simp [h0 hi])
  -- On measures carried by the ball, `fs i` and `f` may be replaced by their compositions with the
  -- radial retraction `ρ` onto the ball. These converge uniformly on all of `E`, to the bounded
  -- continuous function `f ∘ ρ`, so `FiniteMeasure.tendsto_integral_of_tendstoUniformly` applies.
  have hmem := TauCeti.radialRetraction_mem_closedBall (E := E) hr
  have hρ : Continuous (TauCeti.radialRetraction r : E → E) :=
    (TauCeti.lipschitzWith_radialRetraction hr).continuous
  have hρeq {ν : Measure E} (hν : ν (Metric.closedBall 0 r)ᶜ = 0) (g : E → 𝕜) :
      ∫ x, g (TauCeti.radialRetraction r x) ∂ν = ∫ x, g x ∂ν :=
    integral_congr_ae ((hae hν).mono fun x hx ↦ by
      simp [TauCeti.radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 hx)])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn hf
  let G : E →ᵇ 𝕜 := BoundedContinuousFunction.mkOfBound
    ⟨f ∘ TauCeti.radialRetraction r, hf.comp_continuous hρ hmem⟩ (2 * C) fun x y ↦ by
      have hx := hC _ (hmem x)
      have hy := hC _ (hmem y)
      calc dist (f (TauCeti.radialRetraction r x)) (f (TauCeti.radialRetraction r y))
          ≤ ‖f (TauCeti.radialRetraction r x)‖ + ‖f (TauCeti.radialRetraction r y)‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ 2 * C := by linarith
  have hlim := FiniteMeasure.tendsto_integral_of_tendstoUniformly hμ (f := G)
    (fs := fun i ↦ fs i ∘ TauCeti.radialRetraction r)
    (fun u hu ↦ (hfsf u hu).mono fun i hi x ↦ hi _ (hmem x))
    (Eventually.of_forall fun i ↦ ((hfs i).comp_continuous hρ hmem).aestronglyMeasurable)
  rw [← hρeq hμr f]
  exact (tendsto_congr' (hμsr.mono fun i hi ↦ hρeq hi (fs i))).1 hlim

end NarrowConvergence

end MeasureTheory
