/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.Cadlag
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Progressive measurability of deterministic, indicator, and right-continuous processes

A strongly adapted process in nonnegative real time with everywhere right-continuous paths is
strongly progressive, on its original filtration. No completeness or right continuity of the
filtration is required. In particular, the result applies to adapted càdlàg processes and permits
use of the progressive stopped-evaluation API.

We also record general structural facts on arbitrary preordered measurable time indices:
deterministic strongly measurable functions of time are strongly progressive for every filtration
(`MeasureTheory.StronglyMeasurable.isStronglyProgressive`), `ℱ ⊥`-strongly measurable random
variables viewed as time-independent processes are strongly progressive
(`MeasureTheory.StronglyMeasurable.isStronglyProgressive_const`), centering a strongly progressive
process at `⊥` preserves strong progressivity
(`MeasureTheory.IsStronglyProgressive.sub_initialValue`), natural powers preserve strong
progressivity (`MeasureTheory.IsStronglyProgressive.pow`), and restricting a strongly progressive
process to an event measurable at every time preserves strong progressivity
(`MeasureTheory.IsStronglyProgressive.indicator`).

On each fixed horizon, right-endpoint samples are capped at that horizon. These approximations
are measurable for the horizon's product sigma algebra; they need not be adapted at earlier
times. Almost-sure path regularity alone does not give the literal conclusion for a raw version.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §1.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

/-- A deterministic strongly measurable path, viewed as a process independent of the sample
variable, is strongly progressive for every filtration. -/
theorem MeasureTheory.StronglyMeasurable.isStronglyProgressive
    {ι Ω β : Type*} [Preorder ι] [MeasurableSpace ι] {m : MeasurableSpace Ω}
    [TopologicalSpace β] {f : ι → β} (hf : StronglyMeasurable f) (ℱ : Filtration ι m) :
    IsStronglyProgressive ℱ (fun t _ ↦ f t) := fun _ ↦
  hf.comp_measurable (measurable_subtype_coe.comp measurable_fst)

/-- An `ℱ ⊥`-strongly measurable random variable, viewed as a time-independent process, is
strongly progressive for `ℱ`. -/
theorem MeasureTheory.StronglyMeasurable.isStronglyProgressive_const
    {ι Ω β : Type*} [Preorder ι] [OrderBot ι] [MeasurableSpace ι] {m : MeasurableSpace Ω}
    [TopologicalSpace β] {ℱ : Filtration ι m} {ξ : Ω → β}
    (hξ : StronglyMeasurable[ℱ ⊥] ξ) :
    IsStronglyProgressive ℱ (fun _ ↦ ξ) := fun _ ↦
  (hξ.mono (ℱ.mono bot_le)).comp_measurable measurable_snd

/-- Centering a strongly progressive process at its initial value `⊥` preserves strong
progressivity. -/
theorem MeasureTheory.IsStronglyProgressive.sub_initialValue
    {ι Ω β : Type*} [Preorder ι] [OrderBot ι] [MeasurableSpace ι] {m : MeasurableSpace Ω}
    [TopologicalSpace β] [Sub β] [ContinuousSub β] {ℱ : Filtration ι m}
    {u : ι → Ω → β} (hu : IsStronglyProgressive ℱ u) :
    IsStronglyProgressive ℱ (fun t ω ↦ u t ω - u ⊥ ω) := fun t ↦
  (hu t).sub ((hu.stronglyAdapted ⊥).isStronglyProgressive_const t)

/-- Raising a strongly progressive process to a natural power preserves strong progressivity. -/
@[to_additive const_nsmul
/-- Taking a natural scalar multiple of a strongly progressive process preserves strong
progressivity. -/]
theorem MeasureTheory.IsStronglyProgressive.pow
    {ι Ω β : Type*} [Preorder ι] [MeasurableSpace ι] {m : MeasurableSpace Ω}
    [TopologicalSpace β] [Monoid β] [ContinuousMul β] {ℱ : Filtration ι m}
    {u : ι → Ω → β} (hu : IsStronglyProgressive ℱ u) (n : ℕ) :
    IsStronglyProgressive ℱ (fun t ω ↦ u t ω ^ n) := fun t ↦ (hu t).pow n

/-- Restricting a strongly progressive process to an event measurable at every time preserves
strong progressivity. -/
theorem MeasureTheory.IsStronglyProgressive.indicator
    {ι Ω E : Type*} [Preorder ι] [MeasurableSpace ι] {m : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] {ℱ : Filtration ι m} {u : ι → Ω → E}
    (hu : IsStronglyProgressive ℱ u) {s : Set Ω} (hs : ∀ t, MeasurableSet[ℱ t] s) :
    IsStronglyProgressive ℱ (fun t ↦ s.indicator (u t)) := fun t ↦ by
  convert (hu t).indicator ((MeasurableSet.univ : MeasurableSet (univ : Set (Iic t))).prod (hs t))
    using 1
  ext ⟨_, ω⟩
  by_cases hω : ω ∈ s <;> simp [hω]

private noncomputable def rightSample (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈(t : ℝ) * (n + 1)⌉₊ : ℝ≥0) / (n + 1)

private lemma le_rightSample (n : ℕ) (t : ℝ≥0) : t ≤ rightSample n t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).mpr
  exact_mod_cast Nat.le_ceil ((t : ℝ) * (n + 1))

private lemma tendsto_rightSample (t : ℝ≥0) :
    Tendsto (fun n => rightSample n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def, rightSample, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one,
    Nat.cast_add, Nat.cast_one] using
    (tendsto_nat_ceil_mul_div_atTop t.coe_nonneg).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- A strongly adapted process with everywhere right-continuous paths is strongly progressive
on its original filtration. The state space need not be separable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous
    {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsStronglyProgressive ℱ u := by
  intro T
  let : MeasurableSpace Ω := ℱ T
  have hm (n : ℕ) : StronglyMeasurable
      (fun p : Iic T × Ω => u (min (rightSample n p.1) T) p.2) := by
    have hs : StronglyMeasurable (Function.uncurry
        (fun k : ℕ => u (min ((k : ℝ≥0) / (n + 1)) T))) :=
      stronglyMeasurable_uncurry_of_countable fun k => (hu _).mono (ℱ.mono (min_le_right _ _))
    have hmap : Measurable (fun p : Iic T × Ω =>
        (⌈((p.1 : ℝ≥0) : ℝ) * (n + 1)⌉₊, p.2)) :=
      ((NNReal.continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)).mul_const
          (n + 1 : ℝ)).nat_ceil.prodMk measurable_snd
    simpa only [Function.uncurry_def, Function.comp_def, rightSample] using
      hs.comp_measurable hmap
  apply stronglyMeasurable_of_tendsto atTop hm
  apply tendsto_pi_nhds.mpr
  intro p
  apply (continuousWithinAt_Ioi_iff_Ici.mp (hc p.2 p.1)).tendsto.comp
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => ?_⟩
  · have h := (tendsto_rightSample p.1).min (tendsto_const_nhds (x := T))
    rw [min_eq_left (α := ℝ≥0) p.1.property] at h
    exact h
  · exact le_min (le_rightSample n p.1) p.1.property

/-- An adapted process with everywhere right-continuous paths in a second-countable
pseudometrizable Borel state space is progressive, without usual-filtration assumptions. -/
theorem MeasureTheory.Adapted.isProgressive_of_isRightContinuous
    {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : Adapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsProgressive ℱ u :=
  ((stronglyAdapted_iff_adapted.mpr hu).isStronglyProgressive_of_isRightContinuous hc).isProgressive
