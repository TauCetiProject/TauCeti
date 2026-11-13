/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Filtered
public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.MeasureTheory.Measure.IntegerValued.CountPath
import TauCeti.Probability.PointProcess.Poisson.Construction
import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Simplicity

/-!
# Existence of homogeneous Poisson processes

The cumulative counts `t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊` of a Poisson random measure `M` on the
half-line with homogeneous intensity `α • nnvolume` form a rate-`α` Poisson process relative to
their natural filtration (`IsPoissonRandomMeasure.isFilteredPoissonProcess_natural`). The rate may
be zero.

Applying this to the sampling law `Measure.poissonLaw`, after replacing by the zero measure the
null set of realizations that are not locally finite, integer-valued and simple, gives a
probability space carrying a rate-`α` Poisson process for its natural filtration
(`exists_isFilteredPoissonProcess`). Every path of this process, not merely almost every path,
is natural-valued, nondecreasing and right-continuous, starts at zero and jumps by at most one.
An arbitrary version of a Poisson process need not have these path properties; they are a feature
of this construction.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press, 2018,
  Chapters 3 and 7.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

namespace IsPoissonRandomMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℝ≥0}
  {Λ : Measure ℝ≥0} {α : ℝ≥0}

/-- The real-valued cumulative counts of a Poisson random measure on the half-line are
measurable. -/
theorem stronglyMeasurable_count (h : IsPoissonRandomMeasure P M Λ) (t : ℝ≥0) :
    StronglyMeasurable fun ω ↦ (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ) :=
  (Measurable.of_discrete.comp (h.measurable_nat_count t)).stronglyMeasurable

/-- The cumulative counts of a homogeneous temporal Poisson random measure of rate `α` form a
Poisson process of rate `α` relative to their natural filtration. The rate may be zero, and no
path regularity of the realizations is assumed. -/
theorem isFilteredPoissonProcess_natural
    (h : IsPoissonRandomMeasure P M ((α : ℝ≥0∞) • nnvolume)) :
    IsFilteredPoissonProcess (Filtration.natural _ h.stronglyMeasurable_count) α
      (fun t ω ↦ (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ)) P := by
  have : IsLocallyFiniteMeasure ((α : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have hmono := h.ae_monotone_nat_count
  refine HasIndepIncrements.isFilteredPoissonProcess_natural ?_ _ ?_ fun s t hst ↦ ?_
  · -- Monotone paths make truncated natural subtraction agree with real subtraction.
    intro n t ht
    refine ((h.hasIndepIncrements_nat_count n t ht).comp (fun _ (x : ℕ) ↦ (x : ℝ))
      fun _ ↦ Measurable.of_discrete).congr fun i ↦ ?_
    filter_upwards [hmono] with ω hω
    exact Nat.cast_sub (hω (ht i.castSucc_le_succ))
  · exact Eventually.of_forall fun _ ↦ by simp
  · refine ((hasLaw_map (X := (Nat.cast : ℕ → ℝ)) Measurable.of_discrete.aemeasurable).comp
      (h.hasLaw_nat_count_sub_smul_nnvolume hst)).congr ?_
    filter_upwards [hmono] with ω hω
    exact (Nat.cast_sub (hω hst)).symm

end IsPoissonRandomMeasure

/-- **Existence of homogeneous Poisson processes.** For every rate `α`, some probability space
carries a Poisson process of rate `α` relative to its natural filtration, every path of which
starts at zero, is natural-valued, nondecreasing and right-continuous, and jumps by at most one.
The rate may be zero. -/
theorem exists_isFilteredPoissonProcess (α : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : ℝ≥0 → Ω → ℝ)
      (hN : ∀ t, StronglyMeasurable (N t)),
      IsFilteredPoissonProcess (Filtration.natural N hN) α N P ∧
      ∀ ω, N 0 ω = 0 ∧ (∀ t, ∃ n : ℕ, N t ω = n) ∧ Monotone (fun t ↦ N t ω) ∧
        (∀ t, ContinuousWithinAt (fun t ↦ N t ω) (Ici t) t) ∧
        ∀ t, ∀ᶠ s in 𝓝[<] t, N t ω ≤ N s ω + 1 := by
  classical
  set Λ : Measure ℝ≥0 := (α : ℝ≥0∞) • nnvolume
  have : IsLocallyFiniteMeasure Λ := nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have hP := Measure.isPoissonRandomMeasure_poissonLaw Λ
  -- Discard a measurable null set containing every irregular realization.
  have hgood : ∀ᵐ μ ∂Λ.poissonLaw,
      IsLocallyFiniteMeasure μ ∧ μ.IsIntegerValued ∧ ∀ t, μ {t} ≤ 1 := by
    filter_upwards [hP.ae_isLocallyFiniteMeasure, hP.ae_isIntegerValued,
      hP.ae_forall_singleton_le_one_smul_nnvolume] with μ h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨S, hbad, hS, hS0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  let M : Measure ℝ≥0 → Measure ℝ≥0 := S.piecewise 0 id
  have hM : Measurable M := Measurable.piecewise hS measurable_const measurable_id
  have hPM : IsPoissonRandomMeasure Λ.poissonLaw M Λ := hP.congr hM <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with μ hμ
    simp [M, hμ]
  have hreg (μ : Measure ℝ≥0) :
      IsLocallyFiniteMeasure (M μ) ∧ (M μ).IsIntegerValued ∧ ∀ t, M μ {t} ≤ 1 := by
    by_cases hμ : μ ∈ S
    · simp only [M, piecewise_eq_of_mem _ _ _ hμ, Pi.zero_apply]
      exact ⟨inferInstance, Measure.isIntegerValued_zero, fun _ ↦ by simp⟩
    · simp only [M, piecewise_eq_of_notMem _ _ _ hμ, id_eq]
      by_contra hbad'
      exact hμ (hbad hbad')
  refine ⟨Measure ℝ≥0, inferInstance, Λ.poissonLaw, _, hPM.stronglyMeasurable_count,
    hPM.isFilteredPoissonProcess_natural, fun μ ↦ ?_⟩
  obtain ⟨hloc, hint, hsimple⟩ := hreg μ
  refine ⟨by simp, fun t ↦ ⟨_, rfl⟩, fun s t hst ↦ ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · exact Nat.cast_le.2 (Measure.monotone_natFloor_Ioc hst)
  · exact (continuous_of_discreteTopology (f := fun n : ℕ ↦ (n : ℝ))).continuousAt
      |>.comp_continuousWithinAt (hint.continuousWithinAt_natFloor_Ioc t)
  · filter_upwards [hint.eventually_natFloor_Ioc_le_add_one (hsimple t)] with s hs
    exact_mod_cast hs

end TauCeti.Probability
