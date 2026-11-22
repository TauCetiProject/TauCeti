/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag
public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.Process.Poisson.Filtered
import TauCeti.MeasureTheory.Measure.IntegerValued.Stieltjes
import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.PointProcess.Poisson.Construction
import TauCeti.Probability.PointProcess.Poisson.Simplicity
import TauCeti.Probability.RandomMeasure.Cumulative

/-!
# Existence of homogeneous Poisson processes

The real cumulative counts `t ↦ ⌊M (0,t]⌋` of a Poisson random measure `M` on the half-line
with intensity `α` times Lebesgue measure form a Poisson process of rate `α` relative to their
own natural filtration (`IsPoissonRandomMeasure.isFilteredPoissonProcess_natural_count`).
Sampling such a random measure with `Measure.poissonLaw` therefore produces a Poisson process
of every rate `α`, including `α = 0`.

The random measure is almost surely locally finite, integer-valued and simple. Changing the
counts to zero on an ambient-measurable null set containing the exceptional realizations
gives a Poisson process for its natural filtration *every* path of which is a counting path:
natural-valued, zero at time zero, nondecreasing and right-continuous, with jumps from the
left of size at most one (`exists_isFilteredPoissonProcess`). Being natural-valued and
nondecreasing, each path has finitely many jumps on every bounded interval.

The filtration-relative Poisson property comes from the independent Poisson increments of the
counts through `isFilteredPoissonProcess_natural_natCast_iff`; path regularity comes from the
deterministic count-path lemmas for locally finite integer-valued measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press, 2018,
  Theorem 3.6 and Chapter 7.
* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℝ≥0} {α : ℝ≥0}

/-- The real cumulative counts of a Poisson random measure on the half-line with intensity
`α` times Lebesgue measure form a Poisson process of rate `α` relative to their natural
filtration. The counts exclude the origin, so they vanish at time zero. -/
theorem IsPoissonRandomMeasure.isFilteredPoissonProcess_natural_count
    (h : IsPoissonRandomMeasure P M ((α : ℝ≥0∞) • nnvolume))
    (hmeas : ∀ t, StronglyMeasurable fun ω => (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ)) :
    IsFilteredPoissonProcess
      (Filtration.natural (fun t ω => (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ)) hmeas) α
      (fun t ω => (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ)) P := by
  have : IsLocallyFiniteMeasure ((α : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  exact (isFilteredPoissonProcess_natural_natCast_iff h.measurable_nat_count).2
    ⟨ae_of_all _ fun _ => by simp, h.hasIndepIncrements_nat_count,
      fun _ _ hst => h.hasLaw_nat_count_sub_smul_nnvolume hst⟩

/-- **Existence of Poisson processes.** For every rate `α`, some probability space carries a
Poisson process of rate `α` relative to its natural filtration whose paths are all counting
paths: natural-valued, zero at time zero, nondecreasing and right-continuous, and at each
positive time some earlier value is at most one below, so every jump has size at most one.

The process is the count process of a Poisson random measure, set to zero on a null event. -/
theorem exists_isFilteredPoissonProcess (α : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (K : ℝ≥0 → Ω → ℕ)
      (hK : ∀ t, StronglyMeasurable fun ω => (K t ω : ℝ)),
      IsFilteredPoissonProcess (Filtration.natural (fun t ω => (K t ω : ℝ)) hK) α
        (fun t ω => (K t ω : ℝ)) P ∧
      ∀ ω, K 0 ω = 0 ∧ Monotone (K · ω) ∧ IsRightContinuous (K · ω) ∧
        ∀ t > 0, ∃ s < t, K t ω ≤ K s ω + 1 := by
  classical
  let Λ : Measure ℝ≥0 := (α : ℝ≥0∞) • nnvolume
  have : IsLocallyFiniteMeasure Λ := nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  let P := Λ.poissonLaw
  have h : IsPoissonRandomMeasure P id Λ := Λ.isPoissonRandomMeasure_poissonLaw
  -- Almost every realization is locally finite, integer-valued and simple.
  let G : Set (Measure ℝ≥0) :=
    {μ | IsLocallyFiniteMeasure μ ∧ μ.IsIntegerValued ∧ ∀ t, μ {t} ≤ 1}
  have hG : ∀ᵐ μ ∂P, μ ∈ G := by
    filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
      h.ae_forall_singleton_le_one_smul_nnvolume] with μ h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
  -- A measurable null event containing every exceptional realization.
  let S := toMeasurable P Gᶜ
  have hS : ∀ᵐ μ ∂P, μ ∉ S := by
    rw [← measure_eq_zero_iff_ae_notMem, measure_toMeasurable]
    exact ae_iff.mp hG
  let C : ℝ≥0 → Measure ℝ≥0 → ℕ := fun t μ => ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  let K : ℝ≥0 → Measure ℝ≥0 → ℕ := fun t μ => if μ ∈ S then 0 else C t μ
  have hCm (t : ℝ≥0) : Measurable (C t) := h.measurable_nat_count t
  have hKm (t : ℝ≥0) : Measurable fun μ => (K t μ : ℝ) :=
    (measurable_of_countable _).comp
      (Measurable.ite (measurableSet_toMeasurable P Gᶜ) measurable_const (hCm t))
  have hCK (t : ℝ≥0) : (fun μ => (C t μ : ℝ)) =ᵐ[P] fun μ => (K t μ : ℝ) := by
    filter_upwards [hS] with μ hμ
    simp [K, hμ]
  have hcount := h.isFilteredPoissonProcess_natural_count
    fun t => ((measurable_of_countable _).comp (hCm t)).stronglyMeasurable
  have hadapted := (hcount.adapted.ambientNullAugmentation_of_ae_eq hKm hCK).stronglyAdapted
  refine ⟨Measure ℝ≥0, inferInstance, P, K, fun t => (hKm t).stronglyMeasurable,
    (hcount.ambientNullAugmentation.congr hadapted hCK).natural _, fun μ => ?_⟩
  by_cases hμS : μ ∈ S
  · have hK (t : ℝ≥0) : K t μ = 0 := by simp [K, hμS]
    refine ⟨hK 0, fun s t _ => (hK s).trans_le (hK t).ge, ?_,
      fun t ht => ⟨0, ht, by simp [hK]⟩⟩
    rw [show (K · μ) = fun _ => 0 from funext hK]
    exact IsRightContinuous.const
  · obtain ⟨hloc, hint, hsimple⟩ : μ ∈ G := by
      by_contra hμG
      exact hμS (subset_toMeasurable P Gᶜ hμG)
    have : IsLocallyFiniteMeasure μ := hloc
    have hK (t : ℝ≥0) : K t μ = C t μ := by simp [K, hμS]
    have hKC : (K · μ) = (C · μ) := funext hK
    refine ⟨by simp [hK, C], hKC ▸ μ.monotone_natFloor_Ioc 0,
      hKC ▸ μ.isRightContinuous_natFloor_Ioc 0, fun t ht => ?_⟩
    obtain ⟨s, hst, hle⟩ := hint.exists_nat_count_le_add_floor ht
    have hfloor : ⌊(μ {t}).toNNReal⌋₊ ≤ 1 :=
      Nat.floor_le_one_of_le_one <| by
        simpa using ENNReal.toNNReal_mono ENNReal.one_ne_top (hsimple t)
    exact ⟨s, hst, by simpa only [hK] using hle.trans (Nat.add_le_add_left hfloor _)⟩

end TauCeti.Probability
