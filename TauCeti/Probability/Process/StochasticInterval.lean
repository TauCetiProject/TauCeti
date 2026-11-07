/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Predictable stochastic intervals

For stopping times `σ` and `τ` on a raw filtration, the stochastic intervals `(σ,τ]`
and `[0,τ]` are predictable. An event known at `σ` can also be imposed on `(σ,τ]`.
Consequently, cutting a predictable integrand off at a stopping time preserves
predictability. No right continuity or completeness of the filtration is needed.

The lower integral of a nonnegative integrand cut off at `τ` is the stopped cumulative
integral. This pathwise identity includes infinite energies and infinite stopping times;
it is used to identify the square energy of stopped stochastic integrands. In particular,
it does not replace an infinite energy by the fallback value of a Bochner integral.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §2 and Chapter 3, §2.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω}
  [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SeparableSpace ι] [DenselyOrdered ι]
  {ℱ : Filtration ι m} {σ τ : Ω → WithTop ι}

/-- The part of the stochastic ray `(σ,∞)` lying over an event known at `σ` is predictable. -/
theorem IsStoppingTime.measurableSet_predictable_lt_inter (hσ : IsStoppingTime ℱ σ)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[ℱ.predictable] {p : ι × Ω | σ p.2 < p.1 ∧ p.2 ∈ A} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  have he : {p : ι × Ω | σ p.2 < p.1 ∧ p.2 ∈ A} =
      ⋃ q ∈ D, Ioi q ×ˢ (A ∩ {ω | σ ω ≤ q}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioi, mem_inter_iff]
    constructor
    · rintro ⟨hp, hA⟩
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hp)
      obtain ⟨q, hqD, hsq, hqt⟩ := hDd.exists_between (WithTop.coe_lt_coe.mp (hs ▸ hp))
      exact ⟨q, hqD, hqt, hA, hs ▸ WithTop.coe_le_coe.mpr hsq.le⟩
    · rintro ⟨q, hqD, hqt, hA, hsq⟩
      exact ⟨hsq.trans_lt (WithTop.coe_lt_coe.mpr hqt), hA⟩
  rw [he]
  exact MeasurableSet.biUnion hDc fun q _ ↦
    measurableSet_predictable_Ioi_prod (((hσ.measurableSet A).mp hA).2 q)

/-- The stochastic ray `(τ,∞)` is predictable, even when `τ` is not a predictable time. -/
theorem IsStoppingTime.measurableSet_predictable_lt (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ι × Ω | τ p.2 < p.1} := by
  simpa using hτ.measurableSet_predictable_lt_inter (A := univ) MeasurableSet.univ

/-- The stochastic interval `[0,τ]` is predictable, including its time-zero section. -/
theorem IsStoppingTime.measurableSet_predictable_le (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ι × Ω | (p.1 : WithTop ι) ≤ τ p.2} := by
  simpa only [compl_ofPred, not_lt] using hτ.measurableSet_predictable_lt.compl

/-- The stochastic interval `(σ,τ]` is predictable. No ordering between the two times
is assumed; the interval is empty on paths where `τ ≤ σ`. -/
theorem IsStoppingTime.measurableSet_predictable_Ioc (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ι × Ω | σ p.2 < p.1 ∧ (p.1 : WithTop ι) ≤ τ p.2} :=
  hσ.measurableSet_predictable_lt.inter hτ.measurableSet_predictable_le

/-- An event known at the left stopping time can be imposed on `(σ,τ]` while retaining
predictable measurability. -/
theorem IsStoppingTime.measurableSet_predictable_Ioc_inter (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[ℱ.predictable]
      {p : ι × Ω | σ p.2 < p.1 ∧ (p.1 : WithTop ι) ≤ τ p.2 ∧ p.2 ∈ A} := by
  convert (hσ.measurableSet_predictable_lt_inter hA).inter
    hτ.measurableSet_predictable_le using 1
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

variable {E : Type*} [TopologicalSpace E] [Zero E] {H : ι → Ω → E}

/-- Killing a predictable integrand after a stopping time preserves predictability.
This is a cutoff, not the process that keeps its value at the stopping time thereafter. -/
theorem IsStronglyPredictable.ite_le (hH : IsStronglyPredictable ℱ H)
    (hτ : IsStoppingTime ℱ τ) :
    IsStronglyPredictable ℱ (fun t ω ↦ if (t : WithTop ι) ≤ τ ω then H t ω else 0) := by
  classical
  exact StronglyMeasurable.ite hτ.measurableSet_predictable_le hH stronglyMeasurable_const

/-- Restricting a predictable integrand to a stochastic interval `(σ,τ]` preserves
predictability. The left endpoint is excluded and the right endpoint is included. -/
theorem IsStronglyPredictable.ite_Ioc (hH : IsStronglyPredictable ℱ H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    IsStronglyPredictable ℱ
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ι) ≤ τ ω then H t ω else 0) := by
  classical
  exact StronglyMeasurable.ite (hσ.measurableSet_predictable_Ioc hτ) hH
    stronglyMeasurable_const

end MeasureTheory

namespace MeasureTheory

variable {Ω ι : Type*} [LinearOrder ι] [OrderBot ι] [MeasurableSpace ι]
  [TopologicalSpace ι] [OrderTopology ι] [OpensMeasurableSpace ι]

/-- Cutting a nonnegative integrand off at a random time stops its cumulative lower
integral. This identity is pathwise, requires no measurability of the random time or
integrand, and remains valid for infinite energies and infinite random times. -/
theorem setLIntegral_ite_le_eq_stoppedProcess (f : ι → Ω → ℝ≥0∞)
    (τ : Ω → WithTop ι) (μ : Measure ι) (t : ι) (ω : Ω) :
    (∫⁻ s in Ioc ⊥ t, if (s : WithTop ι) ≤ τ ω then f s ω else 0 ∂μ) =
      stoppedProcess (fun u ω ↦ ∫⁻ s in Ioc ⊥ u, f s ω ∂μ) τ t ω := by
  classical
  by_cases ht : (t : WithTop ι) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ht]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp [((WithTop.coe_le_coe.mpr hs.2).trans ht)]
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (lt_of_not_ge ht))
    have hut : u ≤ t := WithTop.coe_le_coe.mp (hu ▸ (le_of_not_ge ht))
    rw [stoppedProcess_eq_of_ge (le_of_not_ge ht), ← hu]
    simp only [WithTop.untopD_coe, WithTop.coe_le_coe]
    have he : (fun s ↦ if s ≤ u then f s ω else 0) = (Iic u).indicator (fun s ↦ f s ω) := by
      ext s
      by_cases hs : s ≤ u <;> simp [hs]
    rw [he, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_of_le hut]

end MeasureTheory
