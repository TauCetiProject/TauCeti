/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Basic tightness criteria for measures

Mathlib's `MeasureTheory.isTightMeasureSet_singleton` says that a single finite measure on a
complete second-countable pseudo-metrizable space is tight, and `IsTightMeasureSet.union` says
that tightness survives a binary union. Together they give tightness of any *finite* set of
finite measures, which is the form the Prokhorov extraction arguments need in order to discard
the finitely many exceptional members of a family for which a uniform tail bound is unavailable.
For finite measures on the real line, uniformly bounded second moments also imply tightness.

## Main declarations

* `TauCeti.isTightMeasureSet_of_finite`: a finite set of finite measures is tight.
* `TauCeti.isTightMeasureSet_range_of_finite`: a family of finite measures indexed by a finite type
  has tight range.
* `TauCeti.isTightMeasureSet_range_of_eventually_eq`: a family of finite measures that is equal to
  a fixed measure off finitely many indices has tight range.
* `TauCeti.isTightMeasureSet_of_integral_sq_le`: finite real measures with uniformly bounded
  second moments form a tight set.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone), "measure extraction via Prokhorov tightness".
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
  [BorelSpace α]

/-- **A finite set of finite measures is tight.** Singletons are tight and tightness is closed
under unions; the empty case routes through an arbitrary singleton, as Mathlib has no dedicated
empty-set tightness lemma. -/
theorem isTightMeasureSet_of_finite {S : Set (Measure α)} (hS : S.Finite)
    (hfin : ∀ ν ∈ S, IsFiniteMeasure ν) : IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact (isTightMeasureSet_singleton (μ := (0 : Measure α))).subset (empty_subset _)
  | @insert ν S _ _ ih =>
      have := hfin ν (mem_insert _ _)
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ ↦ hfin ρ (mem_insert_of_mem _ hρ))

/-- **A family of finite measures indexed by a finite type has tight range.** -/
theorem isTightMeasureSet_range_of_finite {ι : Type*} [Finite ι] (μ : ι → Measure α)
    [∀ i, IsFiniteMeasure (μ i)] : IsTightMeasureSet (range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro _ ⟨i, rfl⟩; infer_instance)

/-- **Eventually constant families of finite measures are tight.** A family of finite measures
that equals a fixed measure `ν` off finitely many indices has finite range, so it is tight. No
finiteness assumption on `ν` is needed: `ν` lies in the range only if it is one of the `μ i`. -/
theorem isTightMeasureSet_range_of_eventually_eq {ι : Type*} {μ : ι → Measure α}
    [∀ i, IsFiniteMeasure (μ i)] {ν : Measure α} (h : ∀ᶠ i in cofinite, μ i = ν) :
    IsTightMeasureSet (range μ) := by
  refine isTightMeasureSet_of_finite (((eventually_cofinite.1 h).image μ).insert ν |>.subset ?_)
    (by rintro _ ⟨i, rfl⟩; infer_instance)
  rintro _ ⟨i, rfl⟩
  exact (em (μ i = ν)).imp id fun hi ↦ ⟨i, hi, rfl⟩

/-- A set of finite measures on `ℝ` with uniformly bounded second moment is tight. -/
theorem isTightMeasureSet_of_integral_sq_le {S : Set (Measure ℝ)} {B : ℝ}
    (hS : ∀ ρ ∈ S, IsFiniteMeasure ρ ∧ Integrable (fun x : ℝ => x ^ 2) ρ ∧
      ∫ x, x ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hlim : Tendsto (fun R : ℝ => B / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  obtain ⟨R, hR1, hR0⟩ := ((hlim.eventually (gt_mem_nhds hε')).and (eventually_gt_atTop 0)).exists
  refine ⟨Icc (-R) R, isCompact_Icc, fun ρ hρ => ?_⟩
  obtain ⟨hfin, hint, hB⟩ := hS ρ hρ
  have : IsFiniteMeasure ρ := hfin
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (f := fun x : ℝ => x ^ 2)
    (ae_of_all _ fun x => sq_nonneg x) hint (R ^ 2)
  have hsub : (Icc (-R) R)ᶜ ⊆ {x : ℝ | R ^ 2 ≤ x ^ 2} := fun x hx => by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    simp only [mem_ofPred_eq]
    rcases hx with hx | hx <;> nlinarith
  have hreal : ρ.real (Icc (-R) R)ᶜ ≤ B / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [measureReal_mono (μ := ρ) hsub,
      measureReal_nonneg (μ := ρ) (s := (Icc (-R) R)ᶜ), sq_nonneg R]
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε'.le).2 ?_ |>.trans_eq
    (ENNReal.ofReal_toReal hεtop)
  exact hreal.trans hR1.le

end TauCeti

end
