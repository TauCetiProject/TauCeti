/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Basic tightness criteria for measures

Mathlib's `MeasureTheory.isTightMeasureSet_singleton` says that a single finite measure on a
complete second-countable pseudo-metrizable space is tight, and `IsTightMeasureSet.union` says
that tightness survives a binary union. Together they give tightness of any *finite* set of
finite measures, which is the form the Prokhorov extraction arguments need in order to discard
the finitely many exceptional members of a family for which a uniform tail bound is unavailable.
For real probability measures, a uniform bound on the second moment also gives tightness by
Markov's inequality.

## Main declarations

* `TauCeti.isTightMeasureSet_of_finite`: a finite set of finite measures is tight.
* `TauCeti.isTightMeasureSet_range_of_finite`: a family of finite measures indexed by a finite type
  has tight range.
* `TauCeti.isTightProbabilityMeasureSet_of_integral_sq_le`: a set of real probability measures
  with uniformly bounded second moments is tight.
* `TauCeti.isTightMeasureSet_image_map_of_eventually_eq`: images under a map of finite measures that
  are eventually equal to a fixed finite measure form a tight family.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone), "measure extraction via Prokhorov tightness".
-/

public section

open MeasureTheory Set Filter
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
      have : IsFiniteMeasure ν := hfin ν (mem_insert _ _)
      rw [insert_eq]
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ => hfin ρ (mem_insert_of_mem _ hρ))

/-- **A family of finite measures indexed by a finite type has tight range.** -/
theorem isTightMeasureSet_range_of_finite {ι : Type*} [Finite ι] (μ : ι → Measure α)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) : IsTightMeasureSet (range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro ν ⟨i, rfl⟩; exact hfin i)

/-- A set of probability measures on `ℝ` with uniformly bounded second moment is tight. -/
theorem isTightProbabilityMeasureSet_of_integral_sq_le
    {S : Set (ProbabilityMeasure ℝ)} {B : ℝ}
    (hS : ∀ ρ ∈ S, Integrable (fun x : ℝ => x ^ 2) (ρ : Measure ℝ) ∧
      ∫ x, x ^ 2 ∂(ρ : Measure ℝ) ≤ B) :
    IsTightMeasureSet ((fun ρ : ProbabilityMeasure ℝ => (ρ : Measure ℝ)) '' S) := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hlim : Tendsto (fun R : ℝ => B / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  obtain ⟨R, hR1, hR0⟩ := ((hlim.eventually (gt_mem_nhds hε')).and (eventually_gt_atTop 0)).exists
  refine ⟨Icc (-R) R, isCompact_Icc, fun ρ hρ => ?_⟩
  obtain ⟨ρ, hρ, rfl⟩ := hρ
  obtain ⟨hint, hB⟩ := hS ρ hρ
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (f := fun x : ℝ => x ^ 2)
    (ae_of_all _ fun x => sq_nonneg x) hint (R ^ 2)
  have hsub : (Icc (-R) R)ᶜ ⊆ {x : ℝ | R ^ 2 ≤ x ^ 2} := fun x hx => by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    simp only [mem_ofPred_eq]
    rcases hx with hx | hx <;> nlinarith
  have hreal : (ρ : Measure ℝ).real (Icc (-R) R)ᶜ ≤ B / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [measureReal_mono (μ := (ρ : Measure ℝ)) hsub,
      measureReal_nonneg (μ := (ρ : Measure ℝ)) (s := (Icc (-R) R)ᶜ),
      sq_nonneg R]
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε'.le).2 ?_ |>.trans_eq
    (ENNReal.ofReal_toReal hεtop)
  exact hreal.trans hR1.le

/-- **Eventually constant images of finite measures are tight.** If the images of finite measures
`η n` under a map `f` are eventually equal to a finite measure `ν`, then the family of images is
tight: it is a finite set together with the constant tail. -/
theorem isTightMeasureSet_image_map_of_eventually_eq {Y : Type*} [MeasurableSpace Y]
    (η : ℕ → Measure Y) [∀ n, IsFiniteMeasure (η n)] (f : Y → α) (ν : Measure α)
    [IsFiniteMeasure ν] (m : ℕ) (h : ∀ n ≥ m, (η n).map f = ν) :
    IsTightMeasureSet ((fun P : Measure Y ↦ P.map f) '' range η) := by
  refine (isTightMeasureSet_of_finite (((finite_Iio m).image fun n ↦ (η n).map f).insert ν)
    ?_).subset ?_
  · rintro ρ (rfl | ⟨n, -, rfl⟩)
    · infer_instance
    · infer_instance
  · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rcases lt_or_ge n m with hn | hn
    · exact mem_insert_of_mem _ ⟨n, hn, rfl⟩
    · dsimp only
      rw [h n hn]
      exact mem_insert _ _

end TauCeti

end
