/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Tightness of a finite family of finite measures

Mathlib's `MeasureTheory.isTightMeasureSet_singleton` says that a single finite measure on a
complete second-countable pseudo-metrizable space is tight, and `IsTightMeasureSet.union` says
that tightness survives a binary union. Together they give tightness of any *finite* set of
finite measures, which is the form the Prokhorov extraction arguments need in order to discard
the finitely many exceptional members of a family for which a uniform tail bound is unavailable.

## Main declarations

* `TauCeti.isTightMeasureSet_of_finite`: a finite set of finite measures is tight.
* `TauCeti.isTightMeasureSet_range_of_finite`: a family of finite measures indexed by a finite type
  has tight range.
* `TauCeti.isTightMeasureSet_range_of_eventually_eq`: a family of finite measures that is equal to
  a fixed measure off finitely many indices has tight range.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone), "measure extraction via Prokhorov tightness".
-/

public section

open Filter MeasureTheory Set

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

end TauCeti

end
