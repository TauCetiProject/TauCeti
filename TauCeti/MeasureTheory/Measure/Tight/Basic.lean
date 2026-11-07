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
* `TauCeti.isTightMeasureSet_image_map_of_eventually_eq`: images under a map of finite measures that
  are eventually equal to a fixed finite measure form a tight family.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone), "measure extraction via Prokhorov tightness".
-/

public section

open MeasureTheory Set

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
