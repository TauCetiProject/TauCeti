/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Measurable enumeration beyond finite measures

A measurable family of integer-valued measures admits a measurable occurrence enumeration
when there is a common countable measurable cover of finite mass. In particular, this applies
to measures finite on compact sets on a sigma-compact standard Borel space. Locations are
repeated according to their multiplicity, and summing the optional Dirac occurrences recovers
the measure exactly, even when its total mass is infinite.

The construction enumerates the finite restrictions to the disjoint pieces of the cover and
interleaves their enumerations. Consequently `none` can occur between actual occurrences;
it is not a signal that the enumeration has ended. This representation supplies the locations
for attaching independent marks to an infinite locally finite configuration.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 5–6 (marking and measurable enumeration).
-/

public section

open MeasureTheory Set
open scoped ENNReal

/-- A measurable family of integer-valued measures with a common countable finite-mass
cover has a measurable enumeration of all its occurrences. The cover need not be increasing
or disjoint. Missing entries may be interspersed with actual occurrences. -/
theorem Measurable.exists_occurrence_enumeration_of_cover
    {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [StandardBorelSpace X]
    {μ : α → Measure X} (hm : Measurable μ)
    (hint : ∀ a, (μ a).IsIntegerValued) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hfinite : ∀ a n, μ a (s n) ≠ ∞) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      ∀ a, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) := by
  have hpiece (n : ℕ) : Measurable fun a => (μ a).restrict (disjointed s n) :=
    (ProbabilityTheory.Kernel.restrict ⟨μ, hm⟩ (MeasurableSet.disjointed hs n)).measurable
  have hfin (a : α) (n : ℕ) : IsFiniteMeasure ((μ a).restrict (disjointed s n)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top (hfinite a n)
      (measure_mono (disjointed_le s n)))
  choose e he _ heq using fun n => (hpiece n).exists_finite_occurrence_enumeration
    (fun a => hfin a n) (fun a => (hint a).restrict)
  refine ⟨fun a k => e k.unpair.1 a k.unpair.2,
    measurable_pi_iff.2 (fun k => (measurable_pi_apply k.unpair.2).comp (he k.unpair.1)),
    fun a => ?_⟩
  calc
    μ a = Measure.sum (fun n => (μ a).restrict (disjointed s n)) := by
      rw [← Measure.restrict_iUnion (disjoint_disjointed s) (MeasurableSet.disjointed hs),
        iUnion_disjointed, hcover, Measure.restrict_univ]
    _ = Measure.sum (fun n => Measure.sum (fun k => (e n a k).elim 0 Measure.dirac)) := by
      simp_rw [heq]
    _ = Measure.sum (fun k : ℕ => (e k.unpair.1 a k.unpair.2).elim 0 Measure.dirac) := by
      rw [Measure.sum_sum]
      exact (Measure.sum_comp_equiv Nat.pairEquiv.symm _).symm

/-- A measurable family of integer-valued measures finite on compact sets on a sigma-compact
Hausdorff standard Borel space can be enumerated measurably, with multiplicities retained and no
finite-total-mass assumption. Missing entries may be interspersed with actual occurrences. -/
theorem Measurable.exists_occurrence_enumeration_of_isFiniteMeasureOnCompacts
    {α X : Type*} [MeasurableSpace α] [TopologicalSpace X] [T2Space X]
    [SigmaCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [StandardBorelSpace X]
    {μ : α → Measure X} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasureOnCompacts (μ a))
    (hint : ∀ a, (μ a).IsIntegerValued) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      ∀ a, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) :=
  hm.exists_occurrence_enumeration_of_cover hint (compactCovering X)
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun a n => by
      have := hfinite a
      exact (isCompact_compactCovering X n).measure_ne_top)
