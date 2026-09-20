/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.StandardBorelModel
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Reading a graphon on the unit interval

Every standard Borel probability space receives a measure-preserving map out of `(I, volume)`
(Janson, Theorem A.9), and the cut distance does not change when a graphon is read along a
measure-preserving map (`cutDist_comap_right`). Pulling a graphon back along such a map therefore
puts it on the canonical carrier `(I, volume)` at no cost.

The map is an arbitrary choice, and so is the representative built from it; what is canonical is
its cut class, which is what `cutDist_unitIntervalModel` records.

The standard Borel hypothesis the map theorem needs costs nothing, because every graphon is
already a pullback from a standard Borel carrier
(`TauCeti.DenseGraphLimits.Graphon.exists_comap_standardBorel`, Janson, Lemma 7.3): a jointly
measurable kernel reads only countably many measurable sets of each argument. Composing the two
reductions puts *every* graphon, on an arbitrary probability carrier, at cut distance zero from
one on the unit interval (Janson, Theorem 7.1) -- the carrier-free representation the separation
converse runs on.

## Main definitions

* `TauCeti.DenseGraphLimits.unitIntervalModel` -- the `(I, volume)` representative of a graphon on
  a standard Borel probability carrier.

## Main results

* `TauCeti.DenseGraphLimits.cutDist_unitIntervalModel` -- cut distances to a graphon are unchanged
  by reading it on the unit interval;
* `TauCeti.DenseGraphLimits.exists_graphon_unitInterval_cutDist_eq_zero` -- every graphon, on an
  arbitrary probability carrier, is at cut distance zero from one on the unit interval.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem A.9, Lemma 7.3 and Theorem 7.1.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

/-- The `(I, volume)` representative of a graphon on a standard Borel probability carrier: its
pullback along a measure-preserving map out of the unit interval (Janson, Thm A.9).

The map is an arbitrary choice; `cutDist_unitIntervalModel` shows that no cut distance to the
graphon depends on it. -/
def unitIntervalModel (ν : Measure α) [IsProbabilityMeasure ν] (V : Graphon α ν) :
    Graphon I (volume : Measure I) :=
  V.comap (Measure.exists_measurePreserving_from_unitInterval ν).choose
    (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec.measurable volume

/-- Reading a graphon on the unit interval leaves every cut distance to it unchanged. -/
@[simp]
theorem cutDist_unitIntervalModel (ν : Measure α) [IsProbabilityMeasure ν] (U : Graphon Ω μ)
    (V : Graphon α ν) : cutDist U (unitIntervalModel ν V) = cutDist U V :=
  cutDist_comap_right U V (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec

/-- **Every graphon is at cut distance zero from a graphon on the unit interval** (Janson,
Thm 7.1), with **no hypothesis on its carrier**: the unit interval sees every graphon up to cut
distance, so a cross-carrier statement invariant under `cutDist = 0` may be proved there.

The carrier is reduced in two steps, neither of which moves the cut class: a graphon is first
rewritten as a pullback from a standard Borel carrier
(`TauCeti.DenseGraphLimits.Graphon.exists_comap_standardBorel`), which `unitIntervalModel` then
reads on the unit interval. -/
theorem exists_graphon_unitInterval_cutDist_eq_zero (W : Graphon Ω μ) :
    ∃ V : Graphon I (volume : Measure I), cutDist W V = 0 := by
  obtain ⟨q, hq, V, hV⟩ := W.exists_comap_standardBorel
  have hVW : cutDist V W = 0 := by
    have h : cutDist V (V.comap q hq μ) = cutDist V V := cutDist_comap_right V V ⟨hq, rfl⟩
    rwa [hV, cutDist_self] at h
  refine ⟨unitIntervalModel (μ.map q) V, le_antisymm ?_ (cutDist_nonneg _ _)⟩
  calc cutDist W (unitIntervalModel (μ.map q) V)
      ≤ cutDist W V + cutDist V (unitIntervalModel (μ.map q) V) := cutDist_triangle _ _ _
    _ = 0 := by rw [cutDist_unitIntervalModel, cutDist_self, cutDist_comm, hVW, add_zero]

end DenseGraphLimits

end TauCeti
