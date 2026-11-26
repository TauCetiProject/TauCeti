/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.Convex.Basic

/-!
# Invariant probability measures of a map

For a map `T : X → X` of a measurable space, `TauCeti.invariantProbabilities T` is the set of
probability measures `ν` with `MeasurePreserving T ν ν`, as a subset of `ProbabilityMeasure X`
with its topology of convergence in distribution. A map is *uniquely ergodic* when this set is a
singleton.

## Main definitions

* `TauCeti.invariantProbabilities T` — the `T`-invariant probability measures.
* `TauCeti.UniquelyErgodic T` — `T` has exactly one invariant probability measure.

## Main results

* `TauCeti.isClosed_invariantProbabilities` — for continuous `T` on a space with
  `HasOuterApproxClosed` (for instance a pseudometrizable space), the invariant probabilities form
  a closed set.
* `TauCeti.isCompact_invariantProbabilities` — on a compact Hausdorff such space they form a
  compact set.
* `TauCeti.invariantProbabilities_nonempty` — on a nonempty compact Hausdorff space they form a
  nonempty set (Mathlib's Krylov–Bogolyubov theorem).
* `TauCeti.convex_setOf_measurePreserving` — the invariant probabilities form a convex subset of
  `Measure X` over `ℝ≥0∞`, the set whose extreme points are the ergodic measures by Mathlib's
  `Ergodic.iff_mem_extremePoints`.
* `TauCeti.not_uniquelyErgodic_id_bool` — the identity of a two-point space is not uniquely
  ergodic.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {T : X → X}

/-- The invariant probability measures of a map `T : X → X`: the probability measures `ν` with
`MeasurePreserving T ν ν`. -/
def invariantProbabilities (T : X → X) : Set (ProbabilityMeasure X) :=
  {ν | MeasurePreserving T ν ν}

@[simp]
theorem mem_invariantProbabilities {ν : ProbabilityMeasure X} :
    ν ∈ invariantProbabilities T ↔ MeasurePreserving T ν ν :=
  Iff.rfl

/-- For a measurable map, a probability measure is invariant if and only if its pushforward is
itself. -/
theorem mem_invariantProbabilities_iff_map_eq (hT : Measurable T) {ν : ProbabilityMeasure X} :
    ν ∈ invariantProbabilities T ↔ ν.map T = ν := by
  rw [mem_invariantProbabilities, ← ProbabilityMeasure.toMeasure_injective.eq_iff,
    ProbabilityMeasure.toMeasure_map]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨hT, h⟩⟩

/-- For a measurable map, the invariant probability measures are those equal to their
pushforward. -/
theorem invariantProbabilities_eq_setOf_map_eq (hT : Measurable T) :
    invariantProbabilities T = {ν | ν.map T = ν} :=
  ext fun _ ↦ mem_invariantProbabilities_iff_map_eq hT

/-- `T` is *uniquely ergodic* if it has exactly one invariant probability measure. -/
def UniquelyErgodic (T : X → X) : Prop :=
  ∃ ν, invariantProbabilities T = {ν}

/-- `T` is uniquely ergodic if and only if its invariant probability measures form a
singleton. -/
theorem uniquelyErgodic_def : UniquelyErgodic T ↔ ∃ ν, invariantProbabilities T = {ν} :=
  Iff.rfl

/-- `T` is uniquely ergodic if and only if it has an invariant probability measure and any two
invariant probability measures are equal. -/
theorem uniquelyErgodic_iff :
    UniquelyErgodic T ↔
      (invariantProbabilities T).Nonempty ∧ (invariantProbabilities T).Subsingleton :=
  exists_eq_singleton_iff_nonempty_subsingleton

/-- An invariant probability measure that every invariant probability measure equals makes `T`
uniquely ergodic. -/
theorem UniquelyErgodic.of_mem {ν : ProbabilityMeasure X} (hν : ν ∈ invariantProbabilities T)
    (h : ∀ μ ∈ invariantProbabilities T, μ = ν) : UniquelyErgodic T :=
  ⟨ν, eq_singleton_iff_unique_mem.mpr ⟨hν, h⟩⟩

/-- A uniquely ergodic map has an invariant probability measure. -/
theorem UniquelyErgodic.nonempty (h : UniquelyErgodic T) : (invariantProbabilities T).Nonempty :=
  (uniquelyErgodic_iff.mp h).1

/-- Any two invariant probability measures of a uniquely ergodic map are equal. -/
theorem UniquelyErgodic.eq_of_mem (h : UniquelyErgodic T) {μ ν : ProbabilityMeasure X}
    (hμ : μ ∈ invariantProbabilities T) (hν : ν ∈ invariantProbabilities T) : μ = ν :=
  (uniquelyErgodic_iff.mp h).2 hμ hν

/-- The invariant probability measures form a convex subset of `Measure X` over `ℝ≥0∞`. -/
theorem convex_setOf_measurePreserving :
    Convex ℝ≥0∞ {ν : Measure X | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν} := by
  rintro μ ⟨hμ, hμ₁⟩ ν ⟨hν, hν₁⟩ a b - - hab
  have hT := hμ.measurable
  refine ⟨⟨hT, ?_⟩, ⟨?_⟩⟩
  · rw [Measure.map_add _ _ hT, Measure.map_smul, Measure.map_smul, hμ.map_eq, hν.map_eq]
    all_goals exact hT.aemeasurable
  · simp [hab]

section Topology

variable [TopologicalSpace X] [BorelSpace X]

/-- For a continuous map of a space with `HasOuterApproxClosed` (for instance a pseudometrizable
space), the invariant probability measures form a closed set. -/
theorem isClosed_invariantProbabilities [HasOuterApproxClosed X] (hT : Continuous T) :
    IsClosed (invariantProbabilities T) := by
  rw [invariantProbabilities_eq_setOf_map_eq hT.measurable]
  exact isClosed_eq (ProbabilityMeasure.continuous_map hT) continuous_id

/-- For a continuous map of a compact Hausdorff space with `HasOuterApproxClosed` (for instance a
compact metrizable space), the invariant probability measures form a compact set. -/
theorem isCompact_invariantProbabilities [HasOuterApproxClosed X] [CompactSpace X] [T2Space X]
    (hT : Continuous T) : IsCompact (invariantProbabilities T) :=
  (isClosed_invariantProbabilities hT).isCompact

/-- A continuous map of a nonempty compact Hausdorff space has an invariant probability measure
(Mathlib's Krylov–Bogolyubov theorem). -/
theorem invariantProbabilities_nonempty [T2Space X] [CompactSpace X] [Nonempty X]
    (hT : Continuous T) : (invariantProbabilities T).Nonempty := by
  obtain ⟨μ, hμ, -, hμ₁⟩ := exists_measurePreserving_probabilityMeasure hT
  exact ⟨⟨μ, hμ₁⟩, mem_invariantProbabilities.mpr hμ⟩

end Topology

/-- The identity of the two-point space is not uniquely ergodic: both Dirac masses are
invariant. -/
theorem not_uniquelyErgodic_id_bool : ¬ UniquelyErgodic (id : Bool → Bool) := by
  intro h
  have hmem (b : Bool) : (⟨Measure.dirac b, inferInstance⟩ : ProbabilityMeasure Bool) ∈
      invariantProbabilities id :=
    mem_invariantProbabilities.mpr (MeasurePreserving.id _)
  have h' := congrArg (fun μ : ProbabilityMeasure Bool ↦ (μ : Measure Bool) {true})
    (h.eq_of_mem (hmem true) (hmem false))
  simp at h'

end TauCeti
