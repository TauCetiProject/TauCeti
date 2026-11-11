/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass.Basic
public import Mathlib.Probability.Kernel.Invariance

/-!
# Invariant measures on closed state spaces

Inclusion intertwines the action of a kernel restricted to a measurable closed set with
its ambient action. Consequently an invariant measure on the restricted state space is
exactly an ambient invariant measure concentrated on that set. The correspondence preserves
probability normalization and does not require a countable state space or finite measures.

This allows a stationary law calculated on an ambient space to be used on the smaller
irreducible state space, for example for a renewal countdown chain with bounded reset law.
Closedness here means that transitions cannot leave the set, not topological closedness.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.2 and 1.7.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {s : Set S}

/-- Inclusion commutes with applying a kernel restricted to a closed set, for every
initial measure on that set. -/
theorem map_comp_subtype (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure s) :
    ((κ.subtype hs) ∘ₘ ν).map Subtype.val = κ ∘ₘ (ν.map Subtype.val) := by
  rw [Measure.map_comp _ _ measurable_subtype_coe, map_subtype κ hs hclosed,
    ← comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

/-- A measure on a closed state space is invariant precisely when its inclusion into the
ambient space is invariant. No finiteness or normalization assumptions are needed. -/
theorem invariant_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure s) :
    (κ.subtype hs).Invariant ν ↔ κ.Invariant (ν.map Subtype.val) := by
  unfold Invariant
  rw [← map_comp_subtype κ hs hclosed ν]
  exact (MeasurableEmbedding.subtype_coe hs).map_injective.eq_iff.symm

/-- An ambient measure concentrated on a closed set is invariant if and only if its
pullback to that set is invariant for the restricted kernel. -/
theorem invariant_comap_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure S) (hν : ν sᶜ = 0) :
    (κ.subtype hs).Invariant (ν.comap Subtype.val) ↔ κ.Invariant ν := by
  rw [invariant_subtype_iff κ hs hclosed, map_comap_subtype_coe hs,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)]

/-- A closed-state restriction has an invariant probability exactly when the ambient kernel
has an invariant probability concentrated on those states. This includes the empty set:
neither side can then have a probability witness. -/
theorem exists_invariant_probability_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    (∃ ν : Measure s, IsProbabilityMeasure ν ∧ (κ.subtype hs).Invariant ν) ↔
      ∃ ν : Measure S, IsProbabilityMeasure ν ∧ κ.Invariant ν ∧ ν sᶜ = 0 := by
  constructor
  · rintro ⟨ν, hprob, hinv⟩
    have := hprob
    refine ⟨ν.map Subtype.val, inferInstance,
      (invariant_subtype_iff κ hs hclosed ν).1 hinv, ?_⟩
    rw [Measure.map_apply measurable_subtype_coe hs.compl]
    simp
  · rintro ⟨ν, hprob, hinv, hν⟩
    have := hprob
    have hae : ∀ᵐ x ∂ν, x ∈ range (Subtype.val : s → S) := by
      simpa only [Subtype.range_coe] using (ae_iff.mpr hν : ∀ᵐ x ∂ν, x ∈ s)
    exact ⟨ν.comap Subtype.val,
      (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap hae,
      (invariant_comap_subtype_iff κ hs hclosed ν hν).2 hinv⟩

end ProbabilityTheory.Kernel
