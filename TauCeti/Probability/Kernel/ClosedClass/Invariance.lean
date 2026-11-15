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

Inclusion intertwines the action (and every power) of a kernel restricted to a measurable closed
set with its ambient action. Consequently an invariant measure on the restricted state space is
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

/-- Inclusion commutes with applying any power of a kernel restricted to a closed set, for every
initial measure on that set. -/
theorem map_pow_comp_subtype (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (n : ℕ) (ν : Measure s) :
    (((κ.subtype hs) ^ n) ∘ₘ ν).map Subtype.val = (κ ^ n) ∘ₘ (ν.map Subtype.val) := by
  rw [Measure.map_comp _ _ measurable_subtype_coe, map_subtype_pow κ hs hclosed n,
    ← comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

/-- Inclusion commutes with applying a kernel restricted to a closed set, for every
initial measure on that set. -/
theorem map_comp_subtype (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure s) :
    ((κ.subtype hs) ∘ₘ ν).map Subtype.val = κ ∘ₘ (ν.map Subtype.val) := by
  simpa only [pow_one] using map_pow_comp_subtype κ hs hclosed 1 ν

/-- A measure on a closed state space is invariant precisely when its inclusion into the
ambient space is invariant. No finiteness or normalization assumptions are needed. -/
theorem invariant_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure s) :
    (κ.subtype hs).Invariant ν ↔ κ.Invariant (ν.map Subtype.val) := by
  unfold Invariant
  rw [← map_comp_subtype κ hs hclosed ν]
  exact (MeasurableEmbedding.subtype_coe hs).map_injective.eq_iff.symm

private theorem map_comap_subtype_val_eq_self (hs : MeasurableSet s) {μ : Measure S}
    (hμ : μ sᶜ = 0) :
    (μ.comap (Subtype.val : s → S)).map Subtype.val = μ := by
  rw [map_comap_subtype_coe hs, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)]

/-- An ambient measure concentrated on a closed set is invariant if and only if its
pullback to that set is invariant for the restricted kernel. -/
theorem invariant_comap_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) (ν : Measure S) (hν : ν sᶜ = 0) :
    (κ.subtype hs).Invariant (ν.comap Subtype.val) ↔ κ.Invariant ν := by
  rw [invariant_subtype_iff κ hs hclosed, map_comap_subtype_val_eq_self hs hν]

private theorem map_subtype_val_compl_eq_zero (hs : MeasurableSet s) (ν : Measure s) :
    ν.map Subtype.val sᶜ = 0 := by
  rw [Measure.map_apply measurable_subtype_coe hs.compl]
  simp

private theorem isProbabilityMeasure_comap_subtype_val (hs : MeasurableSet s) {μ : Measure S}
    [IsProbabilityMeasure μ] (hμ : μ sᶜ = 0) :
    IsProbabilityMeasure (μ.comap (Subtype.val : s → S)) := by
  have hae : ∀ᵐ x ∂μ, x ∈ range (Subtype.val : s → S) := by
    simpa only [Subtype.range_coe] using (ae_iff.mpr hμ : ∀ᵐ x ∂μ, x ∈ s)
  exact (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap hae

/-- A closed-state restriction has an invariant probability exactly when the ambient kernel
has an invariant probability concentrated on those states. This includes the empty set:
neither side can then have a probability witness. -/
theorem exists_invariant_probability_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    (∃ ν : Measure s, IsProbabilityMeasure ν ∧ (κ.subtype hs).Invariant ν) ↔
      ∃ ν : Measure S, IsProbabilityMeasure ν ∧ κ.Invariant ν ∧ ν sᶜ = 0 := by
  constructor
  · rintro ⟨ν, hprob, hinv⟩
    exact ⟨ν.map Subtype.val, inferInstance,
      (invariant_subtype_iff κ hs hclosed ν).1 hinv, map_subtype_val_compl_eq_zero hs ν⟩
  · rintro ⟨ν, hprob, hinv, hν⟩
    exact ⟨ν.comap Subtype.val, isProbabilityMeasure_comap_subtype_val hs hν,
      (invariant_comap_subtype_iff κ hs hclosed ν hν).2 hinv⟩

/-- A closed-state restriction has a unique invariant probability measure if and only if the
ambient kernel has a unique invariant probability measure concentrated on those states. -/
theorem existsUnique_invariant_probability_subtype_iff (κ : Kernel S S) (hs : MeasurableSet s)
    (hclosed : κ.IsClosedSet s) :
    (∃! ν : Measure s, IsProbabilityMeasure ν ∧ (κ.subtype hs).Invariant ν) ↔
      ∃! ν : Measure S, IsProbabilityMeasure ν ∧ κ.Invariant ν ∧ ν sᶜ = 0 := by
  constructor
  · rintro ⟨ν, ⟨hprob, hinv⟩, huniq⟩
    refine ⟨ν.map Subtype.val, ⟨inferInstance, (invariant_subtype_iff κ hs hclosed ν).1 hinv,
      map_subtype_val_compl_eq_zero hs ν⟩, ?_⟩
    rintro μ ⟨hμ_prob, hμ_inv, hμ_supp⟩
    have heq : μ.comap Subtype.val = ν :=
      huniq (μ.comap Subtype.val) ⟨isProbabilityMeasure_comap_subtype_val hs hμ_supp,
        (invariant_comap_subtype_iff κ hs hclosed μ hμ_supp).2 hμ_inv⟩
    rw [← map_comap_subtype_val_eq_self hs hμ_supp, heq]
  · rintro ⟨μ, ⟨hμ_prob, hμ_inv, hμ_supp⟩, huniq⟩
    refine ⟨μ.comap Subtype.val, ⟨isProbabilityMeasure_comap_subtype_val hs hμ_supp,
      (invariant_comap_subtype_iff κ hs hclosed μ hμ_supp).2 hμ_inv⟩, ?_⟩
    rintro ν ⟨hν_prob, hν_inv⟩
    have hmap : ν.map Subtype.val = μ :=
      huniq (ν.map Subtype.val) ⟨inferInstance, (invariant_subtype_iff κ hs hclosed ν).1 hν_inv,
        map_subtype_val_compl_eq_zero hs ν⟩
    exact (MeasurableEmbedding.subtype_coe hs).map_injective
      (hmap.trans (map_comap_subtype_val_eq_self hs hμ_supp).symm)

end ProbabilityTheory.Kernel
