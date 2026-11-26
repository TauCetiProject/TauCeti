/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Contact times for continuous additive actions

For a continuous additive group action on a topological space, contact times of two closed
sets are compact if the time domain and a set containing all contact positions are compact.
The time type need only be topological. With a linear order and closed upper rays, a nonempty
compact contact-time set has a greatest element by `IsCompact.exists_isGreatest`.

## References

* R. Brasca, [closed-barrier formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/cfee5e52aa5576999d055c12bd0f004b0d7cba9f).
-/

public section

open Function Set Topology
open scoped Pointwise

namespace IsCompact

variable {G X τ : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [TopologicalSpace X] [AddAction G X] [ContinuousVAdd G X]
  [TopologicalSpace τ] {D : Set τ} {a : τ → G} {S C K : Set X}

/-- Contact times for a continuous additive action on two closed sets are compact when the
time domain is compact and all contact positions lie in a fixed compact set. -/
theorem isCompact_contactTimes (hD : IsCompact D) (ha : ContinuousOn a D)
    (hS : IsClosed S) (hC : IsClosed C) (hK : IsCompact K)
    (hsweep : ∀ t ∈ D, (a t +ᵥ S) ∩ C ⊆ K) :
    IsCompact {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} := by
  let : CompactSpace D := isCompact_iff_compactSpace.1 hD
  let P : Set (X × D) := Prod.fst ⁻¹' C ∩ (fun p ↦ (-a p.2) +ᵥ p.1) ⁻¹' S
  have hmem (x : X) (t : D) : (x, t) ∈ P ↔ x ∈ (a t +ᵥ S) ∩ C := by
    simp only [P, mem_inter_iff, mem_preimage, mem_vadd_set_iff_neg_vadd_mem, and_comm]
  have hP : IsCompact P :=
    (hK.prod isCompact_univ).of_isClosed_subset
      ((hC.preimage continuous_fst).inter
        (hS.preimage ((ha.domRestrict.comp continuous_snd).neg.vadd continuous_fst)))
      fun p hp ↦ ⟨hsweep p.2 p.2.property ((hmem p.1 p.2).1 hp), mem_univ _⟩
  have himage : (fun p : X × D ↦ (p.2 : τ)) '' P =
      {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} := by
    ext t
    constructor
    · rintro ⟨⟨x, s⟩, hs, rfl⟩
      exact ⟨s.property, x, (hmem x s).1 hs⟩
    · rintro ⟨ht, x, hx⟩
      exact ⟨(x, ⟨t, ht⟩), (hmem x ⟨t, ht⟩).2 hx, rfl⟩
  rw [← himage]
  exact hP.image (continuous_subtypeVal.comp continuous_snd)

end IsCompact
