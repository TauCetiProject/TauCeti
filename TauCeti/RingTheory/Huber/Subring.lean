/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic

/-!
# Subrings containing a pseudouniformiser

A subring of a Tate ring is Tate as soon as it contains a pseudouniformiser and its inverse.
The topology is always the subspace topology. No closedness assumption is needed: intersecting
a ring of definition with the subring supplies an open bounded subring. Closedness is needed
only when one also wants completeness.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace Subring

section Bounded

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- The inverse image of a bounded set under a subring inclusion is bounded for the subspace
topology. -/
theorem isBounded_preimage_subtype (S : Subring R) {s : Set R} (hs : IsBounded s) :
    IsBounded (Subtype.val ⁻¹' s : Set S) := by
  rw [isBounded_iff] at hs ⊢
  intro U hU
  rw [nhds_induced] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  obtain ⟨V, hV, hVW⟩ := hs W hW
  refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt.preimage_mem_nhds hV, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact hWU (hVW (Set.mul_mem_mul hx hy))

end Bounded

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]

/-- A subring containing a pseudouniformiser as a unit is a Tate ring in its subspace topology.
The unit hypothesis says that the inverse also lies in the subring. -/
theorem isTateRing_of_isPseudoUniformizer (S : Subring R) (u : Rˣ)
    (hu : IsPseudoUniformizer u.val) (hmem : u.val ∈ S) (hinv : (u⁻¹).val ∈ S) :
    IsTateRing S := by
  let v : Sˣ := Units.mkOfMulEqOne ⟨u.val, hmem⟩ ⟨(u⁻¹).val, hinv⟩ (Subtype.ext u.val_inv)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  exact IsTateRing.of_isOpen_isBounded (P.ringOfDefinition.comap S.subtype)
    (P.isOpen_ringOfDefinition.preimage continuous_subtype_val)
    (S.isBounded_preimage_subtype P.isBounded_ringOfDefinition)
    (isPseudoUniformizer_iff.mpr ⟨v.isUnit,
      isTopologicallyNilpotent_mk hmem hu.isTopologicallyNilpotent⟩)

end Subring
