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
