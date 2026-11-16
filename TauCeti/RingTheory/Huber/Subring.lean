/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Subrings of Huber rings

A subring `S` of a topological ring `R` carries the subspace topology. This file compares the
Huber-theoretic notions of `S` with those of `R`.

A subring of a Tate ring is Tate as soon as it contains a pseudouniformiser and its inverse.
No closedness assumption is needed: intersecting a ring of definition with the subring supplies
an open bounded subring. Closedness is needed only when one also wants completeness.

Boundedness for the subspace topology is in general weaker than boundedness in `R`: the
neighbourhoods of zero of `S` only test against elements of `S`. Once `S` is itself a Tate ring,
the two notions agree, because the inclusion of a Tate ring into a Huber ring sends bounded sets
to bounded sets (`TauCeti.Huber.IsBounded.image_of_isTateRing`). Consequently `S° = R° ∩ S` for
a Tate subring `S` of a Huber ring `R`.

These are the comparisons needed for the fixed subring of a finite group acting continuously on
a Tate ring (`TauCeti/RingTheory/Huber/Pair/Invariant.lean`).

## Main results

* `Subring.isTateRing_of_isPseudoUniformizer`: a subring containing a pseudouniformiser and its
  inverse is Tate.
* `Subring.isBounded_image_val_iff`: in a Tate subring of a Huber ring, a subset is bounded
  exactly when its image in the ambient ring is.
* `Subring.isPowerBounded_coe_iff`: likewise for power-boundedness.
* `Subring.comap_powerBoundedSubring`: `R° ∩ S = S°` for a Tate subring `S`.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace Subring

section Tate

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

end Tate

section Bounded

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]

/-- **Boundedness in a Tate subring.** If the subring `S` of a Huber ring is a Tate ring for its
subspace topology, a subset of `S` is bounded in `S` exactly when its image is bounded in the
ambient ring. -/
@[simp]
theorem isBounded_image_val_iff (S : Subring R) [IsTateRing S] {s : Set S} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  ⟨fun h ↦ by
    simpa [Set.preimage_image_eq _ Subtype.val_injective] using S.isBounded_preimage_subtype h,
    fun h ↦ h.image_of_isTateRing (f := S.subtype) continuous_subtype_val.continuousAt⟩

/-- In a Tate subring of a Huber ring, an element is power-bounded exactly when it is
power-bounded in the ambient ring. -/
@[simp]
theorem isPowerBounded_coe_iff (S : Subring R) [IsTateRing S] {x : S} :
    IsPowerBounded (x : R) ↔ IsPowerBounded x :=
  ⟨S.isPowerBounded_of_isPowerBounded_coe,
    fun h ↦ h.map_of_isTateRing (f := S.subtype) continuous_subtype_val.continuousAt⟩

/-- **`S° = R° ∩ S`** for a subring `S` of a Huber ring that is Tate in its subspace topology. -/
@[simp]
theorem comap_powerBoundedSubring (S : Subring R) [IsTateRing S] :
    (powerBoundedSubring R).comap S.subtype = powerBoundedSubring S := by
  ext
  rw [Subring.mem_comap, mem_powerBoundedSubring, mem_powerBoundedSubring]
  exact S.isPowerBounded_coe_iff

end Bounded

end Subring
