/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Connected
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local
public import TauCeti.Topology.ConnectedComponents

/-!
# Connected components of locally semialgebraic sets

A semialgebraic set has finitely many connected components, each semialgebraic. More locally,
if a set is semialgebraic near an ambient point, a sufficiently small open semialgebraic
neighborhood meets only finitely many of its global components, and the intersection with each
component is semialgebraic. Consequently the distinct nonempty connected components of a
locally semialgebraic set form a locally finite family of locally semialgebraic sets.

The local assertions include ambient points outside the set, in particular frontier points.
No boundedness or closedness is required. A component may meet the chosen neighborhood in
several connected pieces: its intersection is a finite union of connected semialgebraic pieces,
not necessarily one component of the local restriction.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Sections 2.4 and 8.1 (connected components and locally semialgebraic sets).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {σ : Type*} [Finite σ] {s V : Set (σ → ℝ)} {x : σ → ℝ}

/-- Every connected component of a semialgebraic set is semialgebraic, including the empty
component assigned to a point outside the set. -/
theorem IsSemialgebraic.connectedComponentIn (hs : IsSemialgebraic s) (x : σ → ℝ) :
    IsSemialgebraic (_root_.connectedComponentIn s x) := by
  obtain ⟨𝒞, h𝒞, -, hc, hcover⟩ := hs.exists_finite_isConnected_partition
  have hcover' : ⋃₀ 𝒞 = s ∩ univ := by simpa using hcover
  rw [← inter_univ (_root_.connectedComponentIn s x),
    connectedComponentIn_inter_eq_sUnion (fun t ht ↦ (hc t ht).1.isPreconnected) hcover',
    sUnion_eq_biUnion]
  exact .biUnion (h𝒞.subset (sep_subset _ _)) fun t ht ↦ (hc t ht.1).2

/-- The distinct nonempty connected components of a semialgebraic set form a finite set. -/
theorem IsSemialgebraic.finite_image_connectedComponentIn (hs : IsSemialgebraic s) :
    (_root_.connectedComponentIn s '' s).Finite := by
  obtain ⟨𝒞, h𝒞, -, hc, hcover⟩ := hs.exists_finite_isConnected_partition
  rw [← hcover]
  exact h𝒞.image_connectedComponentIn_sUnion (fun t ht ↦ (hc t ht).1.isPreconnected)
    (hcover ▸ Subset.rfl)

/-- Near any point where a set is semialgebraic, all its global connected components have
semialgebraic intersections with one common, arbitrarily small open semialgebraic neighborhood.
The center need not lie in the set. -/
theorem SemialgebraicAt.exists_isSemialgebraic_inter_connectedComponentIn
    (hs : SemialgebraicAt s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsSemialgebraic U ∧
      ∀ y, IsSemialgebraic (_root_.connectedComponentIn s y ∩ U) := by
  obtain ⟨U, hUo, hxU, hUV, hU, hsU⟩ := hs.exists_subset hV
  obtain ⟨𝒞, h𝒞, -, hc, hcover⟩ := hsU.exists_finite_isConnected_partition
  refine ⟨U, hUo, hxU, hUV, hU, fun y ↦ ?_⟩
  rw [connectedComponentIn_inter_eq_sUnion (fun t ht ↦ (hc t ht).1.isPreconnected) hcover,
    sUnion_eq_biUnion]
  exact .biUnion (h𝒞.subset (sep_subset _ _)) fun t ht ↦ (hc t ht.1).2

/-- Only finitely many global connected components meet a sufficiently small neighborhood of
an ambient point where the set is semialgebraic. The neighborhood can be chosen inside any
prescribed neighborhood, even when the center is outside the set. -/
theorem SemialgebraicAt.exists_finite_image_connectedComponentIn
    (hs : SemialgebraicAt s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsSemialgebraic U ∧
      (_root_.connectedComponentIn s '' (s ∩ U)).Finite := by
  obtain ⟨U, hUo, hxU, hUV, hU, hsU⟩ := hs.exists_subset hV
  obtain ⟨𝒞, h𝒞, -, hc, hcover⟩ := hsU.exists_finite_isConnected_partition
  refine ⟨U, hUo, hxU, hUV, hU, ?_⟩
  rw [← hcover]
  exact h𝒞.image_connectedComponentIn_sUnion (fun t ht ↦ (hc t ht).1.isPreconnected)
    (hcover ▸ inter_subset_left)

/-- Every connected component of a locally semialgebraic set is locally semialgebraic,
including at ambient frontier points not belonging to that component. -/
theorem IsLocallySemialgebraic.connectedComponentIn (hs : IsLocallySemialgebraic s)
    (y : σ → ℝ) : IsLocallySemialgebraic (_root_.connectedComponentIn s y) := by
  refine isLocallySemialgebraic_iff.2 fun x ↦ ?_
  obtain ⟨U, hUo, hxU, -, hU, hcomp⟩ :=
    (hs.semialgebraicAt x).exists_isSemialgebraic_inter_connectedComponentIn
      (V := univ) univ_mem
  exact semialgebraicAt_def.2 ⟨U, hUo, hxU, hU, hcomp y⟩

/-- The family of distinct nonempty connected components of a locally semialgebraic set is
locally finite in the ambient affine space. Indexing by components rather than their points
avoids repetitions in the family. -/
theorem IsLocallySemialgebraic.locallyFinite_connectedComponentIn
    (hs : IsLocallySemialgebraic s) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set (σ → ℝ))) := by
  intro x
  obtain ⟨U, hUo, hxU, -, -, hfin⟩ :=
    (hs.semialgebraicAt x).exists_finite_image_connectedComponentIn (V := univ) univ_mem
  refine ⟨U, hUo.mem_nhds hxU, (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro C ⟨y, hyC, hyU⟩
  obtain ⟨z, hz, hzC⟩ := C.property
  have hy : y ∈ _root_.connectedComponentIn s z := hzC ▸ hyC
  exact ⟨y, ⟨connectedComponentIn_subset s z hy, hyU⟩,
    (connectedComponentIn_eq hy).symm.trans hzC⟩

end TauCeti
