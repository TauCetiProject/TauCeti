/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Walk
public import TauCeti.Combinatorics.Network.Connectivity.Basic

/-!
# Directed connectivity under network isomorphisms

Relabelling vertices and arrow identities preserves arc reachability, arc-strong connectivity,
and vertex-strong connectivity at every threshold. Consequently the numerical arc and vertex
strong connectivities are invariant too. Deletion sets are transported bijectively, so parallel
arrows are counted separately and loops are retained.

No finiteness is needed: only the sets of deleted vertices or arrows are finite. The numerical
identities include empty vertex types, where arc connectivity is infinite and vertex strong
connectivity is zero. Connectivity concerns all arrows, independently of their bounds.
-/

public section

namespace TauCeti.Network.Iso

universe u u' w

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network K V} {N' : Network K W}

/-- Relabelling a network preserves and reflects local arc reachability at every threshold. -/
@[simp]
theorem isArcReachable_iff (e : N ≃ₙ N') (k : ℕ) (s t : V) :
    IsArcReachable N'.Hom k (e.vertexEquiv s) (e.vertexEquiv t) ↔
      IsArcReachable N.Hom k s t := by
  rw [isArcReachable_def, isArcReachable_def]
  exact (e.totalHomEquiv.finsetCongr.forall_congr fun F ↦ by
    simp only [Equiv.finsetCongr_apply, Finset.card_map, Finset.coe_map]
    exact forall_congr' fun _ ↦ (e.reachableWithout_image_iff F).symm).symm

/-- Arc-strong connectivity is unchanged by network isomorphism, even on empty carriers. -/
theorem isArcStrong_iff (e : N ≃ₙ N') (k : ℕ) :
    IsArcStrong N'.Hom k ↔ IsArcStrong N.Hom k := by
  rw [isArcStrong_def, isArcStrong_def]
  exact (e.vertexEquiv.forall_congr fun s ↦
    e.vertexEquiv.forall_congr fun t ↦ (e.isArcReachable_iff k s t).symm).symm

/-- Vertex-strong connectivity is unchanged by relabelling vertices and arrows. -/
theorem isVertexStrong_iff (e : N ≃ₙ N') (k : ℕ) :
    IsVertexStrong N'.Hom k ↔ IsVertexStrong N.Hom k := by
  rw [isVertexStrong_def, isVertexStrong_def]
  refine and_congr ?_ ?_
  · rw [ENat.card_congr e.vertexEquiv]
  · exact (e.vertexEquiv.finsetCongr.forall_congr fun X ↦ by
      simp only [Equiv.finsetCongr_apply, Finset.card_map, Finset.coe_map]
      refine forall_congr' fun _ ↦ ?_
      exact e.vertexEquiv.forall_congr fun s ↦ by
        simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
        refine forall_congr' fun _ ↦ ?_
        exact e.vertexEquiv.forall_congr fun t ↦ by
          simp only [Equiv.symm_apply_apply]
          exact forall_congr' fun _ ↦
            (e.reachableAvoiding_image_iff X).symm).symm

/-- Numerical arc connectivity is invariant under network isomorphism. -/
theorem arcConnectivity_eq (e : N ≃ₙ N') :
    arcConnectivity N'.Hom = arcConnectivity N.Hom := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [← isArcStrong_iff_le_arcConnectivity, ← isArcStrong_iff_le_arcConnectivity,
    e.isArcStrong_iff]

/-- Numerical vertex strong connectivity is invariant under network isomorphism, including
on empty carriers; no nonemptiness hypothesis is needed. -/
theorem vertexStrongConnectivity_eq (e : N ≃ₙ N') :
    vertexStrongConnectivity N'.Hom = vertexStrongConnectivity N.Hom := by
  cases isEmpty_or_nonempty V with
  | inl h =>
    have : IsEmpty W := ⟨fun w ↦ isEmptyElim (e.vertexEquiv.symm w)⟩
    simp
  | inr h =>
    have : Nonempty W := h.map e.vertexEquiv
    apply ENat.eq_of_forall_natCast_le_iff
    intro k
    rw [← isVertexStrong_iff_le_vertexStrongConnectivity,
      ← isVertexStrong_iff_le_vertexStrongConnectivity, e.isVertexStrong_iff]

end TauCeti.Network.Iso
