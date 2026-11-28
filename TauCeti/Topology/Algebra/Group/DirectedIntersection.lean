/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.Topology.Compactness.Compact

/-!
# Images of directed intersections of closed subgroups

A continuous homomorphism from a compact group to a group with closed points commutes with downward
directed intersections of closed subgroups. Indeed, the possible lifts of an element of every
image form a directed family of nonempty compact sets. This is the compactness step used to
recover prescribed images of an inverse limit of subgroups. In particular, for a compatible
family of subgroups under surjective projections from a compact group, the intersection of
the pullbacks has the prescribed image at each level.
-/

public section

namespace MonoidHom

open Subgroup

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [CompactSpace G]
  [TopologicalSpace H] [T1Space H]

/-- A continuous homomorphism from a compact group commutes with nonempty downward directed
intersections of closed subgroups. Only closedness of points in the target is needed; no
continuity of the group operations is required. -/
theorem map_iInf_of_isClosed {ι : Type*} [Nonempty ι] (f : G →* H) (hf : Continuous f)
    (S : ι → Subgroup G) (hS : ∀ i, IsClosed (S i : Set G)) (hdir : Directed (· ≥ ·) S) :
    (⨅ i, S i).map f = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simp only [coe_map, coe_iInf]
  exact hf.image_iInter_of_isClosed _ hS hdir

end MonoidHom

namespace TauCeti

/-- Let `p i` be continuous surjective projections from a compact group, commuting with
transition maps over a directed preorder. If the transitions map each prescribed subgroup onto
the subgroup below it and the pullbacks are closed, then their intersection maps onto each
prescribed subgroup. -/
theorem map_iInf_comap_of_compatible {ι G : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Group G] [TopologicalSpace G] [CompactSpace G] {Gᵢ : ι → Type*}
    [∀ i, Group (Gᵢ i)] [∀ i, TopologicalSpace (Gᵢ i)] [∀ i, T1Space (Gᵢ i)]
    (p : ∀ i, G →* Gᵢ i) (r : ∀ ⦃i j⦄, i ≤ j → Gᵢ j →* Gᵢ i)
    (H : ∀ i, Subgroup (Gᵢ i)) (hp : ∀ i, Continuous (p i))
    (hsurj : ∀ i, Function.Surjective (p i))
    (hclosed : ∀ i, IsClosed ((H i).comap (p i) : Set G))
    (hcomp : ∀ ⦃i j⦄ (hij : i ≤ j), (r hij).comp (p j) = p i)
    (hH : ∀ ⦃i j⦄ (hij : i ≤ j), (H j).map (r hij) = H i) (i : ι) :
    (⨅ j, (H j).comap (p j)).map (p i) = H i := by
  have : Nonempty ι := ⟨i⟩
  let S (j : ι) := (H j).comap (p j)
  have hanti : Antitone S := antitone_comap_of_map_le p r H hcomp fun _ _ h ↦ (hH h).le
  have hmap {k : ι} (hik : i ≤ k) : (S k).map (p i) = H i := by
    dsimp only [S]
    rw [← hcomp hik, ← Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective (hsurj k), hH hik]
  rw [MonoidHom.map_iInf_of_isClosed (p i) (hp i) S hclosed hanti.directed_ge]
  refine le_antisymm ((iInf_le _ i).trans_eq (hmap le_rfl)) (le_iInf fun j ↦ ?_)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact (hmap hik).symm.le.trans (Subgroup.map_mono (hanti hjk))

end TauCeti
