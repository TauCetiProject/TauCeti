/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Compactness.Compact

/-!
# Images of directed intersections of closed subgroups

A continuous homomorphism from a compact group to a group with closed points commutes with downward
directed intersections of closed subgroups. Indeed, the possible lifts of an element of every
image form a directed family of nonempty compact sets. This is the compactness step used to
recover prescribed finite images of an inverse limit of subgroups.
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
  refine le_antisymm (le_iInf fun i ↦ map_mono (iInf_le S i)) fun y hy ↦ ?_
  let C (i : ι) : Set G := (S i : Set G) ∩ f ⁻¹' {y}
  have hclosed (i : ι) : IsClosed (C i) := (hS i).inter (isClosed_singleton.preimage hf)
  have hne (i : ι) : (C i).Nonempty := by
    obtain ⟨x, hx, hxy⟩ := mem_iInf.mp hy i
    exact ⟨x, hx, hxy⟩
  have hC : Directed (· ⊇ ·) C := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hdir i j
    exact ⟨k, fun x hx ↦ ⟨hki hx.1, hx.2⟩, fun x hx ↦ ⟨hkj hx.1, hx.2⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hC hne
    (fun i ↦ (hclosed i).isCompact) hclosed
  exact ⟨x, mem_iInf.mpr fun i ↦ (Set.mem_iInter.mp hx i).1,
    (Set.mem_iInter.mp hx (Classical.choice ‹Nonempty ι›)).2⟩

end MonoidHom
