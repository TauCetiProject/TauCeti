/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import TauCeti.Combinatorics.Network.Subnetwork

/-!
# Strong connectivity of subnetworks

A subnetwork has its own vertex type, consisting only of the selected ambient vertices. This file
characterizes strong connectivity on that subtype by ambient walks whose traced subnetworks remain
inside the selected subnetwork. Thus omitted ambient vertices play no role, while every arrow of a
witnessing walk retains its original identity.

The singleton subnetwork is strongly connected even when the ambient network has further vertices;
this records the empty-walk boundary case of the characterization.
-/

public section

namespace TauCeti.Network.Subnetwork

universe u w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

/-- A subnetwork is strongly connected exactly when every two selected ambient vertices are joined
by an ambient walk whose vertices and arrows all belong to the subnetwork. -/
theorem isStronglyConnected_iff_exists_toSubnetwork_le (S : N.Subnetwork) :
    @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩ ↔
      ∀ x ∈ S.vertexSet, ∀ y ∈ S.vertexSet,
        ∃ p : ArrowWalk N.Hom x y, p.toSubnetwork ≤ S := by
  rw [Quiver.isStronglyConnected_iff]
  constructor
  · intro h x hx y hy
    obtain ⟨p⟩ := h ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨S.mapPath p, toSubnetwork_mapPath_le S p⟩
  · intro h x y
    obtain ⟨p, hp⟩ := h x.1 x.2 y.1 y.2
    obtain ⟨q, -⟩ := (S.exists_mapPath_eq_iff p).2 hp
    exact ⟨q⟩

end TauCeti.Network.Subnetwork

namespace TauCeti.Network

universe u w

variable {K : Type w} {V : Type u} [LE K]

/-- A singleton subnetwork is strongly connected on its own one-vertex carrier, independently of
the other vertices and arrows of the ambient network. -/
theorem isStronglyConnected_singletonSubnetwork (N : Network K V) (x : V) :
    @Quiver.IsStronglyConnected ↥(N.singletonSubnetwork x).vertexSet
      ⟨(N.singletonSubnetwork x).Hom⟩ := by
  rw [Quiver.isStronglyConnected_iff]
  intro y z
  have hy : y.1 = x := by simpa using y.2
  have hz : z.1 = x := by simpa using z.2
  obtain rfl : y = z := Subtype.ext (hy.trans hz.symm)
  exact ⟨ArrowWalk.nil y⟩

end TauCeti.Network
