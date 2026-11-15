/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Connected.PathConnected

/-!
# The group of path components of a topological group

For a topological group `G`, the path component `G₀` of the identity is a normal subgroup
(`Subgroup.pathComponentOne`), and the quotient `G ⧸ G₀` is the group `π₀(G)` of path components of
`G`. Two elements have the same image in `π₀(G)` exactly when they are joined by a path
(`QuotientGroup.mk_eq_mk_iff_joined_pathComponentOne`).
-/

public section

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Two elements of a topological group have the same image in `π₀(G) = G ⧸ G₀` exactly when they
are joined by a path. -/
theorem mk_eq_mk_iff_joined_pathComponentOne {g h : G} :
    (g : G ⧸ Subgroup.pathComponentOne G) = h ↔ Joined g h := by
  rw [QuotientGroup.eq, ← SetLike.mem_coe, Subgroup.coe_pathComponentOne, mem_pathComponent_iff]
  refine ⟨fun hgh ↦ ?_, fun hgh ↦ ?_⟩
  · simpa using hgh.map (f := (g * ·)) (by fun_prop)
  · simpa using hgh.map (f := (g⁻¹ * ·)) (by fun_prop)

/-- An element of a topological group lies in the path component of the identity exactly when its
image in `π₀(G)` is trivial. -/
theorem mk_eq_one_iff_joined_pathComponentOne {g : G} :
    (g : G ⧸ Subgroup.pathComponentOne G) = 1 ↔ Joined g 1 := by
  rw [← QuotientGroup.mk_one, mk_eq_mk_iff_joined_pathComponentOne]

end QuotientGroup
