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
`G`. An element lies in `G₀` exactly when it is joined to `1` by a path
(`Subgroup.mem_pathComponentOne_iff`), and two elements have the same image in `π₀(G)` exactly when
they are joined by a path (`QuotientGroup.mk_eq_mk_iff_joined_pathComponentOne`).
-/

public section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An element of a topological group lies in the path component of the identity exactly when it
is joined to `1` by a path. -/
@[simp]
theorem Subgroup.mem_pathComponentOne_iff {g : G} :
    g ∈ Subgroup.pathComponentOne G ↔ Joined g 1 := by
  rw [← SetLike.mem_coe, Subgroup.coe_pathComponentOne, mem_pathComponent_iff]
  exact ⟨Joined.symm, Joined.symm⟩

namespace QuotientGroup

/-- Two elements of a topological group have the same image in `π₀(G) = G ⧸ G₀` exactly when they
are joined by a path. -/
@[simp]
theorem mk_eq_mk_iff_joined_pathComponentOne {g h : G} :
    (g : G ⧸ Subgroup.pathComponentOne G) = h ↔ Joined g h := by
  rw [QuotientGroup.eq, Subgroup.mem_pathComponentOne_iff]
  refine ⟨fun hgh ↦ ?_, fun hgh ↦ ?_⟩
  · simpa using (hgh.map (f := (g * ·)) (by fun_prop)).symm
  · simpa using (hgh.map (f := (g⁻¹ * ·)) (by fun_prop)).symm

/-- An element of a topological group lies in the path component of the identity exactly when its
image in `π₀(G)` is trivial. -/
theorem mk_eq_one_iff_joined_pathComponentOne {g : G} :
    (g : G ⧸ Subgroup.pathComponentOne G) = 1 ↔ Joined g 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_pathComponentOne_iff]

end QuotientGroup
