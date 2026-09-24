/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Subgroups and topological closure

This file records how subgroup constructions interact with topological closure. It provides
normality of the closure of a normal subgroup, the kernel criterion for a closed normal closure,
and compatibility of multiplicative and additive subgroup closures.

A continuous homomorphism carries the topological closure of a subgroup into the topological
closure of its image, and a closed subgroup containing the commutators `⁅A, B⁆` also contains the
commutators `⁅A, closure B⁆`. These are the two closure facts needed to run commutator calculus on
closed subgroups that are given as topological closures, such as the terms of a lower central
series of a profinite group.

## Main results

* `TauCeti.instNormal_topologicalClosure_normalClosure`: the closure of a normal closure is
  normal.
* `TauCeti.topologicalClosure_normalClosure_le_ker`: relators killed by a continuous map have
  closed normal closure in its kernel.
* `Subgroup.toAddSubgroup_topologicalClosure`: converting to an additive subgroup commutes with
  topological closure.
* `MonoidHom.map_topologicalClosure_le`: a continuous homomorphism maps the topological closure of
  a subgroup into the topological closure of its image.
* `Subgroup.commutator_topologicalClosure_right_le`: a closed subgroup containing `⁅A, B⁆`
  contains `⁅A, B.topologicalClosure⁆`.
-/

public section

namespace TauCeti

/-- The closure of the normal closure of a set is a normal subgroup. -/
instance instNormal_topologicalClosure_normalClosure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (s : Set G) :
    ((Subgroup.normalClosure s).topologicalClosure).Normal := by
  exact Subgroup.is_normal_topologicalClosure _

end TauCeti

namespace TauCeti

/-- The closed normal closure of relators lies in the kernel of a continuous homomorphism that
kills them. -/
theorem topologicalClosure_normalClosure_le_ker {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [T1Space H] {s : Set G}
    {f : G →ₜ* H} (hf : ∀ r ∈ s, f r = 1) :
    (Subgroup.normalClosure s).topologicalClosure ≤ f.toMonoidHom.ker := by
  exact Subgroup.topologicalClosure_minimal (Subgroup.normalClosure s)
    (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hf r hr))
    (isClosed_singleton.preimage f.continuous)

end TauCeti

namespace Subgroup

/-- Converting a subgroup to an additive subgroup commutes with topological closure. -/
@[simp]
theorem toAddSubgroup_topologicalClosure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) :
    S.topologicalClosure.toAddSubgroup = S.toAddSubgroup.topologicalClosure :=
  -- `Additive G` inherits the topology of `G`, and both subgroup closures use the
  -- set-theoretic closure of the same carrier. The definitional reduction is confined
  -- to this bridge so consumers can rewrite without unfolding these representations.
  (rfl)

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism maps the topological closure of a subgroup into the topological
closure of its image. -/
theorem _root_.MonoidHom.map_topologicalClosure_le (f : G →* H) (hf : Continuous f)
    (S : Subgroup G) : S.topologicalClosure.map f ≤ (S.map f).topologicalClosure := by
  rw [← SetLike.coe_subset_coe, coe_map, topologicalClosure_coe, topologicalClosure_coe, coe_map]
  exact image_closure_subset_closure_image hf

open scoped commutatorElement in
/-- A closed subgroup containing the commutators `⁅A, B⁆` contains the commutators
`⁅A, B.topologicalClosure⁆`. -/
theorem commutator_topologicalClosure_right_le {A B N : Subgroup G} (hN : IsClosed (N : Set G))
    (h : ⁅A, B⁆ ≤ N) : ⁅A, B.topologicalClosure⁆ ≤ N := by
  rw [commutator_le] at h ⊢
  intro a ha b hb
  have hcont : Continuous fun y : G ↦ ⁅a, y⁆ := by
    simp only [commutatorElement_def]
    fun_prop
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hb
  exact closure_minimal (fun y hy ↦ h a ha y hy) (hN.preimage hcont) hb

end Subgroup
