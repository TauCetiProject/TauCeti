/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Subgroups and topological closure

This file records how subgroup constructions interact with topological closure. It also provides
normality of the closure of a normal subgroup, the kernel criterion for a closed normal closure,
and compatibility of multiplicative and additive subgroup closures.

## Main results

* `TauCeti.instNormal_topologicalClosure_normalClosure`: the closure of a normal closure is
  normal.
* `TauCeti.topologicalClosure_normalClosure_le_ker`: relators killed by a continuous map have
  closed normal closure in its kernel.
* `Subgroup.toAddSubgroup_topologicalClosure`: converting to an additive subgroup commutes with
  topological closure.
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

end Subgroup
