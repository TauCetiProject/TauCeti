/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Enumerating the elements of a finite subgroup

For a finite subgroup `H` of a group, such as any subgroup of a finite group,
`Subgroup.fintypeOfFinite H` is a `Fintype` structure on the elements of `H`, so that finite sums
and products can be indexed over `H`. Examples are the sum over a subgroup in the relative norm,
and the sums over a subgroup and its cosets in the transfer.

## Main definitions

* `Subgroup.fintypeOfFinite`: the `Fintype` structure `Fintype.ofFinite` on the elements of a
  finite subgroup.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

-- Not a global instance: Mathlib's `Subgroup.instFintypeSubtypeMemOfDecidablePred` asks for
-- decidable membership instead, and the two structures are not definitionally equal. Files about
-- finite subgroups, such as the subgroups of a finite group, install this one with
-- `attribute [local instance]`, so that their statements share one `Fintype` structure.
/-- The `Fintype` structure on a finite subgroup given by `Fintype.ofFinite`. -/
@[instance_reducible, expose]
noncomputable def fintypeOfFinite (H : Subgroup G) [Finite H] : Fintype H :=
  Fintype.ofFinite H

end Subgroup
