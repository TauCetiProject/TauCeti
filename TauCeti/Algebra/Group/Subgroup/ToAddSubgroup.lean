/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Subgroups of `Multiplicative A` and the additive subgroups of `A`

A subgroup `H` of `Multiplicative A` corresponds, through `Subgroup.toAddSubgroup'`, to an additive
subgroup of `A` with the same elements. Finiteness and cyclicity transfer along this
correspondence.

## Main results

* `Subgroup.finite_toAddSubgroup'_of_finite`: the additive subgroup of a finite subgroup is finite.
* `Subgroup.isCyclic_of_isAddCyclic_toAddSubgroup'`: a subgroup whose additive subgroup is cyclic
  is cyclic.
-/

public section

namespace Subgroup

variable {A : Type*} [AddGroup A] (H : Subgroup (Multiplicative A))

/-- The additive subgroup of a finite subgroup of `Multiplicative A` is finite. -/
theorem finite_toAddSubgroup'_of_finite [Finite H] : Finite (Subgroup.toAddSubgroup' H) :=
  Finite.of_injective
    (fun a : Subgroup.toAddSubgroup' H ↦ (⟨Multiplicative.ofAdd a.val, a.property⟩ : H))
    fun _ _ h ↦ Subtype.ext (congrArg (fun y : H ↦ y.val.toAdd) h)

/-- A subgroup `H` of `Multiplicative A` is cyclic as soon as the additive subgroup
`Subgroup.toAddSubgroup' H` of `A` is. -/
theorem isCyclic_of_isAddCyclic_toAddSubgroup' [IsAddCyclic (Subgroup.toAddSubgroup' H)] :
    IsCyclic H := by
  let j : H →* Multiplicative (Subgroup.toAddSubgroup' H) := {
    toFun := fun y ↦ Multiplicative.ofAdd ⟨y.val.toAdd, y.property⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }
  exact isCyclic_of_injective j fun y z h ↦ Subtype.ext (Multiplicative.toAdd.injective
    (congrArg (fun t : Multiplicative (Subgroup.toAddSubgroup' H) ↦ (t.toAdd : A)) h))

end Subgroup
