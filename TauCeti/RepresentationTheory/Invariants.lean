/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# Invariants of group representations

Mathlib names the group sum `∑ g, ρ g` of a finite-group representation `Representation.norm`,
builds the averaging projection `Representation.averageMap` separately out of the group-algebra
element `GroupAlgebra.average`, and records that the latter projects onto the invariants
(`Representation.isProj_averageMap`). What it does not record is how the two operators relate.
The group sum is the shape a symmetrization operator actually takes at a use site, where the
normalizing factor `⅟(#G)` is usually left implicit, and reinstating it by hand is the step that
gets rewritten.

This file supplies the bridge. Unfolding the group algebra once identifies `averageMap` with
`norm` scaled by `⅟(#G)`, and since scaling by a unit changes no image, `norm` has the same range
as the projection: the invariants.

The file also records the companion description of the invariants available when `G` is cyclic.
Invariance is a condition on every group element, but a vector fixed by a generator is fixed by all
of its powers, so testing a single generator `g` suffices and the invariants are cut out by the one
linear map `ρ(g) - 1`. Mathlib states this elementwise, in
`Representation.mem_invariants_iff_of_forall_mem_zpowers`; the submodule-level equality with
`ker (ρ(g) - 1)` is the form used to present the (co)homology of a finite cyclic group as a
subquotient of `M`, where each group is the homology of `ρ(g) - 1` and the norm in one order or
the other.

## Main results

* `Representation.averageMap_eq_invOf_card_smul_norm`: the averaging projection is the group sum
  `Representation.norm` scaled by the inverse of the group order.
* `Representation.range_norm_eq_invariants`: the group sum `Representation.norm ρ` has the
  invariants as its range.
* `Rep.FiniteCyclicGroup.invariants_eq_ker_apply_sub`: for a cyclic group, the invariants are the
  kernel of the action of a generator minus the identity.
-/
public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]

/-- **The averaging projection is the normalized group sum.** Mathlib defines
`Representation.averageMap` through the group algebra; this unfolds that definition to the group sum
`Representation.norm`, scaled by the inverse of the group order. -/
theorem averageMap_eq_invOf_card_smul_norm :
    ρ.averageMap = ⅟(Fintype.card G : k) • ρ.norm := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, norm]

/-- **The group sum has the invariants as its range.** When `#G` is invertible in `k`, the operator
`Representation.norm ρ = ∑ g, ρ g` maps onto the invariants of `ρ`: it agrees with the averaging
projection up to the unit `#G`, so the two have the same image. -/
@[simp]
theorem range_norm_eq_invariants : LinearMap.range ρ.norm = ρ.invariants := by
  rw [← ρ.isProj_averageMap.range, averageMap_eq_invOf_card_smul_norm]
  refine le_antisymm ?_ (LinearMap.range_smul_le_range _ _)
  convert LinearMap.range_smul_le_range (⅟(Fintype.card G : k) • ρ.norm) (Fintype.card G : k)
  rw [smul_smul, mul_invOf_self, one_smul]

end Representation

namespace Rep.FiniteCyclicGroup

variable {R G : Type*} [CommRing R] [Group G] (M : Rep R G) (g : G)

/-- If `g` generates `G`, the invariants of a representation are the kernel of `ρ(g) - 1`. -/
theorem invariants_eq_ker_apply_sub (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    M.ρ.invariants = LinearMap.ker (M.ρ g - LinearMap.id) := by
  ext x
  simpa [sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x

end Rep.FiniteCyclicGroup
