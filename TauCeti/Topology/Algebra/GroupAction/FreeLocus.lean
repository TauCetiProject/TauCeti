/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The free locus of a properly discontinuous group action

For a group acting on a space, the free locus consists of the points with trivial stabilizer.
It is naturally an invariant subspace. If the action is properly discontinuous on a locally
compact Hausdorff space, this subspace is open: a sufficiently small neighbourhood of a free
point meets none of its nontrivial translates.

On the free locus, the orbit projection is a quotient covering map. In particular it is both a
covering map and a local homeomorphism. This separates the unramified part of a quotient from
points with nontrivial stabilizer, where the full orbit projection need not be a covering map.
-/

public section

namespace TauCeti

open Topology

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

/-- The invariant subspace of points whose stabilizer is trivial. -/
def freeLocus : SubMulAction G X where
  carrier := {x | MulAction.stabilizer G x = ⊥}
  smul_mem' g x hx := by
    have hx' : MulAction.stabilizer G x = ⊥ := hx
    exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g x).trans
      (by rw [hx', Subgroup.map_bot])

@[simp]
theorem mem_freeLocus {x : X} : x ∈ freeLocus G X ↔ MulAction.stabilizer G x = ⊥ :=
  Iff.rfl

/-- The action restricted to the free locus is free. -/
instance freeLocus.instIsCancelSMul : IsCancelSMul G (freeLocus G X) := by
  rw [isCancelSMul_iff_stabilizer_eq_bot]
  intro x
  rw [SubMulAction.stabilizer_of_subMul, x.property]

/-- The action on the free locus is continuous in the point when the ambient action is. -/
instance freeLocus.instContinuousConstSMul [TopologicalSpace X] [ContinuousConstSMul G X] :
    ContinuousConstSMul G (freeLocus G X) :=
  Topology.IsInducing.subtypeVal.continuousConstSMul id rfl

section Topology

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]

/-- The free locus of a properly discontinuous action on a locally compact Hausdorff space is
open. -/
theorem isOpen_freeLocus : IsOpen (freeLocus G X : Set X) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hdisjoint⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  filter_upwards [hU] with y hy
  refine (mem_freeLocus G X).mpr (Subgroup.eq_bot_iff_forall _ |>.mpr fun g hg ↦ ?_)
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [← Subgroup.mem_bot, ← (mem_freeLocus (G := G) (X := X)).mp hx,
    MulAction.mem_stabilizer_iff]
  exact hdisjoint g ⟨y, ⟨y, hy, hg⟩, hy⟩

/-- On the free locus of a properly discontinuous action, the ordinary orbit projection is a
quotient covering map. -/
theorem isQuotientCoveringMap_quotientMk_freeLocus :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel G (freeLocus G X))) G := by
  let _ : ProperlyDiscontinuousSMul G (freeLocus G X) :=
    SubMulAction.properlyDiscontinuousSMul (freeLocus G X)
  let _ : LocallyCompactSpace (freeLocus G X) := (isOpen_freeLocus G X).locallyCompactSpace
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The orbit projection from the free locus of a properly discontinuous action is a covering
map. -/
theorem isCoveringMap_quotientMk_freeLocus :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel G (freeLocus G X))) :=
  (isQuotientCoveringMap_quotientMk_freeLocus G X).isCoveringMap

/-- The orbit projection from the free locus of a properly discontinuous action is a local
homeomorphism. -/
theorem isLocalHomeomorph_quotientMk_freeLocus :
    IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel G (freeLocus G X))) :=
  (isCoveringMap_quotientMk_freeLocus G X).isLocalHomeomorph

end Topology

end TauCeti
