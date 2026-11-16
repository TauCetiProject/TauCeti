/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation

/-!
# The fixed tangent subspace of a group action

Let a group `K` act on a manifold `M`. At a point `p` of `M`, the tangent vectors fixed by the
differential at `p` of every element of the stabilizer of `p` form a subspace

`V_p = {v ∈ T_p M | d(k •)_p v = v for every k ∈ stabilizer K p}`

(`TauCeti.fixedTangentSubspace I K p`) of `T_p M`. It is the space of invariant vectors of the
tangent representation of the stabilizer whenever that representation is defined
(`TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`). At a point of the common
fixed set `M^K` the stabilizer is all of `K`, so `V_p` consists of the vectors fixed by the
differential of every element of `K`.

Grouping the points of `M^K` by the dimension of `V_p` gives the sets
`M^K_d = {p ∈ M^K | dim V_p = d}` (`TauCeti.fixedPointsOfFinrank I K M d`), which partition the
fixed set. No metric, topology on `K` or smoothness of the action is needed for these
definitions; for a group of isometries the sets `M^K_d` are embedded submanifolds
(`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`).

## Main definitions

* `TauCeti.fixedTangentSubspace I K p`: the tangent vectors at `p` fixed by the differential of
  every element of the stabilizer of `p`.
* `TauCeti.fixedPointsOfFinrank I K M d`: the points of `M^K` at which this subspace has dimension
  `d`.

## Main results

* `TauCeti.mem_fixedTangentSubspace_iff_of_mem_fixedPoints`: at a point of the fixed set, the
  fixed tangent subspace consists of the vectors fixed by the differential of every element of `K`.
* `TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`: it is the space of invariant
  vectors of the tangent representation.
* `TauCeti.iUnion_fixedPointsOfFinrank`, `TauCeti.pairwise_disjoint_fixedPointsOfFinrank`: the
  sets `M^K_d` partition the fixed set.
-/

public section

open Set MulAction
open scoped Manifold

noncomputable section

namespace TauCeti

section FixedTangentSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (K : Type*) [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]

variable (I) in
/-- The tangent vectors at `p` fixed by the differential at `p` of the action of every element
of the stabilizer of `p`; these are the invariant vectors of the tangent representation
(`TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`). At a point of the fixed set
`M^K` the stabilizer is all of `K` (`TauCeti.mem_fixedTangentSubspace_iff_of_mem_fixedPoints`). -/
def fixedTangentSubspace (p : M) : Submodule ℝ (TangentSpace I p) where
  carrier := {v | ∀ k ∈ stabilizer K p, mfderiv I I (k • ·) p v = v}
  -- The differentials land in `T_(k • p) M`, which like `T_p M` is the model space `E`; `rfl`
  -- identifies the two copies of the remaining operation.
  add_mem' hv hw k hk := by
    simp only [map_add, hv k hk, hw k hk]
    rfl
  zero_mem' k _ := by
    simp only [map_zero]
    rfl
  smul_mem' c v hv k hk := by
    simp only [map_smul, hv k hk]
    rfl

variable {K} in
@[simp]
theorem mem_fixedTangentSubspace {p : M} {v : TangentSpace I p} :
    v ∈ fixedTangentSubspace I K p ↔ ∀ k ∈ stabilizer K p, mfderiv I I (k • ·) p v = v :=
  Iff.rfl

variable {K} in
/-- At a point of the fixed set, the stabilizer is all of `K`, so the fixed tangent subspace
consists of the tangent vectors fixed by the differential of every element of `K`. -/
theorem mem_fixedTangentSubspace_iff_of_mem_fixedPoints {p : M} (hp : p ∈ MulAction.fixedPoints K M)
    {v : TangentSpace I p} :
    v ∈ fixedTangentSubspace I K p ↔ ∀ k : K, mfderiv I I (k • ·) p v = v :=
  ⟨fun h k ↦ h k (hp k), fun h k _ ↦ h k⟩

variable {K} in
/-- The fixed tangent subspace is the space of invariant vectors of the tangent representation of
the stabilizer. -/
theorem invariants_tangentRepresentation_eq_fixedTangentSubspace {p : M}
    (hd : ∀ g ∈ stabilizer K p, MDifferentiableAt I I (fun y : M ↦ g • y) p) :
    (tangentRepresentation hd).toRepresentation.invariants = fixedTangentSubspace I K p :=
  Submodule.ext fun _ ↦ mem_invariants_tangentRepresentation_iff hd

variable (I M) in
/-- The points of the fixed set `M^K` at which the tangent vectors fixed by the differentials of
all elements of `K` form a space of dimension `d`. -/
def fixedPointsOfFinrank (d : ℕ) : Set M :=
  {p | p ∈ MulAction.fixedPoints K M ∧ Module.finrank ℝ (fixedTangentSubspace I K p) = d}

variable {K} in
@[simp]
theorem mem_fixedPointsOfFinrank {d : ℕ} {p : M} :
    p ∈ fixedPointsOfFinrank I K M d ↔
      p ∈ MulAction.fixedPoints K M ∧ Module.finrank ℝ (fixedTangentSubspace I K p) = d :=
  Iff.rfl

variable {K} in
/-- Each part of the fixed set of a given dimension lies in the fixed set. -/
theorem fixedPointsOfFinrank_subset_fixedPoints (d : ℕ) :
    fixedPointsOfFinrank I K M d ⊆ MulAction.fixedPoints K M :=
  fun _ hp ↦ hp.1

variable (I M) in
/-- The fixed set is the union of its parts of each dimension. -/
theorem iUnion_fixedPointsOfFinrank :
    ⋃ d, fixedPointsOfFinrank I K M d = MulAction.fixedPoints K M :=
  Subset.antisymm (iUnion_subset fixedPointsOfFinrank_subset_fixedPoints) fun _ hp ↦
    mem_iUnion.2 ⟨_, hp, rfl⟩

variable (I M) in
/-- The parts of the fixed set of different dimensions are disjoint. -/
theorem pairwise_disjoint_fixedPointsOfFinrank :
    Pairwise (Function.onFun Disjoint (fixedPointsOfFinrank I K M)) :=
  fun _ _ hde ↦ disjoint_left.2 fun _ hp hq ↦ hde (hp.2.symm.trans hq.2)

end FixedTangentSubspace

end TauCeti
