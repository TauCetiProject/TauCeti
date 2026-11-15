/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Separating points of open subspaces of `T₁` type

Let `j : X → Y` be an open embedding of a `T₁` space `X`. Then every point `j x` of the open
subspace is separated from every other point `q` of `Y` by an open set containing `j x` and not `q`
(`Topology.IsOpenEmbedding.exists_isOpen_mem_notMem`): the image of `X ∖ {j⁻¹ q}` when `q` lies in
the subspace, and the subspace itself otherwise. `Y` need not be `T₁`, but a space covered by open
subspaces of this kind is `T₁` by `t1Space_iff_exists_open`; this is how the connected sum of two
`T₁` spaces is shown to be `T₁`.
-/

public section

open Set

namespace Topology.IsOpenEmbedding

/-- A point of an open subspace given by an open embedding of a `T₁` space is separated from
every other point of the space by an open set. -/
theorem exists_isOpen_mem_notMem {X Y : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace Y] {j : X → Y} (hj : IsOpenEmbedding j) {x : X} {q : Y} (hq : q ≠ j x) :
    ∃ U : Set Y, IsOpen U ∧ j x ∈ U ∧ q ∉ U := by
  by_cases hqr : q ∈ range j
  · obtain ⟨y, rfl⟩ := hqr
    exact ⟨j '' {y}ᶜ, hj.isOpenMap _ isOpen_compl_singleton,
      mem_image_of_mem _ (mem_compl_singleton_iff.2 fun h ↦ hq (h ▸ rfl)),
      fun ⟨y', hy', hyy'⟩ ↦ hy' (hj.injective hyy')⟩
  · exact ⟨range j, hj.isOpen_range, mem_range_self x, hqr⟩

end Topology.IsOpenEmbedding
