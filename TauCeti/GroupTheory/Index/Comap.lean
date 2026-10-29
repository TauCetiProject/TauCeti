/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# The index of a preimage

The preimage of a subgroup `H ≤ G` under a homomorphism `f : G' →* G` has index the relative index
of `H` in the range of `f` (Mathlib's `Subgroup.index_comap`). So it never exceeds the index of
`H` when that is finite (`Subgroup.index_comap_le`), and it is strictly smaller when the range of
`f` lies in a proper subgroup containing `H`, being then at most the relative index of `H` in that
subgroup (`Subgroup.index_comap_lt_of_range_le`).

## Main results

* `Subgroup.index_comap_le`: a preimage of a subgroup of finite index has at most its index.
* `Subgroup.index_comap_lt_of_range_le`: if the range lies in a proper subgroup containing `H`,
  the preimage of `H` has smaller index.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) {K : Subgroup G} (f : G' →* G)

/-- The preimage of a subgroup of finite index under a homomorphism has at most its index. -/
@[to_additive /-- The preimage of a subgroup of finite index under a homomorphism has at most its
index. -/]
theorem index_comap_le [H.FiniteIndex] : (H.comap f).index ≤ H.index := by
  rw [index_comap, ← relIndex_top_right]
  exact relIndex_le_of_le_right le_top (by rw [relIndex_top_right]; exact FiniteIndex.index_ne_zero)

/-- If the range of `f` lies in a proper subgroup `K` containing a subgroup `H` of finite index,
then the preimage of `H` has smaller index than `H`: its index is at most `[K : H]`. -/
@[to_additive /-- If the range of `f` lies in a proper subgroup `K` containing a subgroup `H` of
finite index, then the preimage of `H` has smaller index than `H`: its index is at most
`[K : H]`. -/]
theorem index_comap_lt_of_range_le [H.FiniteIndex] (hHK : H ≤ K) (hK : K ≠ ⊤) (hf : f.range ≤ K) :
    (H.comap f).index < H.index := by
  have hmul := relIndex_mul_index hHK
  have hrel : H.relIndex K ≠ 0 := fun h ↦ FiniteIndex.index_ne_zero (by rw [← hmul, h, zero_mul])
  have hK0 : K.index ≠ 0 := fun h ↦ FiniteIndex.index_ne_zero (by rw [← hmul, h, mul_zero])
  have hK1 : K.index ≠ 1 := mt index_eq_one.1 hK
  rw [index_comap]
  calc H.relIndex f.range ≤ H.relIndex K := relIndex_le_of_le_right hf hrel
    _ < H.relIndex K * K.index := lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hrel) (by omega)
    _ = H.index := hmul

end Subgroup
