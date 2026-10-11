/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Index of the image of a normal subgroup

Under a surjective homomorphism, the index of a normal subgroup factors into the index of its
image and its relative index in the kernel. This counts the contribution lost on passing to a
quotient, for instance the contribution of principal ideles to an idele-class index.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- The index of a normal subgroup under a surjection factors into the image index and the
relative index in the kernel. Infinite indices have the usual value zero. -/
@[to_additive index_map_mul_relIndex_ker /-- The index of a normal additive subgroup under a
surjection factors into the
image index and the relative index in the kernel. Infinite indices have the usual value zero. -/]
theorem index_map_mul_relIndex_ker (H : Subgroup G) [H.Normal] (f : G →* G')
    (hf : Function.Surjective f) :
    (H.map f).index * H.relIndex f.ker = H.index := by
  rw [index_map, f.range_eq_top_of_surjective hf, index_top, mul_one,
    ← relIndex_sup_left f.ker H, mul_comm]
  exact relIndex_mul_index (H := H) (K := H ⊔ f.ker) le_sup_left

end Subgroup
