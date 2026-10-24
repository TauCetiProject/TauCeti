/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.Index.Basic

/-!
# Index of the image of a subgroup

Under a surjective homomorphism, the index of a subgroup factors into the index of its
image and its relative index in the kernel. This counts the contribution lost on passing to a
quotient, for instance the contribution of principal ideles to an idele-class index.

## Main results

* `TauCeti.subgroup_index_map_mul_relIndex_ker`: the image-index factorization for groups.
* `TauCeti.addSubgroup_index_map_mul_relIndex_ker`: the same factorization for additive groups.

For a subgroup `H` and a surjective homomorphism `f` with proof `hf`, use
`TauCeti.subgroup_index_map_mul_relIndex_ker H f hf`. For an additive subgroup and homomorphism,
use `TauCeti.addSubgroup_index_map_mul_relIndex_ker H f hf`.
-/

public section

namespace TauCeti

variable {G G' : Type*} [Group G] [Group G']

/-- The index of a subgroup under a surjection factors into the image index and the
relative index in the kernel. Infinite indices have the usual value zero. -/
@[to_additive TauCeti.addSubgroup_index_map_mul_relIndex_ker
  /-- The index of an additive subgroup under a surjection factors into the image index and the
  relative index in the kernel. Infinite indices have the usual value zero. -/]
theorem subgroup_index_map_mul_relIndex_ker (H : Subgroup G) (f : G →* G')
    (hf : Function.Surjective f) :
    (H.map f).index * H.relIndex f.ker = H.index := by
  rw [_root_.Subgroup.index_map, f.range_eq_top_of_surjective hf,
    _root_.Subgroup.index_top, mul_one,
    ← _root_.Subgroup.relIndex_sup_of_le_normalizer
      (H := H) (N := f.ker) _root_.Subgroup.le_normalizer_of_normal, mul_comm]
  exact _root_.Subgroup.relIndex_mul_index (H := H) (K := H ⊔ f.ker) le_sup_left

end TauCeti
