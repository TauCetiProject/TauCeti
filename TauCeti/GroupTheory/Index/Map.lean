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

For an arbitrary homomorphism `f : G → G'` and a subgroup `H ≤ G`, the index of `f(H)` is
related to the index of `H`, the index of the image of `f` and the two kernels:

`[G' : f(G)] · [G : H] · #(H ⊓ ker f) = [G' : f(H)] · #ker f`.

When all these numbers are finite, this says that the cokernel/kernel ratio
`[G' : f(G)] / #ker f` of `f` is the ratio `[G' : f(H)] / #(H ⊓ ker f)` of its restriction to
`H`, divided by `[G : H]`. This is how such a ratio is computed on subgroups of finite index,
for instance the local factor `[E₂(K) : φ E₁(K)] / #E₁(K)[φ]` of an isogeny `φ` over a local field
`K`, which is computed on deep levels of the formal groups.

## Main results

* `Subgroup.index_map_mul_relIndex_ker`: the image-index factorization for groups.
* `AddSubgroup.index_map_mul_relIndex_ker`: the same factorization for additive groups.
* `MonoidHom.index_range_mul_index_mul_card_inf_ker` and its additive form
  `AddMonoidHom.index_range_mul_index_mul_card_inf_ker`: the identity displayed above.

For a subgroup `H` and a surjective homomorphism `f` with proof `hf`, use
`H.index_map_mul_relIndex_ker f hf`. The same dot notation works for additive subgroups.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- The index of a subgroup under a surjection factors into the image index and the
relative index in the kernel. Infinite indices have the usual value zero. -/
@[to_additive index_map_mul_relIndex_ker
  /-- The index of an additive subgroup under a surjection factors into the image index and the
  relative index in the kernel. Infinite indices have the usual value zero. -/]
theorem index_map_mul_relIndex_ker (H : Subgroup G) (f : G →* G')
    (hf : Function.Surjective f) :
    (H.map f).index * H.relIndex f.ker = H.index := by
  rw [_root_.Subgroup.index_map, f.range_eq_top_of_surjective hf,
    _root_.Subgroup.index_top, mul_one,
    ← _root_.Subgroup.relIndex_sup_of_le_normalizer
      (H := H) (N := f.ker) _root_.Subgroup.le_normalizer_of_normal, mul_comm]
  exact _root_.Subgroup.relIndex_mul_index (H := H) (K := H ⊔ f.ker) le_sup_left

end Subgroup

namespace MonoidHom

variable {G G' : Type*} [Group G] [Group G']

/-- **The index of the image of a subgroup**: for a homomorphism `f : G →* G'` and a subgroup
`H` of `G`,

`[G' : f(G)] · [G : H] · #(H ⊓ ker f) = [G' : f(H)] · #ker f`.

No finiteness is required: infinite orders and indices are read as `0`. When all of them are
finite, this says that the cokernel/kernel ratio of `f` is that of its restriction to `H`, divided
by `[G : H]`. -/
@[to_additive AddMonoidHom.index_range_mul_index_mul_card_inf_ker
  /-- **The index of the image of a subgroup**: for a homomorphism `f : G →+ G'` and a subgroup
  `H` of `G`,

  `[G' : f(G)] · [G : H] · #(H ⊓ ker f) = [G' : f(H)] · #ker f`.

  No finiteness is required: infinite orders and indices are read as `0`. When all of them are
  finite, this says that the cokernel/kernel ratio of `f` is that of its restriction to `H`, divided
  by `[G : H]`. -/]
theorem index_range_mul_index_mul_card_inf_ker (f : G →* G') (H : Subgroup G) :
    f.range.index * H.index * Nat.card ↥(H ⊓ f.ker) = (H.map f).index * Nat.card f.ker := by
  -- `[G : H] = [H ⊔ ker f : H] · [G : H ⊔ ker f]` and `[H ⊔ ker f : H] = [ker f : H ⊓ ker f]`
  rw [H.index_map f, ← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ f.ker),
    Subgroup.relIndex_sup_of_le_normalizer Subgroup.le_normalizer_of_normal,
    ← Subgroup.relIndex_mul_card (H := H) (K := f.ker)]
  ac_rfl

end MonoidHom
