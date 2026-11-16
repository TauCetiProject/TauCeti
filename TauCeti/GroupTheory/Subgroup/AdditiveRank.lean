/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The rank over `ℤ` of subgroups of a commutative group

For a commutative group `G`, `Module.rank ℤ (Additive G)` is the torsion-free rank of `G`: the
supremum of the cardinalities of multiplicatively independent families in `G`. It is the rank in
which finite-rank multiplicative groups are measured, for instance in unit equations, where groups
need not be finitely generated.

This file proves that this rank does not increase under surjective homomorphisms or under taking
images of subgroups, that it is subadditive on joins of subgroups, and that a cyclic subgroup has
rank at most one. Consequently, adjoining one element to a subgroup raises its rank by at most one.

## Main statements

* `MonoidHom.rank_additive_le_of_surjective`: the codomain of a surjective homomorphism has rank at
  most that of the domain.
* `Subgroup.rank_additive_map_le`: the image of a subgroup has rank at most that of the subgroup.
* `Subgroup.rank_additive_sup_le`: `rank (H ⊔ K) ≤ rank H + rank K`.
* `Subgroup.rank_additive_zpowers_le_one`: `rank (zpowers g) ≤ 1`.
-/

public section

universe u

variable {G N : Type u} [CommGroup G] [CommGroup N]

namespace MonoidHom

/-- The target of a surjective homomorphism of commutative groups has rank over `ℤ` at most
that of its source. -/
theorem rank_additive_le_of_surjective (f : G →* N) (hf : Function.Surjective f) :
    Module.rank ℤ (Additive N) ≤ Module.rank ℤ (Additive G) :=
  f.toAdditive.toIntLinearMap.rank_le_of_surjective hf

end MonoidHom

namespace Subgroup

/-- The image of a subgroup under a homomorphism of commutative groups has rank over `ℤ` at most
that of the subgroup. -/
theorem rank_additive_map_le (H : Subgroup G) (f : G →* N) :
    Module.rank ℤ (Additive (H.map f)) ≤ Module.rank ℤ (Additive H) :=
  (f.subgroupMap H).rank_additive_le_of_surjective (f.subgroupMap_surjective H)

/-- The rank over `ℤ` is subadditive on joins of subgroups of a commutative group. -/
theorem rank_additive_sup_le (H K : Subgroup G) :
    Module.rank ℤ (Additive ↥(H ⊔ K)) ≤
      Module.rank ℤ (Additive H) + Module.rank ℤ (Additive K) := by
  let f : H × K →* ↥(H ⊔ K) := (inclusion le_sup_left).coprod (inclusion le_sup_right)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, z, rfl⟩ := mem_sup'.mp hx
    exact ⟨(y, z), rfl⟩
  calc Module.rank ℤ (Additive ↥(H ⊔ K)) ≤ Module.rank ℤ (Additive (H × K)) :=
        f.rank_additive_le_of_surjective hf
    _ = Module.rank ℤ (Additive H) + Module.rank ℤ (Additive K) := by
        rw [(AddEquiv.prodAdditive (G := H) (H := K)).toIntLinearEquiv.rank_eq,
          LinearMap.rank_eq_of_surjective (LinearMap.snd_surjective (R := ℤ)), LinearMap.ker_snd,
          rank_range_of_injective _ LinearMap.inl_injective, add_comm]

/-- A cyclic subgroup of a commutative group has rank at most one over `ℤ`. -/
theorem rank_additive_zpowers_le_one (g : G) : Module.rank ℤ (Additive (zpowers g)) ≤ 1 := by
  let f := LinearMap.toSpanSingleton ℤ (Additive (zpowers g)) (Additive.ofMul ⟨g, mem_zpowers g⟩)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.toMul.2
    refine ⟨k, Additive.toMul.injective (Subtype.ext ?_)⟩
    simp [f, hk]
  simpa using f.lift_rank_le_of_surjective hf

end Subgroup
