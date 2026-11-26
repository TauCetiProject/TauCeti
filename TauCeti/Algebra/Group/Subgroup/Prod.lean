/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Lattice and map operations on products of subgroups

For subgroups `H ≤ G` and `K ≤ G'`, the direct product `H.prod K ≤ G × G'` commutes with binary
infima and suprema, and `H₁.prod H₂ = K₁.prod K₂` holds componentwise. Mapping along the factor
inclusions `MonoidHom.inl` and `MonoidHom.inr` produces `H.prod ⊥` and `⊥.prod K`, while pulling
back along the inclusions or pushing forward along `MonoidHom.fst` and `MonoidHom.snd` recovers
the factors. The ranges of the factor inclusions are `⊤.prod ⊥` and `⊥.prod ⊤`, the kernels of the
opposite projections. All statements carry `@[to_additive]` for additive subgroups.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- Mapping a subgroup along the left factor inclusion gives its product with `⊥`. -/
@[to_additive /-- Mapping an additive subgroup along the left factor inclusion gives its product
with `⊥`. -/]
theorem map_inl (H : Subgroup G) : H.map (MonoidHom.inl G G') = H.prod ⊥ :=
  toSubmonoid_injective (Submonoid.map_inl H.toSubmonoid)

/-- Mapping a subgroup along the right factor inclusion gives its product with `⊥`. -/
@[to_additive /-- Mapping an additive subgroup along the right factor inclusion gives its product
with `⊥`. -/]
theorem map_inr (K : Subgroup G') : K.map (MonoidHom.inr G G') = (⊥ : Subgroup G).prod K :=
  toSubmonoid_injective (Submonoid.map_inr K.toSubmonoid)

/-- Pulling back a product subgroup along the left inclusion recovers its first factor. -/
@[to_additive (attr := simp) prod_comap_inl /-- Pulling back a product of additive subgroups along
the left inclusion recovers its first factor. -/]
theorem prod_comap_inl (H : Subgroup G) (K : Subgroup G') :
    (H.prod K).comap (MonoidHom.inl G G') = H := by
  ext x
  simp [mem_prod]

/-- Pulling back a product subgroup along the right inclusion recovers its second factor. -/
@[to_additive (attr := simp) prod_comap_inr /-- Pulling back a product of additive subgroups along
the right inclusion recovers its second factor. -/]
theorem prod_comap_inr (H : Subgroup G) (K : Subgroup G') :
    (H.prod K).comap (MonoidHom.inr G G') = K := by
  ext y
  simp [mem_prod]

/-- Pushing a product subgroup forward along the first projection recovers its first factor. -/
@[to_additive (attr := simp) prod_map_fst /-- Pushing a product of additive subgroups forward along
the first projection recovers its first factor. -/]
theorem prod_map_fst (H : Subgroup G) (K : Subgroup G') :
    (H.prod K).map (MonoidHom.fst G G') = H := by
  ext x
  simp [mem_prod, (⟨1, K.one_mem⟩ : ∃ y, y ∈ K)]

/-- Pushing a product subgroup forward along the second projection recovers its second factor. -/
@[to_additive (attr := simp) prod_map_snd /-- Pushing a product of additive subgroups forward along
the second projection recovers its second factor. -/]
theorem prod_map_snd (H : Subgroup G) (K : Subgroup G') :
    (H.prod K).map (MonoidHom.snd G G') = K := by
  ext y
  simp [mem_prod, (⟨1, H.one_mem⟩ : ∃ x, x ∈ H)]

/-- Two product subgroups are equal if and only if their respective factors are equal. -/
@[to_additive (attr := simp) prod_eq_prod_iff /-- Two products of additive subgroups are equal if
and only if their respective factors are equal. -/]
theorem prod_eq_prod_iff {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup G'} :
    H₁.prod H₂ = K₁.prod K₂ ↔ H₁ = K₁ ∧ H₂ = K₂ := by
  constructor
  · intro h
    exact ⟨by simpa only [prod_comap_inl] using congrArg (comap (MonoidHom.inl G G')) h,
      by simpa only [prod_comap_inr] using congrArg (comap (MonoidHom.inr G G')) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A product subgroup is the whole product group if and only if both factors are `⊤`. -/
@[to_additive (attr := simp) prod_eq_top_iff /-- A product of additive subgroups is `⊤` if and only
if both factors are `⊤`. -/]
theorem prod_eq_top_iff {H : Subgroup G} {K : Subgroup G'} :
    H.prod K = ⊤ ↔ H = ⊤ ∧ K = ⊤ := by
  rw [← top_prod_top, prod_eq_prod_iff]

/-- The intersection of two product subgroups is the product of their intersections. -/
@[to_additive (attr := simp) prod_inf_prod /-- The intersection of two products of additive
subgroups is the product of their intersections. -/]
theorem prod_inf_prod (H₁ K₁ : Subgroup G) (H₂ K₂ : Subgroup G') :
    (H₁.prod H₂) ⊓ (K₁.prod K₂) = (H₁ ⊓ K₁).prod (H₂ ⊓ K₂) := by
  ext x
  simp [mem_prod, and_and_and_comm]

/-- A product subgroup is the join of its two coordinate factors `H.prod ⊥` and `⊥.prod K`. -/
@[to_additive prod_bot_sup_bot_prod /-- A product of additive subgroups is the join of its two
coordinate factors `H.prod ⊥` and `⊥.prod K`. -/]
theorem prod_bot_sup_bot_prod (H : Subgroup G) (K : Subgroup G') :
    (H.prod (⊥ : Subgroup G')) ⊔ ((⊥ : Subgroup G).prod K) = H.prod K := by
  refine le_antisymm (sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl)) fun p hp => ?_
  rw [← Prod.fst_mul_snd p]
  exact mul_mem_sup ⟨hp.1, rfl⟩ ⟨rfl, hp.2⟩

/-- The join of two product subgroups is the product of their joins. -/
@[to_additive (attr := simp) prod_sup_prod /-- The join of two products of additive subgroups is the
product of their joins. -/]
theorem prod_sup_prod (H₁ K₁ : Subgroup G) (H₂ K₂ : Subgroup G') :
    (H₁.prod H₂) ⊔ (K₁.prod K₂) = (H₁ ⊔ K₁).prod (H₂ ⊔ K₂) := by
  rw [← prod_bot_sup_bot_prod H₁ H₂, ← prod_bot_sup_bot_prod K₁ K₂,
    ← prod_bot_sup_bot_prod (H₁ ⊔ K₁) (H₂ ⊔ K₂)]
  simp only [← map_inl, ← map_inr, map_sup]
  ac_rfl

end Subgroup

namespace MonoidHom

variable {G G' : Type*} [Group G] [Group G']

/-- The range of the left factor inclusion is the product subgroup `⊤.prod ⊥`, the kernel of the
second projection (`MonoidHom.ker_snd`). -/
@[to_additive /-- The range of the left factor inclusion is the product of additive subgroups
`⊤.prod ⊥`, the kernel of the second projection (`AddMonoidHom.ker_snd`). -/]
theorem range_inl : (inl G G').range = (⊤ : Subgroup G).prod ⊥ := by
  rw [range_eq_map, Subgroup.map_inl]

/-- The range of the right factor inclusion is the product subgroup `⊥.prod ⊤`, the kernel of the
first projection (`MonoidHom.ker_fst`). -/
@[to_additive /-- The range of the right factor inclusion is the product of additive subgroups
`⊥.prod ⊤`, the kernel of the first projection (`AddMonoidHom.ker_fst`). -/]
theorem range_inr : (inr G G').range = (⊥ : Subgroup G).prod ⊤ := by
  rw [range_eq_map, Subgroup.map_inr]

end MonoidHom
