/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Torsion
import TauCeti.GroupTheory.PGroup

/-!
# Basic properties of primary components of commutative groups

This file records foundational properties of Mathlib's `CommGroup.primaryComponent G n` and
`AddCommGroup.primaryComponent A n`, the subgroup of elements annihilated by a power of `n`:

* Functoriality under homomorphisms and isomorphisms (`MonoidHom.map_primaryComponent_le`,
  `MulEquiv.map_primaryComponent`, `MulEquiv.primaryComponent`, and their additive counterparts).
* Compatibility with binary products (`CommGroup.primaryComponent_prod`,
  `CommGroup.primaryComponentProdMulEquiv`, and their additive counterparts).
* Identification of the `n`-primary component of an `n`-group with the whole group
  (`IsPGroup.primaryComponentEquiv` and its additive counterpart).
* Every `n`-primary component is an `n`-group (`AddCommGroup.primaryComponent.isAddPGroup`), and
  the `p`-primary component of a `q`-group is trivial whenever `p` and `q` are coprime
  (`CommGroup.primaryComponent.subsingleton_of_isPGroup_of_coprime` and its additive counterpart).

## Main definitions and statements

* `MulEquiv.primaryComponent`, `AddEquiv.primaryComponent`
* `CommGroup.primaryComponentProdMulEquiv`, `AddCommGroup.primaryComponentProdAddEquiv`
* `IsPGroup.primaryComponentEquiv`, `IsAddPGroup.primaryComponentEquiv`
* `AddCommGroup.primaryComponent.isAddPGroup`
* `CommGroup.primaryComponent.subsingleton_of_isPGroup_of_coprime`,
  `AddCommGroup.primaryComponent.subsingleton_of_isAddPGroup_of_coprime`
-/

public section

/-- A group homomorphism maps `CommGroup.primaryComponent G n` into
`CommGroup.primaryComponent H n`. -/
@[to_additive /-- An additive group homomorphism maps `AddCommGroup.primaryComponent G n` into
`AddCommGroup.primaryComponent H n`. -/]
theorem MonoidHom.map_primaryComponent_le {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (n : ℕ) :
    (CommGroup.primaryComponent G n).map f ≤ CommGroup.primaryComponent H n := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp hx
  exact CommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_pow, hk, map_one]⟩

/-- A group isomorphism maps the `n`-primary component onto the `n`-primary component. -/
@[to_additive /-- An additive group isomorphism maps the `n`-primary component onto the
`n`-primary component. -/]
theorem MulEquiv.map_primaryComponent {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (CommGroup.primaryComponent G n).map (e : G →* H) = CommGroup.primaryComponent H n := by
  refine le_antisymm (MonoidHom.map_primaryComponent_le (e : G →* H) n) fun y hy ↦ ?_
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact MonoidHom.map_primaryComponent_le (e.symm : H →* G) n ⟨y, hy, rfl⟩

/-- A group isomorphism restricts to an isomorphism between `n`-primary components. -/
@[to_additive /-- An additive group isomorphism restricts to an isomorphism between `n`-primary
components. -/]
def MulEquiv.primaryComponent {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    CommGroup.primaryComponent G n ≃* CommGroup.primaryComponent H n :=
  (e.subgroupMap (CommGroup.primaryComponent G n)).trans
    (MulEquiv.subgroupCongr (e.map_primaryComponent n))

/-- Applying `MulEquiv.primaryComponent e n` agrees with `e` on the underlying elements. -/
@[to_additive (attr := simp)
  /-- Applying `AddEquiv.primaryComponent e n` agrees with `e` on the underlying elements. -/]
theorem MulEquiv.coe_primaryComponent_apply {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) (x : CommGroup.primaryComponent G n) :
    (e.primaryComponent n x : H) = e x := by
  simp [MulEquiv.primaryComponent]

/-- Applying `(MulEquiv.primaryComponent e n).symm` agrees with `e.symm` on the underlying
elements. -/
@[to_additive (attr := simp)
  /-- Applying `(AddEquiv.primaryComponent e n).symm` agrees with `e.symm` on the underlying
  elements. -/]
theorem MulEquiv.coe_primaryComponent_symm_apply {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) (y : CommGroup.primaryComponent H n) :
    ((e.primaryComponent n).symm y : G) = e.symm y := by
  simp [MulEquiv.primaryComponent]

/-- The `n`-primary component of an `n`-group is isomorphic to the group itself. -/
@[to_additive /-- The `n`-primary component of an additive `n`-group is isomorphic to the group
itself. -/]
def IsPGroup.primaryComponentEquiv {G : Type*} [CommGroup G] {n : ℕ}
    (hG : IsPGroup n G) :
    CommGroup.primaryComponent G n ≃* G :=
  (MulEquiv.subgroupCongr ((Subgroup.eq_top_iff' (CommGroup.primaryComponent G n)).mpr hG)).trans
    Subgroup.topEquiv

/-- `IsPGroup.primaryComponentEquiv` acts as the subtype coercion. -/
@[to_additive (attr := simp)
  /-- `IsAddPGroup.primaryComponentEquiv` acts as the subtype coercion. -/]
theorem IsPGroup.primaryComponentEquiv_apply {G : Type*} [CommGroup G] {n : ℕ}
    (hG : IsPGroup n G) (x : CommGroup.primaryComponent G n) :
    hG.primaryComponentEquiv x = x := by
  simp [IsPGroup.primaryComponentEquiv]

/-- The inverse of `IsPGroup.primaryComponentEquiv` preserves the underlying element. -/
@[to_additive (attr := simp)
  /-- The inverse of `IsAddPGroup.primaryComponentEquiv` preserves the underlying element. -/]
theorem IsPGroup.coe_primaryComponentEquiv_symm_apply {G : Type*} [CommGroup G] {n : ℕ}
    (hG : IsPGroup n G) (x : G) :
    (hG.primaryComponentEquiv.symm x : G) = x := by
  simp [IsPGroup.primaryComponentEquiv]

namespace CommGroup

/-- The `n`-primary component of a binary product of commutative groups is the product of their
`n`-primary components. -/
@[to_additive primaryComponent_prod
  /-- The `n`-primary component of a binary product of additive commutative groups is the product of
  their `n`-primary components. -/]
theorem primaryComponent_prod (G H : Type*) [CommGroup G] [CommGroup H] (n : ℕ) :
    CommGroup.primaryComponent (G × H) n =
      (CommGroup.primaryComponent G n).prod (CommGroup.primaryComponent H n) := by
  ext ⟨x, y⟩
  simp only [CommGroup.mem_primaryComponent, Subgroup.mem_prod, Prod.pow_mk, Prod.mk_eq_one]
  constructor
  · rintro ⟨k, hx, hy⟩
    exact ⟨⟨k, hx⟩, ⟨k, hy⟩⟩
  · rintro ⟨⟨k₁, hx⟩, ⟨k₂, hy⟩⟩
    refine ⟨k₁ + k₂, ?_, ?_⟩
    · rw [pow_add, pow_mul, hx, one_pow]
    · rw [add_comm, pow_add, pow_mul, hy, one_pow]

/-- The `n`-primary component of a binary product of commutative groups splits as the product of
their `n`-primary components. -/
@[to_additive primaryComponentProdAddEquiv
  /-- The `n`-primary component of a binary product of additive commutative groups splits as the
  product of their `n`-primary components. -/]
def primaryComponentProdMulEquiv (G H : Type*) [CommGroup G] [CommGroup H] (n : ℕ) :
    CommGroup.primaryComponent (G × H) n ≃*
      CommGroup.primaryComponent G n × CommGroup.primaryComponent H n :=
  (MulEquiv.subgroupCongr (primaryComponent_prod G H n)).trans (Subgroup.prodEquiv _ _)

/-- The first component of `CommGroup.primaryComponentProdMulEquiv` preserves the underlying first
coordinate. -/
@[to_additive (attr := simp) coe_primaryComponentProdAddEquiv_apply_fst
  /-- The first component of `AddCommGroup.primaryComponentProdAddEquiv` preserves the underlying
  first coordinate. -/]
theorem coe_primaryComponentProdMulEquiv_apply_fst (G H : Type*) [CommGroup G] [CommGroup H]
    (n : ℕ) (x : CommGroup.primaryComponent (G × H) n) :
    ((primaryComponentProdMulEquiv G H n x).1 : G) = x.val.1 := by
  rw [primaryComponentProdMulEquiv, MulEquiv.trans_apply]
  exact congrArg Prod.fst (MulEquiv.subgroupCongr_apply (primaryComponent_prod G H n) x)

/-- The second component of `CommGroup.primaryComponentProdMulEquiv` preserves the underlying
second coordinate. -/
@[to_additive (attr := simp) coe_primaryComponentProdAddEquiv_apply_snd
  /-- The second component of `AddCommGroup.primaryComponentProdAddEquiv` preserves the underlying
  second coordinate. -/]
theorem coe_primaryComponentProdMulEquiv_apply_snd (G H : Type*) [CommGroup G] [CommGroup H]
    (n : ℕ) (x : CommGroup.primaryComponent (G × H) n) :
    ((primaryComponentProdMulEquiv G H n x).2 : H) = x.val.2 := by
  rw [primaryComponentProdMulEquiv, MulEquiv.trans_apply]
  exact congrArg Prod.snd (MulEquiv.subgroupCongr_apply (primaryComponent_prod G H n) x)

/-- The inverse of `CommGroup.primaryComponentProdMulEquiv` preserves underlying coordinates. -/
@[to_additive (attr := simp) coe_primaryComponentProdAddEquiv_symm_apply
  /-- The inverse of `AddCommGroup.primaryComponentProdAddEquiv` preserves underlying
  coordinates. -/]
theorem coe_primaryComponentProdMulEquiv_symm_apply (G H : Type*) [CommGroup G] [CommGroup H]
    (n : ℕ) (x : CommGroup.primaryComponent G n) (y : CommGroup.primaryComponent H n) :
    ((primaryComponentProdMulEquiv G H n).symm (x, y) : G × H) = (x.val, y.val) := by
  rw [primaryComponentProdMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply]
  rfl

end CommGroup

namespace AddCommGroup

/-- Every element of `AddCommGroup.primaryComponent A n` is annihilated by a power of `n`. -/
theorem primaryComponent.isAddPGroup (A : Type*) [AddCommGroup A] (n : ℕ) :
    IsAddPGroup n (AddCommGroup.primaryComponent A n) := by
  intro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  exact ⟨k, Subtype.ext hk⟩

/-- If `G` is an additive `q`-group and `p` is coprime to `q`, then the `p`-primary component of
`G` is trivial. -/
theorem primaryComponent.subsingleton_of_isAddPGroup_of_coprime {G : Type*} [AddCommGroup G]
    {p q : ℕ} (hG : IsAddPGroup q G) (hpq : p.Coprime q) :
    Subsingleton (AddCommGroup.primaryComponent G p) :=
  (primaryComponent.isAddPGroup G p).subsingleton_of_coprime (hG.to_addSubgroup _) hpq

end AddCommGroup

namespace CommGroup

/-- If `G` is a `q`-group and `p` is coprime to `q`, then the `p`-primary component of `G` is
trivial. -/
@[to_additive existing]
theorem primaryComponent.subsingleton_of_isPGroup_of_coprime {G : Type*} [CommGroup G]
    {p q : ℕ} (hG : IsPGroup q G) (hpq : p.Coprime q) :
    Subsingleton (CommGroup.primaryComponent G p) :=
  (CommGroup.primaryComponent.isPGroup (G := G) (p := p)).subsingleton_of_coprime
    (hG.to_subgroup _) hpq

end CommGroup
