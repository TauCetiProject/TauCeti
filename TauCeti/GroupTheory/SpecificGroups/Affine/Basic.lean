/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.TrivialIntersection
import Mathlib.Tactic.LinearCombination

/-!
# One-dimensional affine groups

For a ring `F`, the one-dimensional affine group is the semidirect product of the additive
group of `F` by its unit group.  We realize the additive group as `Multiplicative F`, so that
Mathlib's multiplicative semidirect product can be used directly.  An element `(b, a)` acts on
`F` by `x ↦ b + a * x`.

This file records the composition and inversion formulas and identifies the translation and
linear-factor subgroups: the translations form the kernel of the linear-part homomorphism
`SemidirectProduct.rightHom`, the linear factor is the stabilizer of `0`, of index `|F|`, and the
two are complementary, all over an arbitrary ring.  Over a commutative ring the commutator of two
affine maps is an explicit translation, and the commutator subgroup is the whole translation
subgroup as soon as some unit `u` has `u - 1` a unit (for instance over a field with at least
three elements).  Over a ring without zero divisors, every nonidentity
linear factor acts without nonidentity fixed points on the translations.  Over a division ring it
also computes the cardinalities of the two factors.  Thus finite affine groups with at least three
elements are Frobenius groups; their Frobenius kernels are identified in
`TauCeti.RepresentationTheory.FrobeniusGroup.Affine`.

## Main definitions and results

* `TauCeti.affineAction`: multiplication by a unit on the additive group of a ring.
* `TauCeti.AffineGroup`: the semidirect product `F ⋊ Fˣ` for this action, acting faithfully on
  `F` by affine maps (`TauCeti.AffineGroup.smul_def`).
* `TauCeti.AffineGroup.map`: the homomorphism of affine groups induced by a ring homomorphism.
* `TauCeti.affineTranslationSubgroup` and `TauCeti.affineLinearSubgroup`: the two canonical
  factors.
* `TauCeti.isComplement'_affineTranslationSubgroup_affineLinearSubgroup`: the two factors are
  complementary.
* `TauCeti.affineTranslationSubgroup_eq_ker_rightHom`, `TauCeti.AffineGroup.stabilizer_zero`:
  the translations are the kernel of the linear part, and the linear factor is the stabilizer
  of `0`.
* `TauCeti.AffineGroup.commutatorElement_eq_inl`, `TauCeti.commutator_affineGroup_eq`: the
  commutator of two affine maps, and the commutator subgroup of the affine group of a field
  with at least three elements.
* `TauCeti.fixedPointFree_conjNormal_affineTranslationSubgroup`: a nonidentity linear factor
  fixes no nonidentity translation.
* `TauCeti.isFrobeniusComplement_affineLinearSubgroup`: for a finite division ring of order at least
  three, the linear factor is a Frobenius complement.

The construction is the standard affine-group example; see Isaacs, *Character Theory of Finite
Groups*, Chapter 7.
-/

public section

namespace TauCeti

/-- Multiplication by units, regarded as automorphisms of the additive group of a ring. -/
def affineAction (F : Type*) [Ring F] : Fˣ →* MulAut (Multiplicative F) where
  toFun u := (DistribMulAction.toAddEquiv F u).toMultiplicative
  map_one' := by
    ext x
    simp
  map_mul' u v := by
    ext x
    simp [mul_smul]

@[simp]
theorem affineAction_apply_toAdd {F : Type*} [Ring F] (u : Fˣ) (x : Multiplicative F) :
    (affineAction F u x).toAdd = (u : F) * x.toAdd :=
  by simp [affineAction, DistribMulAction.toAddEquiv, Units.smul_def]

/-- The inverse of multiplication by a unit `u` is multiplication by `u⁻¹`. -/
@[simp]
theorem affineAction_symm_apply_toAdd {F : Type*} [Ring F] (u : Fˣ) (x : Multiplicative F) :
    ((affineAction F u).symm x).toAdd = ((u⁻¹ : Fˣ) : F) * x.toAdd := by
  rw [← MulAut.inv_def, ← map_inv, affineAction_apply_toAdd]

/-- The one-dimensional affine group `F ⋊ Fˣ`, with units acting on the additive group by
multiplication. -/
abbrev AffineGroup (F : Type*) [Ring F] :=
  Multiplicative F ⋊[affineAction F] Fˣ

/-- An element `(b, a)` of the affine group sends `x` to `b + a * x`. -/
instance {F : Type*} [Ring F] : SMul (AffineGroup F) F where
  smul g x := g.left.toAdd + (g.right : F) * x

/-- An element `(b, a)` of the affine group acts by `x ↦ b + a * x`. -/
theorem AffineGroup.smul_def {F : Type*} [Ring F] (g : AffineGroup F) (x : F) :
    g • x = g.left.toAdd + (g.right : F) * x :=
  (rfl)

/-- Two elements of the affine group are equal when their translation and linear parts agree. -/
@[ext]
theorem AffineGroup.ext {F : Type*} [Ring F] {g g' : AffineGroup F}
    (h₁ : g.left.toAdd = g'.left.toAdd) (h₂ : (g.right : F) = g'.right) : g = g' :=
  SemidirectProduct.ext (Multiplicative.toAdd.injective h₁) (Units.ext h₂)

/-- The affine group acts on its ring by affine maps. -/
instance {F : Type*} [Ring F] : MulAction (AffineGroup F) F where
  one_smul x := by simp [AffineGroup.smul_def]
  mul_smul g h x := by simp [AffineGroup.smul_def, mul_add, mul_assoc, add_assoc]

/-- The affine group acts faithfully on its ring: an affine map is determined by its values at
`0` and `1`. -/
instance {F : Type*} [Ring F] : FaithfulSMul (AffineGroup F) F where
  eq_of_smul_eq_smul {g h} hgh := by
    have h0 := hgh 0
    have h1 := hgh 1
    simp only [AffineGroup.smul_def, mul_zero, add_zero, mul_one] at h0 h1
    rw [h0, add_right_inj] at h1
    exact AffineGroup.ext h0 h1

/-- A ring homomorphism `f : F →+* E` induces the homomorphism of affine groups
`(b, a) ↦ (f b, f a)`. -/
def AffineGroup.map {F E : Type*} [Ring F] [Ring E] (f : F →+* E) :
    AffineGroup F →* AffineGroup E :=
  SemidirectProduct.map (AddMonoidHom.toMultiplicative (f : F →+ E)) (Units.map (f : F →* E))
    fun u ↦ by
      ext x
      simp

/-- The translation part of `AffineGroup.map f g` is the image of that of `g`. -/
@[simp]
theorem AffineGroup.toAdd_map_left {F E : Type*} [Ring F] [Ring E] (f : F →+* E)
    (g : AffineGroup F) : (AffineGroup.map f g).left.toAdd = f g.left.toAdd :=
  (rfl)

/-- The linear part of `AffineGroup.map f g` is the image of that of `g`. -/
@[simp]
theorem AffineGroup.coe_map_right {F E : Type*} [Ring F] [Ring E] (f : F →+* E)
    (g : AffineGroup F) : ((AffineGroup.map f g).right : E) = f g.right :=
  (rfl)

/-- The homomorphism of affine groups induced by an injective ring homomorphism is injective. -/
theorem AffineGroup.map_injective {F E : Type*} [Ring F] [Ring E] {f : F →+* E}
    (hf : Function.Injective f) : Function.Injective (AffineGroup.map f) := by
  intro g h hgh
  ext
  · exact hf (by simpa using congrArg (fun k : AffineGroup E ↦ k.left.toAdd) hgh)
  · exact hf (by simpa using congrArg (fun k : AffineGroup E ↦ (k.right : E)) hgh)

/-- A ring homomorphism intertwines the affine actions: `map f g • f x = f (g • x)`. -/
theorem AffineGroup.map_smul {F E : Type*} [Ring F] [Ring E] (f : F →+* E) (g : AffineGroup F)
    (x : F) : AffineGroup.map f g • f x = f (g • x) := by
  simp [AffineGroup.smul_def]

/-- The translation part of a composite: `(b, a) * (b', a') = (b + a b', a a')`, matching the
composite `x ↦ b + a (b' + a' x)` of the affine maps. -/
theorem AffineGroup.toAdd_mul_left {F : Type*} [Ring F] (g h : AffineGroup F) :
    (g * h).left.toAdd = g.left.toAdd + (g.right : F) * h.left.toAdd := by
  simp [SemidirectProduct.mul_left]

/-- The translation part of an inverse: `(b, a)⁻¹ = (-(a⁻¹ b), a⁻¹)`. -/
theorem AffineGroup.toAdd_inv_left {F : Type*} [Ring F] (g : AffineGroup F) :
    g⁻¹.left.toAdd = -(((g.right⁻¹ : Fˣ) : F) * g.left.toAdd) := by
  rw [SemidirectProduct.inv_left, affineAction_apply_toAdd, toAdd_inv, mul_neg]

/-- An affine map sends `0` to its translation part. -/
@[simp]
theorem AffineGroup.smul_zero_eq_toAdd_left {F : Type*} [Ring F] (g : AffineGroup F) :
    g • (0 : F) = g.left.toAdd := by
  simp [AffineGroup.smul_def]

/-- The linear part of an affine map is read off from its action as `g • 1 - g • 0`; together with
`AffineGroup.smul_zero_eq_toAdd_left` this recovers both coordinates of `g` from its action. -/
theorem AffineGroup.coe_right_eq_smul_one_sub_smul_zero {F : Type*} [Ring F]
    (g : AffineGroup F) : (g.right : F) = g • (1 : F) - g • (0 : F) := by
  simp [AffineGroup.smul_def]

/-- The affine group of a ring acts transitively on it, already through its translations. -/
instance AffineGroup.isPretransitive {F : Type*} [Ring F] :
    MulAction.IsPretransitive (AffineGroup F) F :=
  ⟨fun x y ↦ ⟨SemidirectProduct.inl (Multiplicative.ofAdd (y - x)),
    by simp only [AffineGroup.smul_def, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      toAdd_ofAdd, Units.val_one, one_mul, sub_add_cancel]⟩⟩

/-- The normal subgroup of translations in the affine group. -/
def affineTranslationSubgroup (F : Type*) [Ring F] : Subgroup (AffineGroup F) :=
  (SemidirectProduct.inl : Multiplicative F →* AffineGroup F).range

/-- The subgroup of linear maps fixing zero in the affine group. -/
def affineLinearSubgroup (F : Type*) [Ring F] : Subgroup (AffineGroup F) :=
  (SemidirectProduct.inr : Fˣ →* AffineGroup F).range

/-- The translation subgroup is the kernel of the linear-part homomorphism
`SemidirectProduct.rightHom : AffineGroup F →* Fˣ`, which is surjective by
`SemidirectProduct.rightHom_surjective`. -/
theorem affineTranslationSubgroup_eq_ker_rightHom (F : Type*) [Ring F] :
    affineTranslationSubgroup F = (SemidirectProduct.rightHom : AffineGroup F →* Fˣ).ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-- An affine transformation is a translation exactly when its linear coordinate is one. -/
@[simp]
theorem mem_affineTranslationSubgroup_iff {F : Type*} [Ring F] (g : AffineGroup F) :
    g ∈ affineTranslationSubgroup F ↔ g.right = 1 := by
  rw [affineTranslationSubgroup_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]

/-- An affine transformation lies in the linear factor exactly when its translation coordinate
is zero. -/
@[simp]
theorem mem_affineLinearSubgroup_iff {F : Type*} [Ring F] (g : AffineGroup F) :
    g ∈ affineLinearSubgroup F ↔ g.left.toAdd = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hg
    refine ⟨g.right, SemidirectProduct.ext ?_ rfl⟩
    exact Multiplicative.ext hg.symm

/-- The translation subgroup of an affine group is normal. -/
instance {F : Type*} [Ring F] : (affineTranslationSubgroup F).Normal := by
  rw [affineTranslationSubgroup_eq_ker_rightHom]
  infer_instance

/-- The stabilizer of `0` in the affine group is the linear factor. -/
theorem AffineGroup.stabilizer_zero (F : Type*) [Ring F] :
    MulAction.stabilizer (AffineGroup F) (0 : F) = affineLinearSubgroup F := by
  ext g
  simp

/-- The linear factor has index `|F|` in the affine group: it is the stabilizer of a point for
a transitive action on `F`. -/
theorem index_affineLinearSubgroup (F : Type*) [Ring F] :
    (affineLinearSubgroup F).index = Nat.card F := by
  rw [← AffineGroup.stabilizer_zero, MulAction.index_stabilizer_of_transitive]

/-- The translation and linear-factor subgroups of an affine group are complementary. -/
theorem isComplement'_affineTranslationSubgroup_affineLinearSubgroup
    (F : Type*) [Ring F] :
    (affineTranslationSubgroup F).IsComplement' (affineLinearSubgroup F) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · refine Subgroup.disjoint_def.mpr ?_
    rintro g ⟨b, rfl⟩ ⟨a, ha⟩
    have hb : b = 1 := by
      apply Multiplicative.ext
      simpa using congrArg (fun x : AffineGroup F ↦ x.left.toAdd) ha.symm
    subst b
    simp
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    rw [Set.mem_mul]
    exact ⟨SemidirectProduct.inl g.left, ⟨g.left, rfl⟩,
      SemidirectProduct.inr g.right, ⟨g.right, rfl⟩,
      SemidirectProduct.inl_left_mul_inr_right g⟩

/-- The translation subgroup of an affine group has the same natural cardinality as the ring. -/
theorem card_affineTranslationSubgroup (F : Type*) [Ring F] :
    Nat.card (affineTranslationSubgroup F) = Nat.card F := by
  rw [affineTranslationSubgroup_eq_ker_rightHom]
  exact (Nat.card_congr SemidirectProduct.mulEquivKerRightHom.toEquiv.symm).trans
    (Nat.card_congr Multiplicative.toAdd)

/-- The linear factor of an affine group has natural cardinality one less than the ring. -/
theorem card_affineLinearSubgroup (F : Type*) [DivisionRing F] :
    Nat.card (affineLinearSubgroup F) = Nat.card F - 1 :=
  (Nat.card_congr (MonoidHom.ofInjective
      (f := (SemidirectProduct.inr : Fˣ →* AffineGroup F))
      SemidirectProduct.inr_injective).toEquiv.symm).trans (Nat.card_units F)

/-- A one-dimensional affine group has natural cardinality `|F| (|F| - 1)`. -/
theorem card_affineGroup (F : Type*) [DivisionRing F] :
    Nat.card (AffineGroup F) = Nat.card F * (Nat.card F - 1) := by
  rw [SemidirectProduct.card, Nat.card_units]
  rfl

/-- A nonidentity element of the linear factor acts without nonidentity fixed points on the
translation subgroup. -/
theorem fixedPointFree_conjNormal_affineTranslationSubgroup
    {F : Type*} [Ring F] [NoZeroDivisors F]
    (h : affineLinearSubgroup F) (hh : h ≠ 1) :
    MonoidHom.FixedPointFree
      (MulAut.conjNormal (h : AffineGroup F) : MulAut (affineTranslationSubgroup F)) := by
  rintro n hn
  rcases h.property with ⟨u, hu⟩
  rcases n.property with ⟨x, hx⟩
  have hu_one : u ≠ 1 := by
    intro h1
    apply hh
    apply Subtype.ext
    simpa [h1] using hu.symm
  have hu_val : (u : F) ≠ 1 := fun hu_val ↦ hu_one (Units.ext hu_val)
  have hux : (u : F) * x.toAdd = x.toAdd := by
    have hconj : (h : AffineGroup F) * (n : AffineGroup F) * (h : AffineGroup F)⁻¹ = n :=
      (MulAut.conjNormal_apply _ _).symm.trans (congrArg Subtype.val hn)
    rw [← hu, ← hx] at hconj
    rw [← map_inv, ← SemidirectProduct.inl_aut] at hconj
    exact congrArg (fun y : AffineGroup F ↦ y.left.toAdd) hconj
  have hx_zero : x.toAdd = 0 := by
    have hzero : ((u : F) - 1) * x.toAdd = 0 := by
      rw [sub_mul, one_mul, hux, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hu_val)
  apply Subtype.ext
  rw [← hx]
  apply SemidirectProduct.ext
  · exact Multiplicative.ext hx_zero
  · simp

/-- The linear factor in an affine group is a trivial-intersection subgroup. -/
theorem isTISubgroup_affineLinearSubgroup
    (F : Type*) [Ring F] [NoZeroDivisors F] :
    IsTISubgroup (affineLinearSubgroup F) := by
  apply isTISubgroup_of_isComplement'_of_fixedPointFree
    (isComplement'_affineTranslationSubgroup_affineLinearSubgroup F)
  exact fixedPointFree_conjNormal_affineTranslationSubgroup

/-- For a finite division ring of order at least three, its affine group is a Frobenius group
with the linear factor as a Frobenius complement. -/
theorem isFrobeniusComplement_affineLinearSubgroup
    (F : Type*) [DivisionRing F] (hF : 3 ≤ Nat.card F) :
    IsFrobeniusComplement (affineLinearSubgroup F) := by
  refine isFrobeniusComplement_of_isComplement'_of_fixedPointFree
    (isComplement'_affineTranslationSubgroup_affineLinearSubgroup F) ?_ ?_
    fixedPointFree_conjNormal_affineTranslationSubgroup
  · intro hbot
    have hcard := card_affineLinearSubgroup F
    rw [hbot, Nat.card_unique] at hcard
    omega
  · intro htop
    have hmem : SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) ∈
        affineLinearSubgroup F := htop ▸ Subgroup.mem_top _
    rw [mem_affineLinearSubgroup_iff] at hmem
    simp at hmem

section CommRing

open scoped commutatorElement

variable {F : Type*} [CommRing F]

/-- **The commutator in the affine group of a commutative ring.** The commutator
`g h g⁻¹ h⁻¹` of `g = (b, a)` and `h = (b', a')` is the translation by
`b (1 - a') - b' (1 - a)`. -/
theorem AffineGroup.commutatorElement_eq_inl (g h : AffineGroup F) :
    ⁅g, h⁆ = SemidirectProduct.inl (Multiplicative.ofAdd
      (g.left.toAdd * (1 - h.right) - h.left.toAdd * (1 - g.right))) := by
  have hg : (g.right : F) * ((g.right⁻¹ : Fˣ) : F) = 1 := g.right.mul_inv
  have hh : (h.right : F) * ((h.right⁻¹ : Fˣ) : F) = 1 := h.right.mul_inv
  ext
  · simp only [commutatorElement_def, AffineGroup.toAdd_mul_left, AffineGroup.toAdd_inv_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_right, Units.val_mul,
      SemidirectProduct.left_inl, toAdd_ofAdd]
    linear_combination (-(g.left.toAdd * (h.right : F) + h.left.toAdd)) * hg -
      (h.left.toAdd * (g.right : F) * ((g.right⁻¹ : Fˣ) : F)) * hh
  · simp only [commutatorElement_def, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, Units.val_mul, Units.val_one]
    linear_combination (h.right : F) * ((h.right⁻¹ : Fˣ) : F) * hg + hh

/-- **The derived subgroup of an affine group.** Over a commutative ring with a unit `u` for which
`u - 1` is also a unit, the commutator subgroup of the affine group is the translation subgroup.
(Some such hypothesis is needed: over `ℤ` the commutators are the even translations.) -/
theorem commutator_affineGroup_eq_of_isUnit_sub_one (u : Fˣ) (hu : IsUnit ((u : F) - 1)) :
    commutator (AffineGroup F) = affineTranslationSubgroup F := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [AffineGroup.commutatorElement_eq_inl]
    exact ⟨_, rfl⟩
  · rintro _ ⟨t, rfl⟩
    -- The translation by `t` is the commutator of the translation by `-t (u - 1)⁻¹` with the
    -- dilation by `u`.
    have key : SemidirectProduct.inl t = ⁅(SemidirectProduct.inl
        (Multiplicative.ofAdd (-(t.toAdd * ((hu.unit⁻¹ : Fˣ) : F)))) : AffineGroup F),
        (SemidirectProduct.inr u : AffineGroup F)⁆ := by
      rw [AffineGroup.commutatorElement_eq_inl, SemidirectProduct.inl_inj]
      have h1 : ((hu.unit⁻¹ : Fˣ) : F) * ((u : F) - 1) = 1 := by
        simp
      apply Multiplicative.toAdd.injective
      simp only [SemidirectProduct.left_inl, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, SemidirectProduct.right_inl, toAdd_ofAdd, toAdd_one,
        Units.val_one, sub_self, mul_zero, sub_zero]
      linear_combination (-t.toAdd) * h1
    rw [key, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Over a field with at least three elements the commutator subgroup of the affine group is the
translation subgroup. -/
theorem commutator_affineGroup_eq {F : Type*} [Field F] [Nontrivial Fˣ] :
    commutator (AffineGroup F) = affineTranslationSubgroup F := by
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  exact commutator_affineGroup_eq_of_isUnit_sub_one u
    (sub_ne_zero.2 fun h ↦ hu (Units.ext h)).isUnit

end CommRing

end TauCeti
