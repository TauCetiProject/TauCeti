/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# Affine groups over division rings

For a division ring `F`, the one-dimensional affine group is the semidirect product of the additive
group of `F` by its unit group.  We realize the additive group as `Multiplicative F`, so that
Mathlib's multiplicative semidirect product can be used directly.  An element `(b, a)` acts on
`F` by `x ↦ b + a * x`.

This file identifies the translation and linear-factor subgroups, proves that they are
complementary, and verifies that every nonidentity linear factor acts without nonidentity fixed
points on the translations.  Thus finite affine groups with at least three elements are
Frobenius groups; their Frobenius kernels are identified in
`TauCeti.RepresentationTheory.FrobeniusGroup.Affine`.

## Main definitions and results

* `TauCeti.affineAction`: multiplication by a unit on the additive group of a division ring.
* `TauCeti.AffineGroup`: the semidirect product `F ⋊ Fˣ` for this action.
* `TauCeti.affineTranslationSubgroup` and `TauCeti.affineLinearSubgroup`: the two canonical
  factors.
* `TauCeti.isComplement'_affineTranslationSubgroup_affineLinearSubgroup`: the two factors are
  complementary.
* `TauCeti.fixedPointFree_conjNormal_affineTranslationSubgroup`: a nonidentity linear factor
  fixes no nonidentity translation.
* `TauCeti.isFrobeniusComplement_affineLinearSubgroup`: for a finite division ring of order at least
  three, the linear factor is a Frobenius complement.

The construction is the standard affine-group example; see Isaacs, *Character Theory of Finite
Groups*, Chapter 7.
-/

public section

namespace TauCeti

/-- Multiplication by units, regarded as automorphisms of the additive group of a division ring. -/
def affineAction (F : Type*) [DivisionRing F] : Fˣ →* MulAut (Multiplicative F) where
  toFun u := (DistribMulAction.toAddEquiv F u).toMultiplicative
  map_one' := by
    ext x
    simp
  map_mul' u v := by
    ext x
    simp [mul_smul]

@[simp]
theorem affineAction_apply_toAdd {F : Type*} [DivisionRing F] (u : Fˣ) (x : Multiplicative F) :
    (affineAction F u x).toAdd = (u : F) * x.toAdd :=
  by simp [affineAction, DistribMulAction.toAddEquiv, Units.smul_def]

/-- The one-dimensional affine group `F ⋊ Fˣ`, with units acting on the additive group by
multiplication. -/
abbrev AffineGroup (F : Type*) [DivisionRing F] :=
  Multiplicative F ⋊[affineAction F] Fˣ

/-- A one-dimensional affine group over a finite division ring is finite. -/
instance {F : Type*} [DivisionRing F] [Finite F] : Finite (AffineGroup F) :=
  Finite.of_equiv (Multiplicative F × Fˣ) SemidirectProduct.equivProd.symm

/-- The normal subgroup of translations in the affine group. -/
def affineTranslationSubgroup (F : Type*) [DivisionRing F] : Subgroup (AffineGroup F) :=
  (SemidirectProduct.inl : Multiplicative F →* AffineGroup F).range

/-- The subgroup of linear maps fixing zero in the affine group. -/
def affineLinearSubgroup (F : Type*) [DivisionRing F] : Subgroup (AffineGroup F) :=
  (SemidirectProduct.inr : Fˣ →* AffineGroup F).range

/-- An affine transformation is a translation exactly when its linear coordinate is one. -/
@[simp]
theorem mem_affineTranslationSubgroup_iff {F : Type*} [DivisionRing F] (g : AffineGroup F) :
    g ∈ affineTranslationSubgroup F ↔ g.right = 1 := by
  unfold affineTranslationSubgroup
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

/-- An affine transformation lies in the linear factor exactly when its translation coordinate
is zero. -/
@[simp]
theorem mem_affineLinearSubgroup_iff {F : Type*} [DivisionRing F] (g : AffineGroup F) :
    g ∈ affineLinearSubgroup F ↔ g.left.toAdd = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hg
    refine ⟨g.right, SemidirectProduct.ext ?_ rfl⟩
    exact Multiplicative.ext hg.symm

/-- The translation subgroup of an affine group is normal. -/
instance {F : Type*} [DivisionRing F] : (affineTranslationSubgroup F).Normal := by
  unfold affineTranslationSubgroup
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The translation and linear-factor subgroups of an affine group are complementary. -/
theorem isComplement'_affineTranslationSubgroup_affineLinearSubgroup
    (F : Type*) [DivisionRing F] :
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
theorem card_affineTranslationSubgroup (F : Type*) [DivisionRing F] :
    Nat.card (affineTranslationSubgroup F) = Nat.card F := by
  unfold affineTranslationSubgroup
  change Nat.card (Set.range (SemidirectProduct.inl : Multiplicative F → AffineGroup F)) = _
  rw [Nat.card_range_of_injective SemidirectProduct.inl_injective]
  rfl

/-- The linear factor of an affine group has natural cardinality one less than the ring. -/
theorem card_affineLinearSubgroup (F : Type*) [DivisionRing F] :
    Nat.card (affineLinearSubgroup F) = Nat.card F - 1 := by
  unfold affineLinearSubgroup
  change Nat.card (Set.range (SemidirectProduct.inr : Fˣ → AffineGroup F)) = _
  rw [Nat.card_range_of_injective SemidirectProduct.inr_injective]
  exact Nat.card_units F

/-- A one-dimensional affine group has natural cardinality `|F| (|F| - 1)`. -/
theorem card_affineGroup (F : Type*) [DivisionRing F] :
    Nat.card (AffineGroup F) = Nat.card F * (Nat.card F - 1) := by
  rw [SemidirectProduct.card, Nat.card_units]
  rfl

/-- A nonidentity element of the linear factor acts without nonidentity fixed points on the
translation subgroup. -/
theorem fixedPointFree_conjNormal_affineTranslationSubgroup
    {F : Type*} [DivisionRing F] (h : affineLinearSubgroup F) (hh : h ≠ 1) :
    MonoidHom.FixedPointFree
      (MulAut.conjNormal (h : AffineGroup F) : MulAut (affineTranslationSubgroup F)) := by
  rintro n hn
  rcases h.2 with ⟨u, hu⟩
  rcases n.2 with ⟨x, hx⟩
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
    (F : Type*) [DivisionRing F] :
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

end TauCeti
