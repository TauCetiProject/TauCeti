/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme

/-!
# Braid relations on the E₆ minuscule carrier

The pinned root words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` on the twenty-seven-dimensional minuscule
carrier satisfy the E₆ braid relations over every commutative ring. Nonadjacent words commute;
adjacent words satisfy the three-factor relation, with their integral signs retained.
These are equalities in the explicit carrier, not just in its Weyl group. They supply the
braid moves needed when transporting root subgroups by such words. No identification with
an independently pinned group scheme or independence of arbitrary root presentations is asserted.

The calculation uses the minuscule weight basis: a root word acts by the simple reflection,
with a minus sign precisely on weights pairing to one with the simple coroot. The signed action
and both braid relations come from the generic `TauCeti.MinusculeWeightTable` API.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The integral generators and weight enumeration are those of
`TauCeti.Algebra.Lie.E6.Minuscule.Basic`.
-/

public section

open Matrix

namespace TauCeti.E6Minuscule

open DynkinType

/-- Pinned simple Weyl words at nonadjacent E₆ nodes commute over every commutative ring. -/
theorem simpleWeyl_commute_of_cartanMatrix_eq_zero (i j : Fin 6)
    (h : CartanMatrix.E 6 i j = 0) (A : Type*) [CommRing A] :
    Commute
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1))
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  have hij : weightTable.cartanMatrix i j = 0 := by
    simpa only [weightTable_cartanMatrix, CartanMatrix.E_transpose] using h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl,
    coe_rootSubgroupPoints_inr, toAdd_ofAdd, neg_smul, one_smul]
  simpa only [sub_eq_add_neg] using
    (weightTable.simpleWeyl_map_commute_of_cartanMatrix_eq_zero (R := A) i j hij).eq

/-- Pinned simple Weyl words at adjacent E₆ nodes satisfy the length-three braid relation,
including over rings with torsion or nilpotents. -/
theorem simpleWeyl_braid_of_cartanMatrix_eq_neg_one (i j : Fin 6)
    (h : CartanMatrix.E 6 i j = -1) (A : Type*) [CommRing A] :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) =
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  have hij : weightTable.cartanMatrix i j = -1 := by
    simpa only [weightTable_cartanMatrix, CartanMatrix.E_transpose] using h
  have hji : weightTable.cartanMatrix j i = -1 := by
    simpa only [weightTable_cartanMatrix, Matrix.transpose_apply] using h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl,
    coe_rootSubgroupPoints_inr, toAdd_ofAdd, neg_smul, one_smul]
  simpa only [sub_eq_add_neg] using
    weightTable.simpleWeyl_map_braid_of_cartanMatrix_eq_neg_one (R := A) i j hij hji

end TauCeti.E6Minuscule
