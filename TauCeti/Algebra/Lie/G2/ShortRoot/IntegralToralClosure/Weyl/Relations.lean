/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# The integral six-term braid relation on the short-root G₂ carrier

For the numbered simple-root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)`, this file proves
`(n₀ n₁)³ = (n₁ n₀)³`, the type-`G₂` braid relation, over every commutative ring.
It permits a braid move in the words used to transport root subgroups from simple roots;
it does not assert independence of all such presentations.

The calculation uses the integral seven-dimensional matrices, retaining the divided-square
terms at the short node. This carrier is not identified here with an independently constructed
pinned simply connected group scheme; constructions transfer to such a group only along a
separately proved identification.

## Main result

* `TauCeti.G2ShortRoot.IntegralToralClosure.rootSubgroupPoints_braid`: the six-term relation.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, the relations for the elements `nᵢ`.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The defining matrices and normalization are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.G2ShortRoot

/-- The integral matrix of the pinned three-factor simple-root word. -/
private def braidMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) *
    (1 - rootMatrix (.inr i) + rootDividedSquareMatrix (.inr i)) *
    (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i))

private theorem braidMatrix_braid :
    (braidMatrix 0 * braidMatrix 1) ^ 3 = (braidMatrix 1 * braidMatrix 0) ^ 3 := by
  simp only [braidMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr]
  decide +kernel

namespace IntegralToralClosure

private theorem coe_root_word (A : Type v) [CommRing A] (i : Fin 2) :
    ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      ((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (braidMatrix i).map (Int.castRingHom A) := by
  conv_rhs =>
    rw [← RingHom.mapMatrix_apply, braidMatrix]
    simp only [map_mul, map_add, map_sub, map_one]
  simp only [coe_rootSubgroupPoints, toAdd_ofAdd, one_pow, neg_one_sq,
    one_smul, neg_one_smul, sub_eq_add_neg, RingHom.mapMatrix_apply, Int.coe_castRingHom]

/-- The pinned simple-root words satisfy the six-term type-`G₂` braid relation over every
commutative ring. Node zero is short and node one is long, in Bourbaki numbering. -/
theorem rootSubgroupPoints_braid (A : Type v) [CommRing A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  dsimp only
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val, Units.val_mul]
  rw [coe_root_word, coe_root_word]
  simpa only [Matrix.map_pow, Matrix.map_mul] using
    congrArg (fun M => M.map (Int.castRingHom A)) braidMatrix_braid

end IntegralToralClosure

end TauCeti.G2ShortRoot
