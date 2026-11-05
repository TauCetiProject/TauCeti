/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Opposite short-root multiplication in the F4 carrier

The opposite simple-root Gauss relation is valid over any commutative ring whenever
`1 + a * b` is a unit. For the two short simple roots of the twenty-six-dimensional
carrier, the quadratic divided-power terms are essential, including in characteristic two.
The torus factor uses the corresponding Bourbaki simple-coroot coordinate.

The calculation uses the integral matrices of `TauCeti.F4ShortRoot.Basic` and the root-point
formulas of `TauCeti.F4ShortRoot.Carrier`. A finite coefficient certificate groups equal
matrix-entry calculations; no division by two or field hypothesis enters the relation.
This does not identify the carrier with an independently pinned simply connected group.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6 (rank-one relations).
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

private def gaussEntries (i : Fin 4) (r s : Fin 26) : Fin 14 → ℤ := ![
  f4ShortRootWeight r i, (1 : Matrix (Fin 26) (Fin 26) ℤ) r s,
  raisingMatrix i r s, raisingDividedSquareMatrix i r s,
  loweringMatrix i r s, loweringDividedSquareMatrix i r s,
  (raisingMatrix i * loweringMatrix i) r s,
  (raisingDividedSquareMatrix i * loweringMatrix i) r s,
  (raisingMatrix i * loweringDividedSquareMatrix i) r s,
  (raisingDividedSquareMatrix i * loweringDividedSquareMatrix i) r s,
  (loweringMatrix i * raisingMatrix i) r s,
  (loweringMatrix i * raisingDividedSquareMatrix i) r s,
  (loweringDividedSquareMatrix i * raisingMatrix i) r s,
  (loweringDividedSquareMatrix i * raisingDividedSquareMatrix i) r s]

-- These are precisely the different entry patterns for the two short nodes. Products are
-- checked over the integers, before any coefficient ring or root parameter is chosen.
private def gaussPatterns : List (Fin 14 → ℤ) := [
  ![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![-2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0],
  ![-2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1],
  ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
  ![2, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0]]

private theorem gaussEntries_mem (i : Fin 4) (hi : 2 ≤ i.val) (r s : Fin 26) :
    gaussEntries i r s ∈ gaussPatterns := by
  simp only [gaussEntries, Matrix.mul_apply, raisingMatrix_apply, loweringMatrix_apply,
    raisingDividedSquareMatrix_apply, loweringDividedSquareMatrix_apply, Matrix.one_apply]
  revert i r s
  decide +kernel

private theorem gauss_scalar {A : Type*} [CommRing A] (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) (d : Fin 14 → ℤ) (hd : d ∈ gaussPatterns) :
    (d 1 : A) + a * d 2 + a ^ 2 * d 3 + b * d 4 + b ^ 2 * d 5 +
        a * b * d 6 + a ^ 2 * b * d 7 + a * b ^ 2 * d 8 + a ^ 2 * b ^ 2 * d 9 =
      ((c ^ d 0 : Aˣ) : A) *
        (d 1 + (a * ↑c⁻¹) * d 2 + (a * ↑c⁻¹) ^ 2 * d 3 +
          (b * ↑c) * d 4 + (b * ↑c) ^ 2 * d 5 + a * b * d 10 +
          a ^ 2 * b * ↑c⁻¹ * d 11 + a * b ^ 2 * ↑c * d 12 +
          a ^ 2 * b ^ 2 * d 13) := by
  have hinv : (c : A) * (↑c⁻¹ : A) = 1 := c.val_inv
  simp only [gaussPatterns, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [zpow_neg, zpow_ofNat]
  all_goals grind only

private theorem gauss_torus_first {A : Type*} [CommRing A]
    (i : Fin 4) (hi : 2 ≤ i.val) (a b : A) (c : Aˣ) (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      weightTorusPoints A (Pi.mulSingle i c) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr,
    coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe, torusCharacter_mulSingle, toAdd_ofAdd]
  rw [mul_assoc]
  ext r s
  rw [Matrix.diagonal_mul]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    one_mul, mul_one, ← Matrix.map_mul_intCast]
  have h := gauss_scalar a b c hc (gaussEntries i r s) (gaussEntries_mem i hi r s)
  simp only [gaussEntries, Matrix.cons_val] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  simp only [Matrix.one_apply, Int.cast_ite, Int.cast_one, Int.cast_zero] at h ⊢
  have hinv : (c : A) * (↑c⁻¹ : A) = 1 := c.val_inv
  convert h using 1
  · ring
  · congr 1
    clear h hc
    grind only

/-- **The opposite-short-root Gauss relation.** If `c = 1 + a * b` is a unit, the
product of positive and negative root points factors as negative root, simple-coroot torus,
and positive root, with parameters `b / c` and `a / c`. The index is a short Bourbaki node. -/
theorem rootSubgroupPoints_inl_mul_inr {A : Type*} [CommRing A]
    (i : Fin 4) (hi : 2 ≤ i.val) (a b : A) (c : Aˣ) (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) := by
  have h := weightTorusPoints_conj_rootSubgroupPoints (.inr i) A
    (Pi.mulSingle i c) (Multiplicative.ofAdd (b * ↑c))
  have hchar : torusCharacter (Pi.mulSingle i c)
      (DynkinType.F4.rootGeneratorWeight valid_F4 (.inr i)) = c ^ (-2 : ℤ) := by
    -- The carrier uses Fin 4, whereas the root character uses Fin F4.rank; elaboration
    -- rewriting reduces the named rank before matching the character equations.
    erw [torusCharacter_mulSingle, DynkinType.rootGeneratorWeight_inr,
      DynkinType.cartanMatrix_apply_same]
  erw [hchar] at h
  have hparam : ((c ^ (-2 : ℤ) : Aˣ) : A) * (b * ↑c) = b * ↑c⁻¹ := by
    norm_num [zpow_neg, zpow_ofNat]
    have hinv : (c : A) * (↑c⁻¹ : A) = 1 := c.val_inv
    grind only
  simp only [toAdd_ofAdd, hparam] at h
  rw [gauss_torus_first i hi a b c hc, eq_mul_of_mul_inv_eq h]

/-- The reverse opposite-short-root Gauss relation, with simple-coroot torus parameter
`c⁻¹`, for a unit `c = 1 + a * b`. -/
theorem rootSubgroupPoints_inr_mul_inl {A : Type*} [CommRing A]
    (i : Fin 4) (hi : 2 ≤ i.val) (a b : A) (c : Aˣ) (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) := by
  have h := congrArg Inv.inv
    (rootSubgroupPoints_inl_mul_inr i hi (-a) (-b) c (by simpa using hc))
  simpa only [mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_mul, neg_neg,
    ← Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.F4ShortRoot
