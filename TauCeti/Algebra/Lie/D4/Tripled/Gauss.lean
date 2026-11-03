/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme

/-!
# Opposite-root factorization in the tripled D₄ carrier

Opposite numbered simple-root subgroups satisfy the rank-one Gauss relation whenever
`1 + a * b` is a unit. The middle factor is the value of the corresponding simple coroot:
in fundamental-weight coordinates it is the existing weight torus at `Pi.mulSingle i c`.
Both multiplication orders are covered, over arbitrary commutative coefficient rings.

The carrier is not identified here with the independently pinned simply connected D₄ group
scheme. These identities transfer to that group only along such an identification.

## Main results

* `TauCeti.D4Tripled.rootSubgroupPoints_inl_mul_inr`: positive times negative factorization.
* `TauCeti.D4Tripled.rootSubgroupPoints_inr_mul_inl`: negative times positive factorization.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.

The calculation uses the minuscule column formulas in
`TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic` and the root and weight-torus
matrices constructed in `TauCeti.Algebra.Lie.D4.Tripled.GroupScheme`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open DynkinType TauCeti.UniversalEnvelopingAlgebra

variable {A : Type*} [CommRing A]

private theorem positive_mulVec_single (i : Fin 4) (t : A) (j : Fin 24) :
    ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A) *ᵥ
      Pi.single j 1 =
        Pi.single j 1 +
          if d4TripledWeight j i = -1 then t • Pi.single (d4TripledReflection i j) 1
          else 0 := by
  rw [coe_rootSubgroupPoints_inl, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_single_one, raisingMatrix_def,
    weightTable.raisingMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, toAdd_ofAdd,
    smul_ite, smul_zero]

private theorem negative_mulVec_single (i : Fin 4) (t : A) (j : Fin 24) :
    ((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A) *ᵥ
      Pi.single j 1 =
        Pi.single j 1 +
          if d4TripledWeight j i = 1 then t • Pi.single (d4TripledReflection i j) 1
          else 0 := by
  rw [coe_rootSubgroupPoints_inr, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_single_one, loweringMatrix_def,
    weightTable.loweringMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, toAdd_ofAdd,
    smul_ite, smul_zero]

private theorem coroot_mulVec_single (i : Fin 4) (c : Aˣ) (j : Fin 24) :
    ((weightTorusPoints A (Pi.mulSingle i c) :
        Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A) *ᵥ
      Pi.single j 1 = (↑(c ^ d4TripledWeight j i) : A) • Pi.single j 1 := by
  rw [coe_weightTorusPoints, kostantTorusMatrix_apply]
  ext r
  by_cases hr : r = j <;> simp [hr]

/-- The Gauss factorization for opposite simple-root points. The unit `c` is `1 + a * b`,
and the middle factor is the `i`-th simple coroot evaluated at `c`. No invertibility
of either root parameter is required. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 4) (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c) *
          rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) := by
  have hinv : (↑c⁻¹ : A) + a * ↑c⁻¹ * b = 1 := by
    calc
      _ = (1 + a * b) * (↑c⁻¹ : A) := by ring
      _ = 1 := by rw [← hc, c.mul_inv]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have href : d4TripledWeight (d4TripledReflection i j) i = -d4TripledWeight j i :=
    by simpa only [weightTable_weight, weightTable_reflection] using
      weightTable.weight_reflection_self i j
  have hrr : d4TripledReflection i (d4TripledReflection i j) = j :=
    by simpa only [weightTable_reflection] using weightTable.reflection_apply_apply i j
  -- Subtype multiplication and multiplication of matrix units have the same underlying matrix.
  change (_ * _) *ᵥ Pi.single j (1 : A) = ((_ * _) * _) *ᵥ Pi.single j (1 : A)
  rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one j i with hj | hj | hj
  all_goals
    simp only [← Matrix.mulVec_mulVec, positive_mulVec_single, negative_mulVec_single,
      Matrix.mulVec_add, Matrix.mulVec_smul, coroot_mulVec_single, href, hj, hrr,
      neg_neg, zpow_neg_one, zpow_zero, zpow_one, Units.val_one,
      ite_true, ite_eq_right (by decide : (-1 : ℤ) ≠ 1),
      ite_eq_right (by decide : (1 : ℤ) ≠ -1), ite_eq_right (by decide : (0 : ℤ) ≠ -1),
      ite_eq_right (by decide : (0 : ℤ) ≠ 1),
      smul_add, smul_smul, add_zero, one_smul]
  · rw [mul_comm b (↑c⁻¹ : A), c.mul_inv_cancel_left, Units.inv_mul_cancel_right]
    calc
      Pi.single j 1 + a • Pi.single (d4TripledReflection i j) 1 =
          ((↑c⁻¹ : A) + a * ↑c⁻¹ * b) • Pi.single j 1 +
            a • Pi.single (d4TripledReflection i j) 1 := by rw [hinv, one_smul]
      _ = _ := by rw [add_smul]; abel
  · rw [mul_comm b (↑c⁻¹ : A), c.mul_inv_cancel_left]
    calc
      Pi.single j 1 + (b • Pi.single (d4TripledReflection i j) 1 +
          (b * a) • Pi.single j 1) =
          (1 + b * a) • Pi.single j 1 + b • Pi.single (d4TripledReflection i j) 1 := by
        rw [add_smul, one_smul]
        abel
      _ = _ := by rw [mul_comm b a, ← hc]

/-- The reverse Gauss factorization. Relative to positive times negative, the simple-coroot
factor is inverted, and the positive root factor comes first. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 4) (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c⁻¹) *
          rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) := by
  have hneg : (c : A) = 1 + (-a) * (-b) := by simpa only [neg_mul_neg] using hc
  have h := congrArg Inv.inv (rootSubgroupPoints_inl_mul_inr i (-a) (-b) c hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv,
    neg_mul, Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.D4Tripled
