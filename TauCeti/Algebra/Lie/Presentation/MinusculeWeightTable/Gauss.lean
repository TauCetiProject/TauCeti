/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic

/-!
# Gauss factorization for minuscule weight tables

The integral raising and lowering matrices of any minuscule weight table satisfy the
rank-one Gauss relation over arbitrary commutative coefficient rings. The middle factor
is diagonal, with entries given by the simple-coroot coordinates of the weights.

The main result `TauCeti.MinusculeWeightTable.one_add_raising_mul_one_add_lowering`
supplies the matrix calculation for opposite-root factorization in explicit minuscule carriers.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (T : MinusculeWeightTable B ι)

private theorem one_add_raising_mulVec_single (i : B) (t : A) (j : ι) :
    (1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → A)) *ᵥ Pi.single j 1 =
      Pi.single j 1 +
        if T.weight j i = -1 then t • Pi.single (T.reflection i j) 1 else 0 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_single_one, T.raisingMatrix_map_col]
  simp only [smul_ite, smul_zero]

private theorem one_add_lowering_mulVec_single (i : B) (t : A) (j : ι) :
    (1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → A)) *ᵥ Pi.single j 1 =
      Pi.single j 1 +
        if T.weight j i = 1 then t • Pi.single (T.reflection i j) 1 else 0 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_single_one, T.loweringMatrix_map_col]
  simp only [smul_ite, smul_zero]

private theorem coroot_mulVec_single (i : B) (c : Aˣ) (j : ι) :
    Matrix.diagonal (fun j => (↑(c ^ T.weight j i) : A)) *ᵥ Pi.single j 1 =
      (↑(c ^ T.weight j i) : A) • Pi.single j 1 := by
  ext r
  by_cases hr : r = j <;> simp [hr]

/-- The rank-one Gauss factorization for the raising and lowering matrices of a minuscule
weight table. The only invertibility assumption is that `c` represents `1 + a * b`;
the middle diagonal matrix evaluates the `i`-th simple coroot at `c`. -/
theorem one_add_raising_mul_one_add_lowering (i : B) (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) :
    (1 + a • (T.raisingMatrix i).map (Int.cast : ℤ → A)) *
        (1 + b • (T.loweringMatrix i).map (Int.cast : ℤ → A)) =
      (1 + (b * ↑c⁻¹) • (T.loweringMatrix i).map (Int.cast : ℤ → A)) *
        Matrix.diagonal (fun j => (↑(c ^ T.weight j i) : A)) *
          (1 + (a * ↑c⁻¹) • (T.raisingMatrix i).map (Int.cast : ℤ → A)) := by
  have hinv : (↑c⁻¹ : A) + a * ↑c⁻¹ * b = 1 := by
    calc
      _ = (1 + a * b) * (↑c⁻¹ : A) := by ring
      _ = 1 := by rw [← hc, c.mul_inv]
  apply Matrix.ext_of_mulVec_single
  intro j
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one j i with hj | hj | hj
  all_goals
    simp only [← Matrix.mulVec_mulVec, one_add_raising_mulVec_single,
      one_add_lowering_mulVec_single, Matrix.mulVec_add, Matrix.mulVec_smul,
      coroot_mulVec_single, T.weight_reflection_self, hj, T.reflection_apply_apply,
      neg_neg, zpow_neg_one, zpow_zero, zpow_one, Units.val_one,
      ite_true, ite_eq_right (by decide : (-1 : ℤ) ≠ 1),
      ite_eq_right (by decide : (1 : ℤ) ≠ -1), ite_eq_right (by decide : (0 : ℤ) ≠ -1),
      ite_eq_right (by decide : (0 : ℤ) ≠ 1),
      smul_add, smul_smul, add_zero, one_smul]
  · rw [mul_comm b (↑c⁻¹ : A), c.mul_inv_cancel_left, Units.inv_mul_cancel_right]
    calc
      Pi.single j 1 + a • Pi.single (T.reflection i j) 1 =
          ((↑c⁻¹ : A) + a * ↑c⁻¹ * b) • Pi.single j 1 +
            a • Pi.single (T.reflection i j) 1 := by rw [hinv, one_smul]
      _ = _ := by rw [add_smul]; abel
  · rw [mul_comm b (↑c⁻¹ : A), c.mul_inv_cancel_left]
    calc
      Pi.single j 1 + (b • Pi.single (T.reflection i j) 1 +
          (b * a) • Pi.single j 1) =
          (1 + b * a) • Pi.single j 1 + b • Pi.single (T.reflection i j) 1 := by
        rw [add_smul, one_smul]
        abel
      _ = _ := by rw [mul_comm b a, ← hc]

end TauCeti.MinusculeWeightTable
