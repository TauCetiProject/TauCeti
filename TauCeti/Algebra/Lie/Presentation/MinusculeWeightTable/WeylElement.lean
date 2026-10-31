/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
import TauCeti.Algebra.Lie.Sl2.SquareZero

/-!
# Simple Weyl representatives on a minuscule weight basis

The word `(1 + Eᵢ) * (1 - Fᵢ) * (1 + Eᵢ)` exchanges each two-element reflection
orbit, with one negative sign. Its square is diagonal, acting by `-1` on those
orbits and by `1` on the fixed weights. The calculation holds over every
commutative ring, including characteristic two.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)
variable [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R]

/-- The simple Weyl representative as a word in raising and lowering unipotents. -/
def weylMatrix (i : B) : Matrix ι ι R :=
  (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) *
    (1 - (T.loweringMatrix i).map (Int.cast : ℤ → R)) *
    (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R))

/-- The defining product of the simple Weyl matrix. -/
theorem weylMatrix_def (i : B) :
    T.weylMatrix R i =
      (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) *
        (1 - (T.loweringMatrix i).map (Int.cast : ℤ → R)) *
        (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) := by
  rw [weylMatrix]

omit [Fintype ι] [DecidableEq ι] in
private theorem reflection_eq_self_of_weight_eq_zero (i : B) (a : ι)
    (h : T.weight a i = 0) : T.reflection i a = a := by
  apply T.weight_injective
  funext j
  simp [T.weight_reflection, h]

private theorem raising_mul_lowering_mul_raising (i : B) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) *
        (T.loweringMatrix i).map (Int.cast : ℤ → R) *
        (T.raisingMatrix i).map (Int.cast : ℤ → R) =
      (T.raisingMatrix i).map (Int.cast : ℤ → R) := by
  ext a b
  have h : ((T.raisingMatrix i).map (Int.cast : ℤ → R) *
        (T.loweringMatrix i).map (Int.cast : ℤ → R) *
        (T.raisingMatrix i).map (Int.cast : ℤ → R)) *ᵥ Pi.single b 1 =
      (T.raisingMatrix i).map (Int.cast : ℤ → R) *ᵥ Pi.single b 1 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases hb : T.weight b i = -1 <;> simp [hb]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h a

private theorem weylMatrix_eq (i : B) :
    T.weylMatrix R i =
      1 + (T.raisingMatrix i).map (Int.cast : ℤ → R) -
        (T.loweringMatrix i).map (Int.cast : ℤ → R) -
        (T.raisingMatrix i).map (Int.cast : ℤ → R) *
          (T.loweringMatrix i).map (Int.cast : ℤ → R) -
        (T.loweringMatrix i).map (Int.cast : ℤ → R) *
          (T.raisingMatrix i).map (Int.cast : ℤ → R) := by
  have hEE : (T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix i).map (Int.cast : ℤ → R) = 0 := by
    calc
      _ = ((T.raisingMatrix i) ^ 2).map (Int.castRingHom R) := by
        rw [pow_two, Matrix.map_mul]
        rfl
      _ = 0 := by rw [T.raisingMatrix_pow_two]; simp
  simpa only [weylMatrix, one_smul, neg_one_smul, sub_eq_add_neg] using
    (Sl2.triple_product_of_mul_self_eq_zero hEE
      (T.raising_mul_lowering_mul_raising R i) (α := (1 : R)) (β := -1) (by simp))

/-- On a coordinate vector, the Weyl word is its reflection, with a negative sign
exactly at a weight whose simple-coroot coordinate is `1`. -/
theorem weylMatrix_mulVec_single (i : B) (a : ι) :
    T.weylMatrix R i *ᵥ Pi.single a 1 =
      if T.weight a i = 1 then -Pi.single (T.reflection i a) 1
      else Pi.single (T.reflection i a) 1 := by
  rw [T.weylMatrix_eq]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec]
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
  · simp [h]
  · have hr := T.reflection_eq_self_of_weight_eq_zero i a h
    simp [h, hr]
  · simp [h]

/-- Each column of a simple Weyl representative is its signed reflected coordinate vector. -/
@[simp]
theorem weylMatrix_col (i : B) (a : ι) :
    (T.weylMatrix R i).col a =
      if T.weight a i = 1 then -Pi.single (T.reflection i a) 1
      else Pi.single (T.reflection i a) 1 := by
  simpa only [Matrix.mulVec_single_one] using T.weylMatrix_mulVec_single R i a

/-- Squaring a simple Weyl representative gives the sign on each reflection orbit. -/
@[simp]
theorem weylMatrix_pow_two (i : B) :
    T.weylMatrix R i ^ 2 =
      Matrix.diagonal (fun a ↦ if T.weight a i = 0 then (1 : R) else -1) := by
  apply Matrix.ext
  intro a b
  have hvec : (T.weylMatrix R i ^ 2) *ᵥ Pi.single b 1 =
      (if T.weight b i = 0 then (1 : R) else -1) • Pi.single b 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, T.weylMatrix_mulVec_single]
    rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
    · simp [hb, T.weylMatrix_mulVec_single]
    · simp [hb, T.weylMatrix_mulVec_single]
    · simp [hb, Matrix.mulVec_neg, T.weylMatrix_mulVec_single]
  have h := congrFun hvec a
  by_cases hab : a = b
  · subst b
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using h
  · simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply,
      Matrix.diagonal_apply, hab, Ne.symm hab] using h

end TauCeti.MinusculeWeightTable
