/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Graded.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Gluing an even graded string

The even glued basis fixes the definite coordinates and rescales the two halves of
the string by star-dual units. The resulting change of basis preserves the graded
Gram matrix, which has no middle entry and is unimodular for every value of `N`.

The construction follows `New.gradedLatticeBasis` and
`New.Seesaw.gram_gradedLatticeBasis_eq_gluedGram` in
`grh/src/New/UpperBound/Seesaw/AdmissibleCombinations.lean` of
grh-lean (<https://github.com/lsernau/grh-lean>, revision `72fead1`, Apache 2.0,
copyright 2026 Anthropic, PBC). It uses the diagonal basis change
`TauCeti.diagGL` and the reversal pairing of `TauCeti.gradedGram`.
-/

public section

open Matrix

namespace TauCeti

variable {R X : Type*} [DecidableEq X]

/-- In the glued basis for a string of length `2 * r`, the definite block is unchanged.
The first half of the string is scaled by `u * a⁻¹` and the second by `u * star a`. -/
def evenGluedBasis [Semiring R] [StarMul R] [Fintype X] (r : ℕ) (u : unitary R) (a : Rˣ) :
    GL (X ⊕ Fin (2 * r)) R :=
  diagGL fun
    | .inl _ => 1
    | .inr i => Unitary.toUnits u * (if (i : ℕ) < r then a⁻¹ else star a)

/-- The columns of the even glued basis are the indicated rescalings of the coordinate basis. -/
@[simp] theorem evenGluedBasis_val [Semiring R] [StarMul R] [Fintype X]
    (r : ℕ) (u : unitary R) (a : Rˣ) :
    (evenGluedBasis (X := X) r u a).val = diagonal (fun
      | .inl _ => 1
      | .inr i => (u : R) * (if (i : ℕ) < r then ↑a⁻¹ else star (a : R))) := by
  rw [evenGluedBasis, diagGL_coe]
  congr 1
  funext i
  rcases i with x | i
  · rfl
  · by_cases hi : (i : ℕ) < r <;> simp [hi]

/-- The even glued basis has the original graded Gram matrix. The scalars on paired
string coordinates cancel after taking the star in the first coordinate. -/
theorem conjTranspose_evenGluedBasis_mul_gradedGram_mul [Ring R] [StarRing R] [Fintype X]
    (r : ℕ) (u : unitary R) (a : Rˣ) (N : R) :
    (evenGluedBasis (X := X) r u a).valᴴ * gradedGram X (2 * r) N *
        (evenGluedBasis (X := X) r u a).val = gradedGram X (2 * r) N := by
  -- Use the parameter for which the string block is the reversal permutation matrix.
  have hGram : gradedGram X (2 * r) N = gradedGram X (2 * r) (-1 : R) :=
    gradedGram_eq_of_even (even_two_mul r) N (-1)
  rw [hGram, evenGluedBasis_val, diagonal_conjTranspose]
  ext i j
  simp only [mul_diagonal, diagonal_mul, Pi.star_apply]
  rcases i with x | i <;> rcases j with y | j
  · simp
  · simp
  · simp
  · by_cases hij : i.rev = j
    · subst j
      have hhalf : (i.rev : ℕ) < r ↔ ¬ (i : ℕ) < r := by grind
      have hu : star (u : R) * (u : R) = 1 := Unitary.star_mul_self_of_mem u.property
      have cancel (b c : R) : (b * star (u : R)) * (u * c) = b * c := by
        rw [mul_assoc, ← mul_assoc (star (u : R)), hu, one_mul]
      simp only [gradedGram_inr_inr, neg_neg, ite_self, hhalf, star_mul]
      by_cases hi : (i : ℕ) < r
      · simp only [hi, ite_true, not_true_eq_false, ite_false, mul_one, cancel]
        rw [← Units.coe_star_inv, ← Units.coe_star, Units.inv_mul]
      · simp only [hi, ite_false, not_false_eq_true, ite_true, star_star, mul_one, cancel,
          Units.mul_inv]
    · simp only [gradedGram_inr_inr, ite_eq_right hij, mul_zero, zero_mul]

end TauCeti
