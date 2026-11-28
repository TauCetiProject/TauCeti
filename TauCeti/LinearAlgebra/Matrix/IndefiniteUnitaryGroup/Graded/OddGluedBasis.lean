/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel

/-!
# The glued basis of an odd graded string

The last definite vector and the middle string vector form a two-dimensional block.
In the glued basis, the last vector is isotropic and pairs with the middle vector to `-1`.
This makes the Gram matrix unimodular even over coefficient rings in which its middle norm
is not a unit. `conjTranspose_oddGluedBasis_mul_mul` computes the form using `TauCeti.splitGram` and
`Matrix.fromBlocks`. The resulting `oddGluedGram` is unimodular by
`isUnit_det_oddGluedGram`.

The calculation follows the glued basis of `New.gradedLatticeBasis` in
`grh/src/New/UpperBound/Seesaw/AdmissibleCombinations.lean` of lsernau/grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC,
revision `72fead1`).
-/

public section

open Matrix

namespace TauCeti

variable {R X : Type*}

section
variable [MonoidWithZero R] [StarMul R] [DecidableEq X]

/-- The columns of the glued basis in split coordinates, with the middle string vector and
the last definite vector indexed by `0` and `1` in the last block. The string vectors are
scaled by `u`; the last definite vector becomes `y / star π + u z / (π * star π)`. -/
def oddGluedBasis (r : ℕ) (u : unitary R) (π : Rˣ) :
    Matrix (SplitIndex r (X ⊕ Fin 2)) (SplitIndex r (X ⊕ Fin 2)) R :=
  fromBlocks ((u : R) • 1) 0 0 (fromBlocks
    (fromBlocks 1 0 0 !![(u : R), (u : R) * (↑π⁻¹ * star (↑π⁻¹ : R));
      0, star (↑π⁻¹ : R)])
    0 0 ((u : R) • 1))

/-- Block formula for the change to the glued basis. -/
theorem oddGluedBasis_def (r : ℕ) (u : unitary R) (π : Rˣ) :
    oddGluedBasis (X := X) r u π =
      fromBlocks ((u : R) • 1) 0 0 (fromBlocks
        (fromBlocks 1 0 0 !![(u : R), (u : R) * (↑π⁻¹ * star (↑π⁻¹ : R));
          0, star (↑π⁻¹ : R)])
        0 0 ((u : R) • 1)) := (rfl)

/-- The two-by-two block of the change of basis on the glued coordinates. -/
@[simp]
theorem oddGluedBasis_apply_glued (r : ℕ) (u : unitary R) (π : Rˣ) (i j : Fin 2) :
    oddGluedBasis (X := X) r u π (.inr (.inl (.inr i))) (.inr (.inl (.inr j))) =
      !![(u : R), (u : R) * (↑π⁻¹ * star (↑π⁻¹ : R)); 0, star (↑π⁻¹ : R)] i j := (rfl)

end

/-- The Gram matrix of the odd glued basis with middle string norm `-N`, in split
coordinates. The last row and column are zero except for the pairing `-1` with the
middle string vector. -/
def oddGluedGram [Zero R] [One R] [Neg R] [DecidableEq X] (r : ℕ) (N : R) :
    Matrix (SplitIndex r (X ⊕ Fin 2)) (SplitIndex r (X ⊕ Fin 2)) R :=
  splitGram r (fromBlocks 1 0 0 !![-N, -1; -1, 0])

/-- In split coordinates the ordinary definite vectors contribute an identity block and
the two glued coordinates contribute the displayed two-by-two block. -/
theorem oddGluedGram_def [Zero R] [One R] [Neg R] [DecidableEq X] (r : ℕ) (N : R) :
    oddGluedGram (X := X) r N =
      splitGram r (fromBlocks (1 : Matrix X X R) 0 0 !![-N, -1; -1, 0]) := (rfl)

/-- The Gram entries on the middle string vector and the last definite vector. -/
@[simp]
theorem oddGluedGram_apply_glued [Zero R] [One R] [Neg R] [DecidableEq X]
    (r : ℕ) (N : R) (i j : Fin 2) :
    oddGluedGram (X := X) r N (.inr (.inl (.inr i))) (.inr (.inl (.inr j))) =
      !![-N, -1; -1, 0] i j := by rw [oddGluedGram_def, splitGram_middle_middle, fromBlocks_apply₂₂]

section

variable [CommRing R] [StarRing R] [Fintype X] [DecidableEq X]

/-- On the two glued coordinates, the normalized last vector is isotropic and its
pairing with the scaled middle vector is `-1`. -/
theorem conjTranspose_oddGluedBasis_block_mul_mul {R : Type*} [CommRing R] [StarRing R]
    (u : unitary R) (π : Rˣ) :
      (!![(u : R), (u : R) * (↑π⁻¹ * star (↑π⁻¹ : R)); 0, star (↑π⁻¹ : R)])ᴴ *
        !![-((π : R) * star (π : R)), 0; 0, 1] *
        !![(u : R), (u : R) * (↑π⁻¹ * star (↑π⁻¹ : R)); 0, star (↑π⁻¹ : R)] =
      !![-((π : R) * star (π : R)), -1; -1, 0] := by
  have hn : ((π : R) * star (π : R)) * (↑π⁻¹ * star (↑π⁻¹ : R)) = 1 := by
    have hs := (star π).mul_inv
    rw [Units.coe_star, Units.coe_star_inv] at hs
    grind [π.mul_inv]
  have hscaled : star (u : R) * ((π : R) * star (π : R)) * (u : R) =
      (π : R) * star (π : R) := by
    calc
      _ = (star (u : R) * u) * ((π : R) * star (π : R)) := by ring
      _ = _ := by rw [Unitary.coe_star_mul_self, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, conjTranspose_apply,
      of_apply, cons_val', cons_val_zero, cons_val_fin_one, Fin.sum_univ_two, cons_val_one,
      star_zero, zero_mul, add_zero, mul_neg, neg_mul, mul_zero, neg_inj, star_mul, star_star,
      mul_one, zero_add]
  · exact hscaled
  · rw [← mul_assoc, hscaled, hn]
  · linear_combination (↑π⁻¹ * star (↑π⁻¹ : R)) * hscaled + hn
  · linear_combination -(↑π⁻¹ * star (↑π⁻¹ : R)) ^ 2 * hscaled -
      (↑π⁻¹ * star (↑π⁻¹ : R)) * hn

/-- In the odd glued basis, the split hyperbolic pairs and the ordinary definite vectors
retain their Gram entries. The new last vector is isotropic and pairs to `-1` with
the middle string vector. -/
theorem conjTranspose_oddGluedBasis_mul_mul (r : ℕ) (u : unitary R) (π : Rˣ) :
    (oddGluedBasis (X := X) r u π)ᴴ *
      splitGram r (fromBlocks (1 : Matrix X X R) 0 0 !![-((π : R) * star (π : R)), 0; 0, 1]) *
      oddGluedBasis (X := X) r u π =
    oddGluedGram (X := X) r ((π : R) * star (π : R)) := by
  simp only [oddGluedBasis_def, oddGluedGram_def, splitGram_eq_fromBlocks, fromBlocks_conjTranspose,
    conjTranspose_zero, conjTranspose_one, conjTranspose_smul, fromBlocks_multiply,
    fromCols_mul_fromBlocks, fromBlocks_mul_fromRows, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, smul_mul, Matrix.mul_smul, smul_zero,
    conjTranspose_oddGluedBasis_block_mul_mul]
  congr 1
  · ext i (j | j)
    · simp
    · simp only [Matrix.smul_apply, smul_eq_mul, fromCols_apply_inr,
        ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  · ext (i | i) j
    · simp
    · have hu : (u : R) * star (u : R) = 1 := Unitary.mul_star_self_of_mem u.property
      simp only [Matrix.smul_apply, smul_eq_mul, fromRows_apply_inr, ← mul_assoc, hu, one_mul]

end

/-- The odd glued Gram matrix is Hermitian precisely when the middle norm is self-adjoint. -/
@[simp]
theorem isHermitian_oddGluedGram_iff [Ring R] [StarRing R] [DecidableEq X]
    (r : ℕ) {N : R} :
    (oddGluedGram r N : Matrix (SplitIndex r (X ⊕ Fin 2)) (SplitIndex r (X ⊕ Fin 2)) R).IsHermitian
      ↔ star N = N := by
  rw [oddGluedGram_def]
  constructor
  · intro h
    have hN := h.apply (.inr (.inl (.inr 0))) (.inr (.inl (.inr 0)))
    simpa using hN
  · intro hN
    apply isHermitian_splitGram
    refine IsHermitian.fromBlocks isHermitian_one (by simp) (IsHermitian.ext ?_)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hN]

/-- The Gram matrix of the odd glued basis is unimodular over any coefficient ring, even
when the middle norm is not a unit. -/
theorem isUnit_det_oddGluedGram [CommRing R] [Fintype X] [DecidableEq X]
    (r : ℕ) (N : R) :
    IsUnit (oddGluedGram (X := X) r N).det := by
  rw [oddGluedGram_def]
  apply isUnit_det_of_right_inverse (B := splitGram r
    (fromBlocks (1 : Matrix X X R) 0 0 !![0, -1; -1, N]))
  have h : (!![-N, -1; -1, 0] : Matrix (Fin 2) (Fin 2) R) * !![0, -1; -1, N] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [splitGram_mul_splitGram, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, add_zero, zero_add, h, fromBlocks_one]

/-- The change of basis for the odd gluing is invertible over the ring containing the
units `u` and `π`. -/
theorem isUnit_det_oddGluedBasis [CommRing R] [StarRing R] [Fintype X] [DecidableEq X]
    (r : ℕ) (u : unitary R) (π : Rˣ) : IsUnit (oddGluedBasis (X := X) r u π).det := by
  have h := isUnit_det_oddGluedGram (X := X) r ((π : R) * star (π : R))
  rw [← conjTranspose_oddGluedBasis_mul_mul r u π, det_mul] at h
  exact isUnit_of_mul_isUnit_right h

end TauCeti
