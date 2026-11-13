/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.SpecialFunctions.Complex.Arctan

/-!
# The Cayley transform of a Hermitian matrix

The **Cayley transform** of a square complex matrix `A` is `(1 + i A) (1 - i A)⁻¹`
(`Matrix.cayley`). For a Hermitian matrix `A` both factors are invertible, since the eigenvalues
of `A` are real (`Matrix.IsHermitian.isUnit_det_one_add_I_smul`), and the Cayley transform is
unitary (`Matrix.IsHermitian.cayley_mem_unitaryGroup`). It commutes with conjugation by an
invertible matrix (`Matrix.cayley_conj`), and on a real diagonal matrix it is the diagonal matrix
of the Cayley transforms of the entries; for a real number `x`,
`(1 + i x) / (1 - i x) = e^{2 i arctan x}` (`Complex.one_add_mul_I_div_one_sub_mul_I_eq_exp`).

For a real symmetric matrix `A`, the Cayley transform is the Souriau map `U Uᵀ` of any unitary
frame `U` of the Lagrangian graph `{x + i A x}` of `A` in `ℂⁿ`, which is how the Maslov index of
paths of graphs is computed (`TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization`). Its
determinant is `z / conj z` for `z = det (1 + i A)` (`Matrix.IsHermitian.det_cayley`).

## Main definitions

* `Matrix.cayley`: the Cayley transform `(1 + i A) (1 - i A)⁻¹`.

## Main results

* `Matrix.IsHermitian.isUnit_det_one_add_I_smul`, `Matrix.IsHermitian.isUnit_det_one_sub_I_smul`:
  `1 ± i A` is invertible for Hermitian `A`.
* `Matrix.IsHermitian.cayley_mul_one_sub_I_smul`: the characterization
  `cayley A * (1 - i A) = 1 + i A`.
* `Matrix.cayley_eq_inv_mul`: the factors may be taken in either order.
* `Matrix.IsHermitian.cayley_mem_unitaryGroup`: the Cayley transform of a Hermitian matrix is
  unitary.
* `Matrix.cayley_conj`: naturality under conjugation.
* `Matrix.cayley_diagonal_ofReal`: the Cayley transform of a real diagonal matrix.
* `Matrix.IsHermitian.det_cayley`: the determinant of the Cayley transform.

## References

* A. Cayley, *Sur quelques propriétés des déterminants gauches*, J. Reine Angew. Math. **32**
  (1846), 119–123.
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117–148.
-/

public section

open Complex

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Cayley transform** `(1 + i A) (1 - i A)⁻¹` of a square complex matrix. For a Hermitian
matrix it is unitary (`Matrix.IsHermitian.cayley_mem_unitaryGroup`). -/
noncomputable def cayley (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 + I • A) * (1 - I • A)⁻¹

theorem cayley_def (A : Matrix n n ℂ) : cayley A = (1 + I • A) * (1 - I • A)⁻¹ :=
  (rfl)

@[simp]
theorem cayley_zero : cayley (0 : Matrix n n ℂ) = 1 := by
  simp [cayley]

/-- **Naturality of the Cayley transform.** Conjugating by an invertible matrix `P`, with inverse
`Q`, commutes with the Cayley transform. -/
theorem cayley_conj {P Q : Matrix n n ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (A : Matrix n n ℂ) : cayley (P * A * Q) = P * cayley A * Q := by
  have hconj (s : ℂ) : 1 + s • (P * A * Q) = P * (1 + s • A) * Q := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.mul_smul, Matrix.smul_mul]
  have hinv (B : Matrix n n ℂ) : (P * B * Q)⁻¹ = P * B⁻¹ * Q := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_eq_left_inv hPQ, inv_eq_left_inv hQP,
      Matrix.mul_assoc]
  have hneg : 1 - I • (P * A * Q) = 1 + (-I) • (P * A * Q) := by rw [neg_smul, sub_eq_add_neg]
  rw [cayley, cayley, hconj, hneg, hconj, hinv, neg_smul, ← sub_eq_add_neg]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]

/-- The Cayley transform of a real diagonal matrix is the diagonal matrix of the points
`e^{2 i arctan dⱼ}` of the circle. -/
theorem cayley_diagonal_ofReal (d : n → ℝ) :
    cayley (diagonal fun j => (d j : ℂ)) =
      diagonal fun j => exp (↑(2 * Real.arctan (d j)) * I) := by
  have hdiag (s : ℂ) : 1 + s • diagonal (fun j => (d j : ℂ)) = diagonal fun j => 1 + s * d j := by
    simp [← diagonal_one, ← diagonal_add, ← diagonal_smul, Pi.smul_def]
  have hneg : 1 - I • diagonal (fun j => (d j : ℂ)) = 1 + (-I) • diagonal fun j => (d j : ℂ) := by
    rw [neg_smul, sub_eq_add_neg]
  have hne (j : n) : 1 + -I * (d j : ℂ) ≠ 0 := fun h => by simpa using congrArg re h
  have hinv : (diagonal fun j => 1 + -I * (d j : ℂ))⁻¹ =
      diagonal fun j => (1 + -I * (d j : ℂ))⁻¹ :=
    inv_eq_right_inv <| by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      simp_rw [mul_inv_cancel₀ (hne _)]
  rw [cayley, hneg, hdiag, hdiag, hinv, diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← div_eq_mul_inv, neg_mul, ← sub_eq_add_neg, mul_comm I,
    Complex.one_add_mul_I_div_one_sub_mul_I_eq_exp]

/-- The factors `1 + i A` and `1 - i A` of the Cayley transform commute. -/
theorem commute_one_add_I_smul_one_sub_I_smul (A : Matrix n n ℂ) :
    Commute (1 + I • A) (1 - I • A) :=
  ((Commute.one_left _).add_left ((Commute.one_right _).smul_left I)).sub_right
    (((Commute.one_left _).smul_right I).add_left ((Commute.refl A).smul_left I |>.smul_right I))

/-- The two factors of the Cayley transform may be taken in either order:
`(1 + i A) (1 - i A)⁻¹ = (1 - i A)⁻¹ (1 + i A)`. -/
theorem cayley_eq_inv_mul (A : Matrix n n ℂ) : cayley A = (1 - I • A)⁻¹ * (1 + I • A) := by
  by_cases hY : IsUnit (1 - I • A).det
  · calc cayley A = (1 - I • A)⁻¹ * ((1 - I • A) * (1 + I • A)) * (1 - I • A)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hY, Matrix.one_mul, cayley]
      _ = (1 - I • A)⁻¹ * (1 + I • A) := by
          rw [← (commute_one_add_I_smul_one_sub_I_smul A).eq, Matrix.mul_assoc, Matrix.mul_assoc,
            mul_nonsing_inv _ hY, Matrix.mul_one]
  · rw [cayley, nonsing_inv_apply_not_isUnit _ hY, Matrix.mul_zero, Matrix.zero_mul]

namespace IsHermitian

variable {A : Matrix n n ℂ}

/-- For a Hermitian matrix `A`, the matrix `1 - i A` is invertible: its eigenvalues `1 - i λ`
have real part `1`. -/
theorem isUnit_det_one_sub_I_smul (hA : A.IsHermitian) : IsUnit (det (1 - I • A)) := by
  rw [hA.det_one_sub_smul, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro j _ h
  simpa using congrArg re h

/-- For a Hermitian matrix `A`, the matrix `1 + i A` is invertible. -/
theorem isUnit_det_one_add_I_smul (hA : A.IsHermitian) : IsUnit (det (1 + I • A)) := by
  rw [← sub_neg_eq_add, ← smul_neg]
  exact hA.neg.isUnit_det_one_sub_I_smul

/-- For a Hermitian matrix `A`, `det (1 - i A)` is the complex conjugate of `det (1 + i A)`. -/
theorem det_one_sub_I_smul (hA : A.IsHermitian) :
    det (1 - I • A) = (starRingEnd ℂ) (det (1 + I • A)) := by
  rw [← sub_neg_eq_add, ← neg_smul, hA.det_one_sub_smul, hA.det_one_sub_smul, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [sub_eq_add_neg]

/-- **The Cayley transform of a Hermitian matrix** `A` is characterized by
`cayley A * (1 - i A) = 1 + i A`. -/
theorem cayley_mul_one_sub_I_smul (hA : A.IsHermitian) : cayley A * (1 - I • A) = 1 + I • A := by
  rw [cayley, Matrix.mul_assoc, nonsing_inv_mul _ hA.isUnit_det_one_sub_I_smul, Matrix.mul_one]

/-- **The Cayley transform of a Hermitian matrix is unitary.** -/
theorem cayley_mem_unitaryGroup (hA : A.IsHermitian) : cayley A ∈ unitaryGroup n ℂ := by
  have hstar : star (1 + I • A) = 1 - I • A := by
    rw [star_add, star_one, star_smul, hA.star_eq, star_def, conj_I, neg_smul, sub_eq_add_neg]
  have hstarInv : star (1 - I • A)⁻¹ = (1 + I • A)⁻¹ := by
    rw [star_eq_conjTranspose, conjTranspose_nonsing_inv, ← star_eq_conjTranspose,
      ← star_star (1 + I • A), hstar]
  rw [mem_unitaryGroup_iff']
  calc star (cayley A) * cayley A
      = star (cayley A) * ((1 - I • A)⁻¹ * (1 + I • A)) :=
        congrArg (star (cayley A) * ·) (cayley_eq_inv_mul A)
    _ = (1 + I • A)⁻¹ * ((1 - I • A) * ((1 - I • A)⁻¹ * (1 + I • A))) := by
        rw [cayley_def, star_mul, hstarInv, hstar, Matrix.mul_assoc]
    _ = 1 := by
        rw [mul_nonsing_inv_cancel_left _ _ hA.isUnit_det_one_sub_I_smul,
          nonsing_inv_mul _ hA.isUnit_det_one_add_I_smul]

/-- **The determinant of the Cayley transform** of a Hermitian matrix is `z / conj z` for
`z = det (1 + i A)`. -/
theorem det_cayley (hA : A.IsHermitian) :
    det (cayley A) = det (1 + I • A) / (starRingEnd ℂ) (det (1 + I • A)) := by
  rw [cayley, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hA.det_one_sub_I_smul,
    div_eq_mul_inv]

end IsHermitian

end Matrix
