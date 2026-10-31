/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Swap
import TauCeti.Analysis.Matrix.LDL

/-!
# Cholesky factors of positive-definite real matrices

This file constructs the lower-triangular Cholesky factor of a positive-definite real matrix
from Mathlib's LDL decomposition.  The diagonal of the LDL factor is positive, so taking its
entrywise square root and absorbing it into the lower factor gives `S = L * Lᵀ`, with `L` lower
triangular and positive on the diagonal.

## Main definitions

* `TauCeti.PosDiagLowerTriangular` is the space of lower-triangular real matrices with positive
  diagonal.
* `TauCeti.cholesky` constructs the Cholesky factor of a positive-definite matrix, and
  `TauCeti.cholesky_coe` gives its closed form in terms of the LDL decomposition.
* `TauCeti.cholesky_mul_transpose` proves the Cholesky reconstruction identity.
* `Matrix.PosDef.exists_generalLinearGroup_mul_transpose_eq_and_apply_eq_zero` factors a
  positive-definite matrix as `C * Cᵀ` with `C` invertible and a prescribed row of `C`
  supported on a single entry.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.2.
-/

-- The declaration names and signatures of the Cholesky API below follow the skeleton pinned in
-- `TauCetiRoadmap/StandardDistributions/Suggested.lean`, section "Cholesky coordinates".

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- Lower-triangular real matrices of size `p` whose diagonal entries are positive. -/
abbrev PosDiagLowerTriangular (p : ℕ) :=
  {L : Matrix (Fin p) (Fin p) ℝ // L.IsLowerTriangular ∧ ∀ i, 0 < L i i}

namespace Matrix

variable {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)

private noncomputable def choleskyFactor : Matrix (Fin p) (Fin p) ℝ :=
  LDL.lower hS * Matrix.diagonal fun i ↦ Real.sqrt (LDL.diagEntries hS i)

private theorem choleskyFactor_isLowerTriangular : (choleskyFactor hS).IsLowerTriangular :=
  (LDL.isLowerTriangular_lower hS).mul (Matrix.blockTriangular_diagonal _)

private theorem choleskyFactor_diag_pos (i : Fin p) : 0 < choleskyFactor hS i i := by
  rw [choleskyFactor, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simpa [LDL.lower_apply_diag hS i] using
      Real.sqrt_pos.2 (LDL.diagEntries_pos hS i)
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ hji, mul_zero]
  · simp

private theorem diagonal_sqrt_mul_self :
    Matrix.diagonal (fun i ↦ Real.sqrt (LDL.diagEntries hS i)) *
        Matrix.diagonal (fun i ↦ Real.sqrt (LDL.diagEntries hS i)) =
      LDL.diag hS := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, LDL.diag]
    rw [← sq]
    exact Real.sq_sqrt (LDL.diagEntries_pos hS i).le
  · simp [LDL.diag, hij]

private theorem choleskyFactor_mul_transpose :
    choleskyFactor hS * (choleskyFactor hS)ᵀ = S := by
  rw [choleskyFactor, Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (LDL.lower hS), diagonal_sqrt_mul_self]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using LDL.lower_conj_diag hS

end Matrix

/-- The lower-triangular Cholesky factor of a positive-definite real symmetric matrix. -/
noncomputable def cholesky {p : ℕ} (A : PosDefMatrix p) : PosDiagLowerTriangular p :=
  ⟨Matrix.choleskyFactor A.2,
    Matrix.choleskyFactor_isLowerTriangular A.2,
    Matrix.choleskyFactor_diag_pos A.2⟩

/-- The Cholesky factor of `A` in closed form: Mathlib's LDL lower factor of `A`, with the
square roots of the LDL diagonal entries absorbed into its columns. -/
theorem cholesky_coe {p : ℕ} (A : PosDefMatrix p) :
    (cholesky A).1 =
      LDL.lower A.2 * Matrix.diagonal fun i ↦ Real.sqrt (LDL.diagEntries A.2 i) :=
  (rfl)

/-- A positive-definite matrix is the product of its Cholesky factor and its transpose. -/
@[simp]
theorem cholesky_mul_transpose {p : ℕ} (A : PosDefMatrix p) :
    (cholesky A).1 * ((cholesky A).1)ᵀ =
      (A.1 : Matrix (Fin p) (Fin p) ℝ) :=
  Matrix.choleskyFactor_mul_transpose A.2

/-- A lower-triangular matrix with positive diagonal has linearly independent rows. -/
theorem PosDiagLowerTriangular.vecMul_injective {p : ℕ} (L : PosDiagLowerTriangular p) :
    Function.Injective L.1.vecMul := by
  apply Matrix.vecMul_injective_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isLowerTriangular L.1 L.2.1]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ (L.2.2 i).ne'

/-- Reconstruct a positive-definite symmetric matrix from a lower-triangular matrix with positive
diagonal. -/
noncomputable def choleskyReconstruction {p : ℕ} (L : PosDiagLowerTriangular p) :
    PosDefMatrix p := by
  refine ⟨⟨L.1 * L.1ᵀ, ?_⟩, ?_⟩
  · have h := Matrix.isHermitian_mul_conjTranspose_self L.1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp h
  · have h := Matrix.PosDef.mul_conjTranspose_self L.1 L.vecMul_injective
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The matrix underlying `choleskyReconstruction L` is `L * Lᵀ`. -/
@[simp]
theorem choleskyReconstruction_coe {p : ℕ} (L : PosDiagLowerTriangular p) :
    ((choleskyReconstruction L).1 : Matrix (Fin p) (Fin p) ℝ) = L.1 * L.1ᵀ := by
  rw [choleskyReconstruction]

/-- Reconstructing a matrix from its Cholesky factor returns the original matrix. -/
@[simp]
theorem choleskyReconstruction_cholesky {p : ℕ} (A : PosDefMatrix p) :
    choleskyReconstruction (cholesky A) = A := by
  apply Subtype.ext
  apply Subtype.ext
  exact cholesky_mul_transpose A

/-- The Cholesky construction is injective. -/
theorem cholesky_injective {p : ℕ} : Function.Injective (@cholesky p) :=
  Function.LeftInverse.injective fun A ↦ choleskyReconstruction_cholesky A

end TauCeti

namespace Matrix.PosDef

open TauCeti

variable {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- A positive-definite matrix factors as `C * Cᵀ` with `C` invertible and with the `i`-th row of
`C` vanishing off a single column `j`. -/
theorem exists_generalLinearGroup_mul_transpose_eq_and_apply_eq_zero (hS : S.PosDef)
    (i : Fin p) :
    ∃ (C : Matrix.GeneralLinearGroup (Fin p) ℝ) (j : Fin p),
      (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = S ∧
        ∀ a, a ≠ j → (C : Matrix (Fin p) (Fin p) ℝ) i a = 0 := by
  -- Swap the indices `i` and `0`, take the Cholesky factor, whose first row is supported on its
  -- first entry, and swap back to move that row to position `i`.
  set j : Fin p := ⟨0, i.pos⟩
  set P : Matrix (Fin p) (Fin p) ℝ := Matrix.swap ℝ i j with hPdef
  have hPP : P * P = 1 := Matrix.swap_mul_self i j
  have hPt : Pᵀ = P := Matrix.transpose_swap i j
  have hPS : (P * S * P).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hPt] using
      hS.mul_mul_conjTranspose_same
        (Matrix.vecMul_injective_iff_isUnit.2 ⟨⟨P, P, hPP, hPP⟩, rfl⟩)
  let A : PosDefMatrix p := ⟨⟨P * S * P, Matrix.isHermitian_iff_isSelfAdjoint.1 hPS.1⟩, hPS⟩
  set L : Matrix (Fin p) (Fin p) ℝ := (cholesky A).1
  have hL : L * Lᵀ = P * S * P := cholesky_mul_transpose A
  have hC : P * L * (P * L)ᵀ = S := by
    calc P * L * (P * L)ᵀ = P * (L * Lᵀ) * P := by
          rw [Matrix.transpose_mul, hPt, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (P * P) * S * (P * P) := by rw [hL]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  have hdet : (P * L).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hC
    rw [Matrix.det_mul, Matrix.det_transpose, h, zero_mul] at this
    exact hS.det_pos.ne' this.symm
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero (P * L) hdet
  have hcoe : (C : Matrix (Fin p) (Fin p) ℝ) = P * L := rfl
  refine ⟨C, j, hcoe ▸ hC, fun a ha ↦ ?_⟩
  -- the `i`-th row of `P * L` is the first row of the lower-triangular `L`
  have hja : j < a := Fin.lt_def.2 (Nat.pos_of_ne_zero fun h ↦ ha (Fin.ext h))
  rw [hcoe, hPdef, Matrix.swap_mul_apply_left]
  exact (cholesky A).2.1 (by simpa using hja)

end Matrix.PosDef
