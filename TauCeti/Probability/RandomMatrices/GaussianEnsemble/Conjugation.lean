/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Measure
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates

/-!
# Conjugation of the Gaussian ensembles acts orthogonally on their coordinates

The matrix `TauCeti.Probability.gaussianEnsemble β n g` is built from an array
`g : Fin n × Fin n → ℝ` of real coordinates. Orthogonal conjugation `A ↦ U * A * Uᵀ` of the real
symmetric ensemble (`β = 1`) and unitary conjugation `A ↦ U * A * Uᴴ` of the complex Hermitian
ensemble (`β ≠ 1`) are linear isometries of the underlying real inner-product space, so they act on
the coordinates by orthogonal matrices of `Fin n × Fin n`:

* `gueConjMatrix n U` is the matrix of unitary conjugation by `U` in
  `TauCeti.hermitianOrthonormalBasis n`, and
  `gaussianEnsemble β n (gueConjMatrix n U *ᵥ g) = U * gaussianEnsemble β n g * Uᴴ` for `β ≠ 1`;
* `goeConjMatrix n U` acts on the upper-triangular coordinates by the matrix of orthogonal
  conjugation by `U` in `TauCeti.symmetricOrthonormalBasis n`, and fixes the strictly
  lower-triangular coordinates, which the real symmetric ensemble does not read; then
  `gaussianEnsemble 1 n (goeConjMatrix n U *ᵥ g)` is the conjugate of `gaussianEnsemble 1 n g`
  by `U`.

Both matrices lie in `Matrix.orthogonalGroup (Fin n × Fin n) ℝ`. Since an orthogonal matrix maps
independent standard Gaussian coordinates, or independent Brownian coordinates, to independent
ones of the same kind, this is the coordinate form of the conjugation invariance of the GOE, the
GUE and matrix Brownian motion.

## Main definitions

* `TauCeti.Probability.goeConjMatrix`, `TauCeti.Probability.gueConjMatrix`.

## Main results

* `TauCeti.Probability.goeConjMatrix_mem_orthogonalGroup`,
  `TauCeti.Probability.gueConjMatrix_mem_orthogonalGroup`: the matrices are orthogonal.
* `TauCeti.Probability.goeMatrix_goeConjMatrix_mulVec`,
  `TauCeti.Probability.gueMatrix_gueConjMatrix_mulVec`: conjugation of `goeMatrix` and
  `gueMatrix` on the self-adjoint subspaces.
* `TauCeti.Probability.gaussianEnsemble_one_goeConjMatrix_mulVec`,
  `TauCeti.Probability.gaussianEnsemble_gueConjMatrix_mulVec_of_ne_one`: the same for the ambient
  complex matrices.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.1 and §4.3.1.
-/

public section

noncomputable section

open Matrix Module

namespace TauCeti.Probability

variable {n : ℕ}

/-! ### Unitary conjugation of the complex Hermitian ensemble -/

/-- The matrix by which unitary conjugation `A ↦ U * A * Uᴴ` acts on the coordinates of the
complex Hermitian ensemble: the change-of-basis matrix from `TauCeti.hermitianOrthonormalBasis n`
to its image under conjugation by `U`. -/
def gueConjMatrix (n : ℕ) (U : unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  (hermitianOrthonormalBasis n).toBasis.toMatrix
    ((hermitianOrthonormalBasis n).map (UnitaryGroup.hermitianConj U))

/-- The `(kl, ij)` entry of `gueConjMatrix n U` is the `kl`-coordinate of the conjugate of the
`ij`-th vector of `TauCeti.hermitianOrthonormalBasis n`. -/
theorem gueConjMatrix_apply (U : unitaryGroup (Fin n) ℂ) (kl ij : Fin n × Fin n) :
    gueConjMatrix n U kl ij = (hermitianOrthonormalBasis n).repr
      (UnitaryGroup.hermitianConj U (hermitianOrthonormalBasis n ij)) kl := by
  rw [gueConjMatrix, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.map_apply]

/-- `gueConjMatrix n U` is an orthogonal matrix. -/
theorem gueConjMatrix_mem_orthogonalGroup (U : unitaryGroup (Fin n) ℂ) :
    gueConjMatrix n U ∈ orthogonalGroup (Fin n × Fin n) ℝ :=
  OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal _ _

/-- Unitary conjugation of `gueMatrix n g` is `gueMatrix` of the coordinates transformed by
`gueConjMatrix n U`. -/
theorem gueMatrix_gueConjMatrix_mulVec (U : unitaryGroup (Fin n) ℂ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n (gueConjMatrix n U *ᵥ g) = UnitaryGroup.hermitianConj U (gueMatrix n g) := by
  rw [gueMatrix_eq_smul_sum_orthonormalBasis, gueMatrix_eq_smul_sum_orthonormalBasis, map_smul,
    OrthonormalBasis.map_sum_smul]
  simp_rw [mulVec, dotProduct, gueConjMatrix_apply]

/-- **Unitary conjugation of the complex Hermitian ensemble** (`β ≠ 1`): conjugating
`gaussianEnsemble β n g` by a unitary `U` gives the ensemble of the coordinates transformed by
the orthogonal matrix `gueConjMatrix n U`. -/
theorem gaussianEnsemble_gueConjMatrix_mulVec_of_ne_one {β : ℕ} (hβ : β ≠ 1)
    (U : unitaryGroup (Fin n) ℂ) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (gueConjMatrix n U *ᵥ g) =
      (U : Matrix (Fin n) (Fin n) ℂ) * gaussianEnsemble β n g *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  rw [gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one hβ,
    gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one hβ, ← coe_gueMatrix, ← coe_gueMatrix,
    gueMatrix_gueConjMatrix_mulVec, UnitaryGroup.coe_hermitianConj_apply]

/-! ### Orthogonal conjugation of the real symmetric ensemble -/

/-- The matrix by which orthogonal conjugation `A ↦ U * A * Uᵀ` acts on the coordinates of the
real symmetric ensemble. On the upper-triangular coordinates `(i, j)`, `i ≤ j`, it is the
change-of-basis matrix from `TauCeti.symmetricOrthonormalBasis n` to its image under conjugation
by `U`; it fixes the strictly lower-triangular coordinates, which the ensemble does not read. -/
def goeConjMatrix (n : ℕ) (U : orthogonalGroup (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  (fromBlocks ((symmetricOrthonormalBasis n).toBasis.toMatrix
      ((symmetricOrthonormalBasis n).map (UnitaryGroup.symmetricConj U))) 0 0 1).submatrix
    (Equiv.sumCompl fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2).symm
    (Equiv.sumCompl fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2).symm

/-- `goeConjMatrix n U` is an orthogonal matrix. -/
theorem goeConjMatrix_mem_orthogonalGroup (U : orthogonalGroup (Fin n) ℝ) :
    goeConjMatrix n U ∈ orthogonalGroup (Fin n × Fin n) ℝ := by
  refine submatrix_equiv_mem_unitary.2 ((mem_orthogonalGroup_iff _ _).2 ?_)
  simp [fromBlocks_transpose, fromBlocks_multiply,
    (mem_orthogonalGroup_iff _ _).1
      (OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal _ _)]

/-- On an upper-triangular coordinate, `goeConjMatrix n U` acts by the matrix of conjugation by
`U` in `TauCeti.symmetricOrthonormalBasis n`. -/
theorem goeConjMatrix_mulVec_apply_upperTriangle (U : orthogonalGroup (Fin n) ℝ)
    (g : Fin n × Fin n → ℝ) (ij : upperTriangle n) :
    (goeConjMatrix n U *ᵥ g) ij = ∑ kl : upperTriangle n, (symmetricOrthonormalBasis n).repr
      (UnitaryGroup.symmetricConj U (symmetricOrthonormalBasis n kl)) ij * g kl := by
  rw [goeConjMatrix, submatrix_mulVec_equiv, Function.comp_apply,
    Equiv.sumCompl_symm_apply_pos ij, fromBlocks_mulVec]
  simp [mulVec, dotProduct, Basis.toMatrix_apply]

/-- `goeConjMatrix n U` fixes the strictly lower-triangular coordinates. -/
@[simp] theorem goeConjMatrix_mulVec_apply_of_gt (U : orthogonalGroup (Fin n) ℝ)
    (g : Fin n × Fin n → ℝ) {i j : Fin n} (h : j < i) :
    (goeConjMatrix n U *ᵥ g) (i, j) = g (i, j) := by
  rw [goeConjMatrix, submatrix_mulVec_equiv, Function.comp_apply,
    Equiv.sumCompl_symm_apply_of_neg (p := fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2) h.not_ge,
    fromBlocks_mulVec]
  simp

/-- Orthogonal conjugation of `goeMatrix n g` is `goeMatrix` of the coordinates transformed by
`goeConjMatrix n U`. -/
theorem goeMatrix_goeConjMatrix_mulVec (U : orthogonalGroup (Fin n) ℝ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n (goeConjMatrix n U *ᵥ g) = UnitaryGroup.symmetricConj U (goeMatrix n g) := by
  rw [goeMatrix_eq_smul_sum_orthonormalBasis, goeMatrix_eq_smul_sum_orthonormalBasis, map_smul,
    OrthonormalBasis.map_sum_smul]
  simp_rw [goeConjMatrix_mulVec_apply_upperTriangle]

/-- **Orthogonal conjugation of the real symmetric ensemble** (`β = 1`): conjugating
`gaussianEnsemble 1 n g` by a real orthogonal `U` gives the ensemble of the coordinates
transformed by the orthogonal matrix `goeConjMatrix n U`. -/
theorem gaussianEnsemble_one_goeConjMatrix_mulVec (U : orthogonalGroup (Fin n) ℝ)
    (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble 1 n (goeConjMatrix n U *ᵥ g) =
      (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * gaussianEnsemble 1 n g *
        ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ := by
  rw [← map_ofReal_coe_goeMatrix n (goeConjMatrix n U *ᵥ g), ← map_ofReal_coe_goeMatrix n g,
    goeMatrix_goeConjMatrix_mulVec,
    UnitaryGroup.coe_symmetricConj_apply]
  ext i j
  simp [-map_ofReal_coe_goeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

end TauCeti.Probability
