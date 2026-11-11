/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.Topology.Homotopy.Path

/-!
# The Robbin–Salamon and Conley–Zehnder indices of symplectic paths

Let `γ : [0, 1] → Sp(2n)` be a path of symplectic matrices. Its graphs
`Γ(γ t) = {(x, γ t x)}` form a path of Lagrangian subspaces of `ℝ^{2n} × ℝ^{2n}` with the
symplectic form `(-ω) ⊕ ω`, and the **Robbin–Salamon index** of `γ`
(`TauCeti.GLSymplectic.robbinSalamonIndex`) is the Maslov index of this path of graphs relative to
the diagonal `Δ = Γ(1)`. For a path starting at the identity, the **Conley–Zehnder index**
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is taken with the sign convention
`CZ(γ) = -μ_RS(Γ ∘ γ, Δ)`, in which a small positive rotation of `ℝ²` has index `-1`. This is the
grading convention of Hamiltonian Floer homology for the equation `∂s u + J (∂t u - X_H) = 0`,
whose generators are graded by `μ = -CZ`; it is the opposite of the sign in Robbin–Salamon.

The construction reduces to the Maslov index of paths of Lagrangian frames relative to `ℝⁿ`,
`Matrix.UnitaryGroup.maslovIndex`, defined by Souriau's spectral formula. In `ℂⁿ × ℂⁿ` the graph of
`A` is the image of the real points under the graph frame `Matrix.graphFrame A`
(`TauCeti/Analysis/Matrix/SymplecticGroup/Graph.lean`). The complex matrix `(graphFrame 1)ᴴ` is
`√2` times a unitary matrix and takes the diagonal to the real points. Moving the graph by it gives
the frame `G = (graphFrame 1)ᴴ (graphFrame A)`, whose Gram matrix `Gᴴ G = 2 (1 + Aᵀ A)` is real
because the graph is Lagrangian. Hence `U = G (2 (1 + Aᵀ A))^{-1/2}` is a unitary matrix with the
same image of the real points (`TauCeti.GLSymplectic.diagonalGraphFrame`,
`TauCeti.GLSymplectic.realImage_diagonalGraphFrame`). It depends continuously on `A`, and its
Souriau map `U Uᵀ` is `G (2 (1 + Aᵀ A))⁻¹ Gᵀ`
(`TauCeti.GLSymplectic.coe_souriau_diagonalGraphFrame`), equal to `1` at `A = 1`.

The index inherits the axioms of the Maslov index for paths:

* **homotopy:** it is invariant under homotopies with fixed endpoints
  (`TauCeti.GLSymplectic.robbinSalamonIndex_eq_of_homotopic`);
* **catenation:** it is additive under concatenation and changes sign under reversal
  (`TauCeti.GLSymplectic.robbinSalamonIndex_trans`, `TauCeti.GLSymplectic.robbinSalamonIndex_symm`);
* **loops:** on a loop it is twice the Maslov index of the loop of symplectic matrices
  (`TauCeti.GLSymplectic.robbinSalamonIndex_eq_two_mul_maslovIndex`), because the square of the
  determinant of `U` is, up to a constant, the determinant phase of the graph frame;
* **product:** multiplying a path from the identity pointwise by a loop `φ` at the identity adds
  `2 μ(φ)` to the Robbin–Salamon index and so changes the Conley–Zehnder index by `-2 μ(φ)`
  (`TauCeti.GLSymplectic.robbinSalamonIndex_mul`, `TauCeti.GLSymplectic.conleyZehnderIndex_mul`).
  This is how the index changes under a loop of symplectic trivializations.

For realified symmetric unitary matrices `V` the Souriau map is the block matrix
`fromBlocks V 0 0 V`. Along a path of rotations `t ↦ diag (e^{i θ_j t})` this computes the index
(`TauCeti.GLSymplectic.robbinSalamonIndex_eq_sum_of_diagonal`):
each angle contributes `⌊θ_j / 2π⌋ + ⌈θ_j / 2π⌉`, so
`CZ = -∑ j, (⌊θ_j / 2π⌋ + ⌈θ_j / 2π⌉)` (`TauCeti.GLSymplectic.conleyZehnderIndex_rotationPath`).
For instance a rotation by angles in `(0, 2π)` has index `-n`, and a rotation by angles in
`(-2π, 0)` has index `n` (`TauCeti.GLSymplectic.conleyZehnderIndex_rotationPath_of_pos`,
`TauCeti.GLSymplectic.conleyZehnderIndex_rotationPath_of_neg`). At a nondegenerate endpoint the
index is the classical odd integer `-(2 ⌊θ_j / 2π⌋ + 1)` per angle.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of graphs relative to the diagonal).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360 (the Conley–Zehnder index and its
  loop property).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the normalization by rotations).
-/

public section

open Complex Matrix
open scoped unitInterval MatrixOrder ComplexOrder ComplexConjugate

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The graph frame relative to the diagonal -/

/-- The Gram matrix `2 (1 + Aᵀ A)` of the frame `(graphFrame 1)ᴴ * graphFrame A`. -/
private noncomputable def graphGram (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (2 : ℝ) • (1 + Aᵀ * A)

private theorem posDef_graphGram (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : (graphGram A).PosDef :=
  (PosDef.one.add_posSemidef (by simpa using posSemidef_conjTranspose_mul_self A)).smul two_pos

/-- The frame `(graphFrame 1)ᴴ * graphFrame A` of the graph of `A`, moved so that the diagonal
becomes the real points. -/
private noncomputable def diagonalGraphMatrix (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (graphFrame 1)ᴴ * graphFrame A

private theorem conjTranspose_diagonalGraphMatrix_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (diagonalGraphMatrix A)ᴴ * diagonalGraphMatrix A = (graphGram A).map (↑) := by
  rw [diagonalGraphMatrix, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (graphFrame 1), graphFrame_one_mul_conjTranspose, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, conjTranspose_graphFrame_mul_graphFrame_of_mem hA, graphGram]
  ext i j
  simp [mul_add]

/-- The inverse square root `(2 (1 + Aᵀ A))^{-1/2}` of the Gram matrix. -/
private noncomputable def graphGramInvSqrt (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  graphGram A ^ (-(1 / 2) : ℝ)

private theorem transpose_graphGramInvSqrt (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphGramInvSqrt A)ᵀ = graphGramInvSqrt A := by
  have h : (graphGramInvSqrt A).IsHermitian :=
    (nonneg_iff_posSemidef.1 (CFC.rpow_nonneg (a := graphGram A))).isHermitian
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h

private theorem graphGramInvSqrt_mul_graphGramInvSqrt (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    graphGramInvSqrt A * graphGramInvSqrt A = (graphGram A)⁻¹ := by
  have hu : IsUnit (graphGram A) := (posDef_graphGram A).isUnit
  rw [graphGramInvSqrt, ← CFC.rpow_add hu, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num,
    ← CFC.inverse_eq_rpow_neg_one (posDef_graphGram A).isStrictlyPositive,
    Matrix.nonsing_inv_eq_ringInverse]

private theorem graphGramInvSqrt_mul_graphGram_mul (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    graphGramInvSqrt A * graphGram A * graphGramInvSqrt A = 1 := by
  have hu : IsUnit (graphGram A) := (posDef_graphGram A).isUnit
  calc graphGramInvSqrt A * graphGram A * graphGramInvSqrt A =
        graphGram A ^ (-(1 / 2) : ℝ) * graphGram A ^ (1 : ℝ) * graphGram A ^ (-(1 / 2) : ℝ) := by
          rw [CFC.rpow_one _ (posDef_graphGram A).posSemidef.nonneg, graphGramInvSqrt]
    _ = graphGram A ^ (-(1 / 2) + 1 + -(1 / 2) : ℝ) := by rw [CFC.rpow_add hu, CFC.rpow_add hu]
    _ = 1 := by norm_num [CFC.rpow_zero _ (posDef_graphGram A).posSemidef.nonneg]

private theorem isUnit_graphGramInvSqrt (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    IsUnit (graphGramInvSqrt A) :=
  (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse (B := graphGram A * graphGramInvSqrt A)
    (by rw [← Matrix.mul_assoc]; exact graphGramInvSqrt_mul_graphGram_mul A))

omit [DecidableEq n] in
/-- `Matrix.map_mul` for the coercion `ℝ → ℂ`, stated with the coercion rather than
`Complex.ofRealHom` so that it can be used to rewrite. -/
private theorem map_ofReal_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (M * N).map ((↑) : ℝ → ℂ) = M.map (↑) * N.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

private theorem det_diagonalGraphMatrix_ne_zero (A : GLSymplectic n ℝ) :
    (diagonalGraphMatrix ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0 := by
  rw [diagonalGraphMatrix, det_mul, det_conjTranspose]
  exact mul_ne_zero (star_ne_zero.2 (by simpa using det_graphFrame_ne_zero 1))
    (det_graphFrame_ne_zero A)

/-- The frame `(graphFrame 1)ᴴ * graphFrame A` as an invertible matrix. -/
private noncomputable def diagonalGraphGL (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero _ (det_diagonalGraphMatrix_ne_zero A)

/-- The real orthonormalization of the frame `G = (graphFrame 1)ᴴ * graphFrame A` is
`G (2 (1 + Aᵀ A))^{-1/2}`, since the Gram matrix of `G` is the real matrix `2 (1 + Aᵀ A)`. -/
private theorem coe_realOrthonormalize_diagonalGraphGL (A : GLSymplectic n ℝ) :
    (GeneralLinearGroup.realOrthonormalize (diagonalGraphGL A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphMatrix ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        (graphGramInvSqrt ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map (↑) := by
  have hG : (diagonalGraphGL A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphMatrix ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    GeneralLinearGroup.val_mkOfDetNeZero _ _
  rw [GeneralLinearGroup.coe_realOrthonormalize, hG,
    conjTranspose_diagonalGraphMatrix_mul (mem_iff_mem_symplecticGroup.1 A.2)]
  congr 3

private theorem realOrthonormalize_diagonalGraphGL_mem_unitaryGroup (A : GLSymplectic n ℝ) :
    (GeneralLinearGroup.realOrthonormalize (diagonalGraphGL A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) ∈
      unitaryGroup (n ⊕ n) ℂ := by
  set Q := graphGramInvSqrt ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hQ : (Q.map ((↑) : ℝ → ℂ))ᴴ = Q.map (↑) := by
    rw [← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
      conjTranspose_eq_transpose_of_trivial, transpose_graphGramInvSqrt]
  rw [coe_realOrthonormalize_diagonalGraphGL, mem_unitaryGroup_iff', star_eq_conjTranspose,
    conjTranspose_mul, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonalGraphMatrix _)ᴴ,
    conjTranspose_diagonalGraphMatrix_mul (mem_iff_mem_symplecticGroup.1 A.2),
    ← map_ofReal_mul, ← map_ofReal_mul, ← Matrix.mul_assoc, graphGramInvSqrt_mul_graphGram_mul]
  simp

/-- The **diagonal graph frame** of a symplectic matrix `A`: a unitary matrix whose image of the
real points of `ℂ^{n ⊕ n}` is the graph of `A` moved by `(graphFrame 1)ᴴ`, the map taking the
diagonal (the graph of `1`) to the real points (`realImage_diagonalGraphFrame`). It is the real
orthonormalization `G (Gᴴ G)^{-1/2}` (`Matrix.GeneralLinearGroup.realOrthonormalize`) of the frame
`G = (graphFrame 1)ᴴ (graphFrame A)`, which is unitary because the Gram matrix
`Gᴴ G = 2 (1 + Aᵀ A)` is real: the graph is Lagrangian. -/
noncomputable def diagonalGraphFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨_, realOrthonormalize_diagonalGraphGL_mem_unitaryGroup A⟩

private theorem coe_diagonalGraphFrame_eq (A : GLSymplectic n ℝ) :
    (diagonalGraphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphMatrix ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        (graphGramInvSqrt ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map (↑) :=
  coe_realOrthonormalize_diagonalGraphGL A

/-- The diagonal graph frame is `G (2 (1 + Aᵀ A))^{-1/2}` for
`G = (graphFrame 1)ᴴ (graphFrame A)`. -/
theorem coe_diagonalGraphFrame (A : GLSymplectic n ℝ) :
    (diagonalGraphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (graphFrame 1)ᴴ * graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        (((2 : ℝ) • (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))) ^ (-(1 / 2) : ℝ)).map (↑) :=
  coe_diagonalGraphFrame_eq A

/-- The diagonal graph frame frames the graph of `A`, moved by `(graphFrame 1)ᴴ`. -/
theorem realImage_diagonalGraphFrame (A : GLSymplectic n ℝ) :
    (diagonalGraphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (graphSubspace (A : GL (n ⊕ n) ℝ)).map
        (((toEuclideanCLM (𝕜 := ℂ) (graphFrame 1)ᴴ :
          EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) :
          EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) := by
  have h : (diagonalGraphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (GeneralLinearGroup.realOrthonormalize (diagonalGraphGL A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    rfl
  rw [h, GeneralLinearGroup.realImage_realOrthonormalize, diagonalGraphGL,
    GeneralLinearGroup.val_mkOfDetNeZero, diagonalGraphMatrix, realImage_mul, graphSubspace_def]

/-- The diagonal frame of the graph of the identity frames the real points: `(graphFrame 1)ᴴ`
takes the diagonal to the real points. -/
@[simp]
theorem realImage_diagonalGraphFrame_one :
    (diagonalGraphFrame (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      realSubspace (n ⊕ n) := by
  have h2 : IsUnit ((2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) :=
    (isUnit_iff_isUnit_det _).2 (by simp)
  rw [coe_diagonalGraphFrame_eq, realImage_mul_map_ofReal _ (isUnit_graphGramInvSqrt _),
    diagonalGraphMatrix, OneMemClass.coe_one, Units.val_one,
    conjTranspose_graphFrame_mul_graphFrame_of_mem (one_mem _), transpose_one, Matrix.one_mul,
    ← two_smul ℝ (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)]
  exact realImage_map_ofReal h2

private theorem coe_souriau_diagonalGraphFrame_eq (A : GLSymplectic n ℝ) :
    (souriau (diagonalGraphFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphMatrix (A : GL (n ⊕ n) ℝ) *
        (graphGram (A : GL (n ⊕ n) ℝ))⁻¹.map ((↑) : ℝ → ℂ) *
          (diagonalGraphMatrix (A : GL (n ⊕ n) ℝ))ᵀ := by
  rw [coe_souriau, coe_diagonalGraphFrame_eq, transpose_mul, ← transpose_map,
    transpose_graphGramInvSqrt, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.map _ _),
    ← map_ofReal_mul, graphGramInvSqrt_mul_graphGramInvSqrt, Matrix.mul_assoc]

/-- **The Souriau map of the diagonal graph frame**: for `G = (graphFrame 1)ᴴ (graphFrame A)` it
is `G (2 (1 + Aᵀ A))⁻¹ Gᵀ`. The Robbin–Salamon index of a path depends only on these matrices. -/
theorem coe_souriau_diagonalGraphFrame (A : GLSymplectic n ℝ) :
    (souriau (diagonalGraphFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (graphFrame 1)ᴴ * graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        ((2 : ℝ) • (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)))⁻¹.map ((↑) : ℝ → ℂ) *
        ((graphFrame 1)ᴴ * graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᵀ :=
  coe_souriau_diagonalGraphFrame_eq A

open scoped Matrix.Norms.L2Operator in
/-- The diagonal graph frame depends continuously on the symplectic matrix. -/
theorem continuous_diagonalGraphFrame :
    Continuous (diagonalGraphFrame : GLSymplectic n ℝ → unitaryGroup (n ⊕ n) ℂ) := by
  have hG : Continuous (diagonalGraphGL : GLSymplectic n ℝ → GL (n ⊕ n) ℂ) := by
    refine Units.isOpenEmbedding_val.continuous_iff.2 ?_
    have hA : Continuous fun A : GLSymplectic n ℝ ↦
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_const.matrix_mul ((continuous_graphFrame (n := n)).comp hA)
  exact (Units.continuous_val.comp
    (GeneralLinearGroup.continuous_realOrthonormalize hG)).subtype_mk _

/-- At the identity the Souriau map of the diagonal graph frame is `1`. -/
@[simp]
theorem souriau_diagonalGraphFrame_one :
    souriau (diagonalGraphFrame (1 : GLSymplectic n ℝ)) = 1 := by
  refine Subtype.ext ?_
  have hG : diagonalGraphMatrix (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = (2 : ℂ) • 1 := by
    rw [diagonalGraphMatrix, conjTranspose_graphFrame_mul_graphFrame_of_mem (one_mem _)]
    ext i j
    by_cases h : i = j <;> simp [h]
    norm_num
  have hP : (graphGram (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹.map ((↑) : ℝ → ℂ) = (4⁻¹ : ℂ) • 1 := by
    have h4 : graphGram (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = (4 : ℝ) • 1 := by
      rw [graphGram, transpose_one, Matrix.one_mul, smul_add, ← add_smul]
      norm_num
    rw [h4, inv_eq_left_inv (B := (4⁻¹ : ℝ) • 1) (by rw [smul_mul_smul, Matrix.one_mul]; norm_num)]
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [coe_souriau_diagonalGraphFrame_eq]
  simp only [OneMemClass.coe_one, Units.val_one, hG, hP, transpose_smul, transpose_one,
    smul_mul_smul, Matrix.one_mul]
  norm_num

/-- **The Souriau map at a realified symmetric unitary matrix.** If `V` is unitary with `Vᵀ = V`,
the Souriau map of the diagonal graph frame of its realification is `fromBlocks V 0 0 V`. -/
theorem coe_souriau_diagonalGraphFrame_ofUnitary {V : unitaryGroup n ℂ}
    (hV : (V : Matrix n n ℂ)ᵀ = V) :
    (souriau (diagonalGraphFrame (ofUnitary V)) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      fromBlocks (V : Matrix n n ℂ) 0 0 V := by
  set W : Matrix n n ℂ := (V : Matrix n n ℂ) with hW
  have hO : (W.realify)ᵀ * W.realify = 1 := by
    rw [← realify_conjTranspose, ← realify_mul, ← star_eq_conjTranspose,
      hW, UnitaryGroup.star_mul_self, realify_one]
  have hP : (graphGram W.realify)⁻¹.map ((↑) : ℝ → ℂ) = (4⁻¹ : ℂ) • 1 := by
    have h4 : graphGram W.realify = (4 : ℝ) • 1 := by
      rw [graphGram, hO, smul_add, ← add_smul]
      norm_num
    rw [h4, inv_eq_left_inv (B := (4⁻¹ : ℝ) • 1) (by rw [smul_mul_smul, Matrix.one_mul]; norm_num)]
    ext i j
    by_cases h : i = j <;> simp [h]
  have hG : diagonalGraphMatrix W.realify =
      fromBlocks (1 + W) (Complex.I • (W - 1)) (Complex.I • (1 - W)) (1 + W) := by
    rw [diagonalGraphMatrix, graphFrame_one, graphFrame_realify, fromBlocks_conjTranspose,
      fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_neg, conjTranspose_smul, star_def, conj_I]
    congr 1 <;> simp [smul_sub, smul_smul] <;> abel
  rw [coe_souriau_diagonalGraphFrame_eq, coe_ofUnitary, hP, hG, fromBlocks_transpose]
  simp only [transpose_add, transpose_one, transpose_smul, transpose_sub, hV, Matrix.mul_smul,
    Matrix.mul_one, fromBlocks_smul, fromBlocks_multiply]
  -- Blockwise, `(1 + V)² - (1 - V)² = 4 V`, and the off-diagonal blocks cancel since `V`
  -- commutes with itself.
  congr 1 <;>
  simp only [Matrix.smul_mul, smul_smul, add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul,
    Matrix.mul_one] <;>
  match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring

/-- The square of the determinant of the diagonal graph frame is the graph phase, up to the
constant factor `(graphPhase 1)⁻¹`. -/
theorem detCircle_diagonalGraphFrame_sq (A : GLSymplectic n ℝ) :
    detCircle (diagonalGraphFrame A) ^ 2 =
      (graphPhase (1 : GLSymplectic n ℝ))⁻¹ * graphPhase A := by
  set F := graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  set d := (graphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
  set r := (graphGramInvSqrt ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
  set z : ℂ := (detCircle (diagonalGraphFrame A) : ℂ)
  have hQ : ((graphGramInvSqrt ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map
      ((↑) : ℝ → ℂ)).det = r :=
    (RingHom.map_det Complex.ofRealHom _).symm
  have hz : z = conj d * F.det * r := by
    simp only [z, coe_detCircle, coe_diagonalGraphFrame_eq, diagonalGraphMatrix, det_mul,
      det_conjTranspose, hQ]
    rfl
  have hzz : z * conj z = 1 := by
    simp only [z, mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hd : d ≠ 0 := by simpa using det_graphFrame_ne_zero (1 : GLSymplectic n ℝ)
  have hF : F.det ≠ 0 := det_graphFrame_ne_zero A
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    ((isUnit_iff_isUnit_det _).1 (isUnit_graphGramInvSqrt _)).ne_zero
  have h1 : ((graphPhase (1 : GLSymplectic n ℝ) : Circle) : ℂ) = d / conj d := by
    simpa [d] using coe_graphPhase (1 : GLSymplectic n ℝ)
  refine Circle.ext ?_
  rw [Circle.coe_pow, Circle.coe_mul, Circle.coe_inv_eq_conj, h1, coe_graphPhase]
  have hconj : conj z = d * conj F.det * r := by
    rw [hz, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  -- On the unit circle `z² = z / conj z`, and the positive factor `r` cancels.
  calc z ^ 2 = z / conj z := by
        rw [eq_div_iff (fun h ↦ by simp [h] at hzz), sq, mul_assoc, hzz, mul_one]
    _ = _ := by
        rw [hconj, hz]
        simp only [map_div₀, Complex.conj_conj]
        field_simp
        ring

/-! ### The Robbin–Salamon and Conley–Zehnder indices -/

/-- The **Robbin–Salamon index** of a path `γ` of symplectic matrices: the Maslov index
(`Matrix.UnitaryGroup.maslovIndex`) of the path of its graphs relative to the diagonal, computed
in the diagonal graph frames. -/
noncomputable def robbinSalamonIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  Matrix.UnitaryGroup.maslovIndex (γ.map continuous_diagonalGraphFrame)

theorem robbinSalamonIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    robbinSalamonIndex γ = Matrix.UnitaryGroup.maslovIndex (γ.map continuous_diagonalGraphFrame) :=
  (rfl)

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices starting at the identity, in
the sign convention `CZ = -μ_RS` of Hamiltonian Floer theory, in which a small positive rotation
of `ℝ²` has index `-1` (`conleyZehnderIndex_rotationPath_of_pos`). -/
noncomputable def conleyZehnderIndex {A : GLSymplectic n ℝ} (γ : Path 1 A) : ℝ :=
  -robbinSalamonIndex γ

theorem conleyZehnderIndex_def {A : GLSymplectic n ℝ} (γ : Path 1 A) :
    conleyZehnderIndex γ = -robbinSalamonIndex γ :=
  (rfl)

/-- The constant path has Robbin–Salamon index zero. -/
@[simp]
theorem robbinSalamonIndex_refl (A : GLSymplectic n ℝ) : robbinSalamonIndex (Path.refl A) = 0 := by
  rw [robbinSalamonIndex, Path.map_refl, Matrix.UnitaryGroup.maslovIndex_refl]

/-- **Catenation.** The Robbin–Salamon index of a concatenation is the sum of the indices. -/
@[simp]
theorem robbinSalamonIndex_trans {A B C : GLSymplectic n ℝ} (γ : Path A B) (δ : Path B C) :
    robbinSalamonIndex (γ.trans δ) = robbinSalamonIndex γ + robbinSalamonIndex δ := by
  rw [robbinSalamonIndex, Path.map_trans, Matrix.UnitaryGroup.maslovIndex_trans, robbinSalamonIndex,
    robbinSalamonIndex]

/-- Reversing a path negates its Robbin–Salamon index. -/
@[simp]
theorem robbinSalamonIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    robbinSalamonIndex γ.symm = -robbinSalamonIndex γ := by
  rw [robbinSalamonIndex, ← Path.map_symm, Matrix.UnitaryGroup.maslovIndex_symm,
    robbinSalamonIndex]

/-- **Homotopy invariance.** Paths that are homotopic relative to their endpoints have the same
Robbin–Salamon index. -/
theorem robbinSalamonIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : robbinSalamonIndex γ₀ = robbinSalamonIndex γ₁ :=
  Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_diagonalGraphFrame⟩)

/-- The constant path at the identity has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl : conleyZehnderIndex (Path.refl (1 : GLSymplectic n ℝ)) = 0 := by
  rw [conleyZehnderIndex, robbinSalamonIndex_refl, neg_zero]

/-- Extending a path from the identity by a path `δ` subtracts the Robbin–Salamon index of `δ`. -/
theorem conleyZehnderIndex_trans {A B : GLSymplectic n ℝ} (γ : Path 1 A) (δ : Path A B) :
    conleyZehnderIndex (γ.trans δ) = conleyZehnderIndex γ - robbinSalamonIndex δ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, robbinSalamonIndex_trans]
  ring

/-- **Homotopy invariance** of the Conley–Zehnder index, relative to the endpoints. -/
theorem conleyZehnderIndex_eq_of_homotopic {A : GLSymplectic n ℝ} {γ₀ γ₁ : Path 1 A}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, robbinSalamonIndex_eq_of_homotopic h]

/-! ### Loops and the product formula -/

/-- **The loop axiom.** On a loop of symplectic matrices the Robbin–Salamon index of the graphs is
twice the Maslov index of the loop. -/
theorem robbinSalamonIndex_eq_two_mul_maslovIndex {A : GLSymplectic n ℝ} (γ : Path A A) :
    robbinSalamonIndex γ = 2 * maslovIndex γ := by
  have hpt (t : I) :
      (((γ.map continuous_diagonalGraphFrame).map continuous_detCircle).map (continuous_pow 2)) t =
        ((Path.refl (graphPhase (1 : GLSymplectic n ℝ))⁻¹).mul
          (γ.map continuous_graphPhase)) t := by
    simp [detCircle_diagonalGraphFrame_sq]
  have hdeg : 2 * Circle.degree ((γ.map continuous_diagonalGraphFrame).map continuous_detCircle) =
      2 * maslovIndex γ := by
    rw [← degree_map_graphPhase, ← Nat.cast_two (R := ℤ), ← Circle.degree_map_pow,
      Circle.degree_congr _ _ hpt, Circle.degree_mul, Circle.degree_refl, zero_add]
  rw [robbinSalamonIndex, Matrix.UnitaryGroup.maslovIndex_eq_two_mul_degree,
    mul_left_cancel₀ two_ne_zero hdeg]

/-- **The product formula.** Multiplying a path `ψ` from the identity pointwise by a loop `φ` at
the identity adds twice the Maslov index of `φ` to the Robbin–Salamon index. -/
theorem robbinSalamonIndex_mul {A : GLSymplectic n ℝ} (φ : Path (1 : GLSymplectic n ℝ) 1)
    (ψ : Path 1 A) :
    robbinSalamonIndex (φ.mul ψ) = 2 * maslovIndex φ + robbinSalamonIndex ψ := by
  have hcast : robbinSalamonIndex ((φ.trans ψ).cast (mul_one 1) (one_mul A)) =
      robbinSalamonIndex (φ.trans ψ) :=
    Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _ _ fun _ ↦ rfl
  rw [robbinSalamonIndex_eq_of_homotopic (Path.mul_homotopic_trans φ ψ), hcast,
    robbinSalamonIndex_trans, robbinSalamonIndex_eq_two_mul_maslovIndex]

/-- **The product formula** for the Conley–Zehnder index: multiplying a path `ψ` from the identity
pointwise by a loop `φ` at the identity changes its index by `-2 μ(φ)`. -/
theorem conleyZehnderIndex_mul {A : GLSymplectic n ℝ} (φ : Path (1 : GLSymplectic n ℝ) 1)
    (ψ : Path 1 A) :
    conleyZehnderIndex ((φ.mul ψ).cast (mul_one 1).symm (one_mul A).symm) =
      conleyZehnderIndex ψ - 2 * maslovIndex φ := by
  have hcast : robbinSalamonIndex ((φ.mul ψ).cast (mul_one 1).symm (one_mul A).symm) =
      robbinSalamonIndex (φ.mul ψ) :=
    Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _ _ fun _ ↦ rfl
  rw [conleyZehnderIndex, hcast, robbinSalamonIndex_mul, conleyZehnderIndex]
  ring

/-! ### Rotations -/

/-- **The index of a path of diagonal rotations.** If `γ t` is the realification of
`diag (e^{i θ_j t})` for continuous angles `θ_j`, the Robbin–Salamon index of `γ` is
`∑ j, (c (θ_j 1) - c (θ_j 0))` with `c θ = ⌊θ / 2π⌋ + ⌈θ / 2π⌉`: each angle counts twice the
multiples of `2π` it crosses, a multiple at an endpoint counting once. -/
theorem robbinSalamonIndex_eq_sum_of_diagonal {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, γ t = ofUnitary (unitaryTorusHom n fun j ↦ Circle.exp (θ j t))) :
    robbinSalamonIndex γ = ∑ j, ((((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ)) : ℝ) -
      (((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ)) : ℝ)) := by
  -- The Souriau maps are those of the diagonal frames `diag (e^{i θ_j t / 2})` on `n ⊕ n`.
  set φ : n ⊕ n → I → ℝ := fun k t ↦ Sum.elim (fun j ↦ θ j t / 2) (fun j ↦ θ j t / 2) k with hφ
  have hφc (k : n ⊕ n) : Continuous (φ k) := by
    rcases k with j | j <;> exact (hθ j).div_const 2
  set W : I → unitaryGroup (n ⊕ n) ℂ := fun t ↦ unitaryTorusHom (n ⊕ n) fun k ↦ Circle.exp (φ k t)
  have hW : Continuous W :=
    continuous_unitaryTorusHom.comp (continuous_pi fun k ↦ Circle.exp.continuous.comp (hφc k))
  let γ' : Path (W 0) (W 1) := ⟨⟨W, hW⟩, rfl, rfl⟩
  have hγ' (t : I) : γ' t = W t := rfl
  have hs (t : I) : souriau ((γ.map continuous_diagonalGraphFrame) t) = souriau (γ' t) := by
    refine Subtype.ext ?_
    have hd : (unitaryTorusHom n fun j ↦ Circle.exp (θ j t) : Matrix n n ℂ)ᵀ =
        unitaryTorusHom n fun j ↦ Circle.exp (θ j t) := by
      simp
    rw [Path.map_coe, Function.comp_apply, hγ t, coe_souriau_diagonalGraphFrame_ofUnitary hd, hγ',
      coe_souriau_of_coe_eq_diagonal (coe_unitaryTorusHom _), coe_unitaryTorusHom,
      fromBlocks_diagonal]
    congr 1
    funext k
    rcases k with j | j <;>
    · simp only [φ, Sum.elim_inl, Sum.elim_inr, Circle.coe_exp, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
  rw [robbinSalamonIndex, Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _ γ' hs,
    Matrix.UnitaryGroup.maslovIndex_eq_sum_of_diagonal γ' hφc fun t ↦ by
      simp [γ', W, Circle.coe_exp]]
  rw [Fintype.sum_sum_type]
  simp only [φ, Sum.elim_inl, Sum.elim_inr, div_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The path `t ↦ diag (e^{i θ_j t})` of rotations from the identity, realified to symplectic
matrices. -/
noncomputable def rotationPath (θ : n → ℝ) :
    Path 1 (ofUnitary (unitaryTorusHom n fun j ↦ Circle.exp (θ j))) where
  toFun t := ofUnitary (unitaryTorusHom n fun j ↦ Circle.exp (θ j * t))
  continuous_toFun := continuous_ofUnitary.comp (continuous_unitaryTorusHom.comp
    (continuous_pi fun j ↦
      Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)))
  source' := by simp [Circle.exp_zero, ← Pi.one_def]
  target' := by simp

/-- The rotation path at time `t` is the realification of `diag (e^{i θ_j t})`. -/
@[simp]
theorem rotationPath_apply (θ : n → ℝ) (t : I) :
    rotationPath θ t = ofUnitary (unitaryTorusHom n fun j ↦ Circle.exp (θ j * t)) :=
  (rfl)

/-- **The Conley–Zehnder index of a rotation path**: `-∑ j, (⌊θ_j / 2π⌋ + ⌈θ_j / 2π⌉)`. -/
theorem conleyZehnderIndex_rotationPath (θ : n → ℝ) :
    conleyZehnderIndex (rotationPath θ) =
      -∑ j, (((⌊θ j / (2 * Real.pi)⌋ + ⌈θ j / (2 * Real.pi)⌉ : ℤ)) : ℝ) := by
  rw [conleyZehnderIndex, robbinSalamonIndex_eq_sum_of_diagonal (rotationPath θ)
    (θ := fun j t ↦ θ j * t) (fun j ↦ continuous_const.mul continuous_subtype_val)
    (rotationPath_apply θ)]
  simp

/-- **Normalization.** A rotation by angles in `(0, 2π)` has Conley–Zehnder index `-n`; in
particular a small positive rotation of `ℝ²` has index `-1`. -/
theorem conleyZehnderIndex_rotationPath_of_pos {θ : n → ℝ}
    (hθ : ∀ j, 0 < θ j ∧ θ j < 2 * Real.pi) :
    conleyZehnderIndex (rotationPath θ) = -Fintype.card n := by
  have h (j : n) : ⌊θ j / (2 * Real.pi)⌋ + ⌈θ j / (2 * Real.pi)⌉ = 1 := by
    have h0 : 0 < θ j / (2 * Real.pi) := div_pos (hθ j).1 (by positivity)
    have h1 : θ j / (2 * Real.pi) < 1 := (div_lt_one (by positivity)).2 (hθ j).2
    rw [Int.floor_eq_zero_iff.2 ⟨h0.le, h1⟩,
      (Int.ceil_eq_iff (z := 1)).2 ⟨by norm_num [h0], by norm_num [h1.le]⟩]
    norm_num
  simp [conleyZehnderIndex_rotationPath, h]

/-- **Normalization.** A rotation by angles in `(-2π, 0)` has Conley–Zehnder index `n`. -/
theorem conleyZehnderIndex_rotationPath_of_neg {θ : n → ℝ}
    (hθ : ∀ j, -(2 * Real.pi) < θ j ∧ θ j < 0) :
    conleyZehnderIndex (rotationPath θ) = Fintype.card n := by
  have h (j : n) : ⌊θ j / (2 * Real.pi)⌋ + ⌈θ j / (2 * Real.pi)⌉ = -1 := by
    have h0 : θ j / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (hθ j).2 (by positivity)
    have h1 : -1 < θ j / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith [(hθ j).1]
    rw [(Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
    norm_num
  simp [conleyZehnderIndex_rotationPath, h]

end TauCeti.GLSymplectic
