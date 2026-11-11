/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian

/-!
# The Conley–Zehnder index of paths of symplectic matrices

Identify `ℝ^{n ⊕ n}` with `ℂⁿ` by `φ (x, y) = x + i y`, the convention of `Matrix.realify`, so that
`J = Matrix.J n ℝ` is multiplication by `i` and the standard symplectic form is `ω = Im ⟪·, ·⟫`.
The graph `Γ(A)` of a symplectic matrix `A` is a Lagrangian subspace of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`
(`Matrix.graphSubspace`), and the graph of the identity is the diagonal `Δ = Γ(1)`. Following
Robbin and Salamon, the Maslov index of a path `γ` of symplectic matrices is the Maslov index
`μ(Γ ∘ γ, Δ)` of its path of graphs relative to the diagonal, and its Conley–Zehnder index is
read off from it.

To measure graphs relative to `Δ` we move `Δ` to the real points `ℝ^{n ⊕ n}` of `ℂ^{n ⊕ n}`. The
frame `graphFrame 1` of `Δ` is `√2` times a unitary matrix
(`Matrix.conjTranspose_graphFrame_one_mul_self`), and it carries the real span of the
**diagonal graph frame**

`N(A) = (1 + A) + i J (1 - A)` (`Matrix.diagonalGraphFrame`)

onto `Γ(A)` (`Matrix.graphSubspace_eq_map_realImage_diagonalGraphFrame`), while `N(1) = 2` spans
`ℝ^{n ⊕ n}`. The Hermitian Gram matrix of `N(A)` is `2 (1 + Aᵀ A) + 2 i (J - Aᵀ J A)`
(`Matrix.conjTranspose_diagonalGraphFrame_mul_self`). Its imaginary part vanishes exactly when `A`
is symplectic, which says that `N(A) ℝ^{n ⊕ n}` is Lagrangian, and its real part is positive
definite, so `N(A)` is invertible (`Matrix.isUnit_diagonalGraphFrame`).

Orthonormalizing the real columns of `N(A)` gives a unitary frame of the same Lagrangian,
`TauCeti.GLSymplectic.diagonalGraphUnitary A`, continuous in `A`. Its Souriau map `W(A)` is
characterized by `W(A) (conj N(A)) = N(A)`
(`TauCeti.GLSymplectic.coe_souriau_diagonalGraphUnitary_eq`).
In particular `W(1) = 1`, and `W(A)` has the eigenvalue `1` exactly when `A` does
(`TauCeti.GLSymplectic.det_coe_souriau_diagonalGraphUnitary_sub_one_eq_zero_iff`), that is,
exactly when `Γ(A)` meets `Δ` nontrivially.

* `TauCeti.GLSymplectic.graphMaslovIndex γ` is `μ(Γ ∘ γ, Δ)`, Souriau's formula
  `Matrix.UnitaryGroup.maslovIndex` for the path of unitary frames. It is additive under
  catenation, changes sign under reversal and is invariant under homotopies with fixed endpoints.
* `TauCeti.GLSymplectic.conleyZehnderIndex γ = -graphMaslovIndex γ` for a path `γ` starting at the
  identity. With this sign a small positive rotation has index `-n`: the path `t ↦ e^{i θ t} I` of
  scalar rotations has index `-n (⌊θ / 2π⌋ + ⌈θ / 2π⌉)`
  (`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_scalarRotation`), which is `-n` for
  `0 < θ < 2π` and `n` for `-2π < θ < 0`. So `t ↦ exp (t J S)` has index `-signature(S) / 2` for
  `S = θ I` with `0 < |θ| < 2π`, and the clockwise flow of `H = ε |z|² / 2`, for
  `ι_{X_H} ω = dH` and small `ε > 0`, has index `n`.

As for Robbin and Salamon, both indices are defined for every path; at an endpoint with the
eigenvalue `1` they may take half-integer values. The integrality of the Conley–Zehnder index at
nondegenerate endpoints, its loop and direct-sum laws, and the comparison with crossing forms are
not treated here.

## Main definitions

* `Matrix.diagonalGraphFrame`: the frame `(1 + A) + i J (1 - A)` of the graph of `A` relative to
  the diagonal.
* `TauCeti.GLSymplectic.diagonalGraphUnitary`: its unitary orthonormalization.
* `TauCeti.GLSymplectic.graphMaslovIndex`: the Maslov index of the graphs of a symplectic path
  relative to the diagonal.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a symplectic path from
  the identity.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Sections 4 and 5 (the Maslov index of a symplectic path as that of its graph relative to the
  diagonal, and the Conley–Zehnder index).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360 (the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Complex
open scoped unitInterval ComplexConjugate Matrix.Norms.L2Operator

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The diagonal graph frame -/

/-- The **diagonal graph frame** `(1 + A) + i J (1 - A)` of a real matrix `A` on `ℝ^{n ⊕ n}`. The
frame `graphFrame 1` of the diagonal carries its real span onto the graph of `A`
(`Matrix.graphSubspace_eq_map_realImage_diagonalGraphFrame`) and the real points onto the
diagonal, so it frames the graph of `A` relative to the diagonal. -/
noncomputable def diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (1 + A).map ((↑) : ℝ → ℂ) + Complex.I • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ)

/-- The diagonal graph frame of `A` is `(1 + A) + i J (1 - A)`. -/
theorem diagonalGraphFrame_def (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalGraphFrame A =
      (1 + A).map ((↑) : ℝ → ℂ) + Complex.I • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ) :=
  (rfl)

/-- The frame of the diagonal times the diagonal graph frame of `A` is twice the graph frame of
`A`. -/
theorem graphFrame_one_mul_diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    graphFrame 1 * diagonalGraphFrame A = (2 : ℂ) • graphFrame A := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, A = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks A).symm⟩
  rw [graphFrame_def, graphFrame_def, diagonalGraphFrame, J, ← fromBlocks_one]
  simp only [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_multiply, fromBlocks_map,
    fromBlocks_smul, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h] <;> ring_nf <;> simp [I_sq] <;> ring

/-- The frame of the diagonal is `√2` times a unitary matrix: `(graphFrame 1)ᴴ graphFrame 1 = 2`.
-/
theorem conjTranspose_graphFrame_one_mul_self :
    (graphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ * graphFrame 1 = (2 : ℂ) • 1 := by
  rw [graphFrame_def, ← fromBlocks_one]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, fromBlocks_conjTranspose, fromBlocks_multiply]
  conv_rhs => rw [← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h] <;> ring

/-- **The diagonal graph frame frames the graph relative to the diagonal.** The frame
`graphFrame 1` of the diagonal carries the real span of `diagonalGraphFrame A` onto the graph of
`A`. -/
theorem graphSubspace_eq_map_realImage_diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    graphSubspace A = (diagonalGraphFrame A).realImage.map
      (((toEuclideanCLM (𝕜 := ℂ) (graphFrame 1) :
        EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) :
          EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) := by
  have h2 : IsUnit ((2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) := by
    rw [isUnit_iff_isUnit_det, det_smul, det_one, mul_one]
    exact (IsUnit.mk0 (2 : ℝ) two_ne_zero).pow _
  have h : ((2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) = (2 : ℂ) • 1 := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [← realImage_mul, graphFrame_one_mul_diagonalGraphFrame, graphSubspace_def,
    ← realImage_mul_map_ofReal (graphFrame A) h2, h, Matrix.mul_smul, Matrix.mul_one]

/-- The Hermitian Gram matrix of the diagonal graph frame is
`2 (1 + Aᵀ A) + 2 i (J - Aᵀ J A)`. Its imaginary part is the obstruction to `A` being symplectic. -/
theorem conjTranspose_diagonalGraphFrame_mul_self (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (diagonalGraphFrame A)ᴴ * diagonalGraphFrame A =
      (2 • (1 + Aᵀ * A)).map ((↑) : ℝ → ℂ) +
        Complex.I • (2 • (J n ℝ - Aᵀ * J n ℝ * A)).map ((↑) : ℝ → ℂ) := by
  have hJ : (J n ℝ)ᵀ * J n ℝ = 1 := by rw [J_transpose, neg_mul, J_squared, neg_neg]
  have h₁ : (1 + A)ᵀ * (1 + A) + (J n ℝ * (1 - A))ᵀ * (J n ℝ * (1 - A)) = 2 • (1 + Aᵀ * A) := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (J n ℝ)ᵀ, hJ, Matrix.one_mul,
      transpose_add, transpose_sub, transpose_one]
    noncomm_ring
  have h₂ : (1 + A)ᵀ * (J n ℝ * (1 - A)) - (J n ℝ * (1 - A))ᵀ * (1 + A) =
      2 • (J n ℝ - Aᵀ * J n ℝ * A) := by
    rw [transpose_mul, J_transpose, transpose_add, transpose_sub, transpose_one]
    noncomm_ring
  rw [diagonalGraphFrame, conjTranspose_mul_self_map_ofReal_add_I_smul, h₁, h₂]

/-- **The diagonal graph frame of a symplectic matrix frames a Lagrangian subspace**: its
Hermitian Gram matrix `2 (1 + Aᵀ A)` is real. -/
theorem conjTranspose_diagonalGraphFrame_mul_self_of_mem {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (diagonalGraphFrame A)ᴴ * diagonalGraphFrame A = (2 • (1 + Aᵀ * A)).map ((↑) : ℝ → ℂ) := by
  rw [conjTranspose_diagonalGraphFrame_mul_self, SymplecticGroup.mem_iff'.1 hA, sub_self,
    smul_zero, Matrix.map_zero _ ofReal_zero, smul_zero, add_zero]

/-- The diagonal graph frame of a symplectic matrix is invertible. -/
theorem isUnit_diagonalGraphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) : IsUnit (diagonalGraphFrame A) := by
  have hpos : (2 • (1 + Aᵀ * A)).PosDef := by
    have h := (PosDef.one (n := n ⊕ n) (R := ℝ)).add_posSemidef
      (posSemidef_conjTranspose_mul_self A)
    rw [conjTranspose_eq_transpose_of_trivial] at h
    rw [two_nsmul]
    exact h.add h
  have h : IsUnit ((2 • (1 + Aᵀ * A)).map ((↑) : ℝ → ℂ)) :=
    hpos.isUnit.map Complex.ofRealHom.mapMatrix
  rw [← conjTranspose_diagonalGraphFrame_mul_self_of_mem hA] at h
  exact isUnit_of_mul_isUnit_right h

/-- The imaginary part of the diagonal graph frame: `N - conj N = 2 i J (1 - A)`. -/
theorem diagonalGraphFrame_sub_map_conj (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalGraphFrame A - (diagonalGraphFrame A).map conj =
      (2 * Complex.I) • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ) := by
  ext i j
  apply Complex.ext <;> simp [diagonalGraphFrame]
  ring

/-- For the realification of a scalar `c` of modulus one, the diagonal graph frame `N` satisfies
`c (conj N) = N`. -/
theorem smul_map_conj_diagonalGraphFrame_realify_smul_one {c : ℂ} (hc : c * conj c = 1) :
    c • (diagonalGraphFrame (c • (1 : Matrix n n ℂ)).realify).map conj =
      diagonalGraphFrame (c • (1 : Matrix n n ℂ)).realify := by
  have hre : c.re * c.re + c.im * c.im = 1 := by
    have h := congrArg Complex.re hc
    simp only [mul_re, conj_re, conj_im, one_re] at h
    linarith
  ext (i | i) (j | j) <;> apply Complex.ext <;> by_cases h : i = j <;>
    simp [diagonalGraphFrame, J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h,
      realify_apply_inl_inl, realify_apply_inl_inr, realify_apply_inr_inl,
      realify_apply_inr_inr] <;>
    nlinarith [hre]

end Matrix

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The unitary frame of the graph relative to the diagonal -/

/-- The Hermitian Gram matrix of the diagonal graph frame of a symplectic matrix, as a real
matrix. -/
private theorem conjTranspose_diagonalGraphFrame_mul_self_coe (A : GLSymplectic n ℝ) :
    (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ *
        diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (2 • (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))).map ((↑) : ℝ → ℂ) :=
  conjTranspose_diagonalGraphFrame_mul_self_of_mem (mem_iff_mem_symplecticGroup.1 A.2)

/-- The diagonal graph frame of a symplectic matrix, as an invertible matrix. -/
private noncomputable def diagonalGraphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  (isUnit_diagonalGraphFrame (mem_iff_mem_symplecticGroup.1 A.2)).unit

private theorem coe_diagonalGraphFrameUnit (A : GLSymplectic n ℝ) :
    (diagonalGraphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  IsUnit.unit_spec _

/-- The **unitary frame of the graph** of a symplectic matrix `A` relative to the diagonal: the
real orthonormalization of the diagonal graph frame of `A`. It spans the same Lagrangian subspace
(`TauCeti.GLSymplectic.realImage_diagonalGraphUnitary`). -/
noncomputable def diagonalGraphUnitary (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨realOrthonormalize (diagonalGraphFrameUnit A), realOrthonormalize_mem_unitaryGroup <| by
    rw [coe_diagonalGraphFrameUnit]
    exact conjTranspose_diagonalGraphFrame_mul_self_coe A⟩

/-- The unitary frame of the graph spans the same real subspace as the diagonal graph frame. -/
theorem realImage_diagonalGraphUnitary (A : GLSymplectic n ℝ) :
    (diagonalGraphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
  rw [← coe_diagonalGraphFrameUnit]
  exact realImage_realOrthonormalize _

/-- The Souriau map `W` of the unitary frame of the graph satisfies `W (conj N) = N` for the
diagonal graph frame `N`. -/
theorem souriau_diagonalGraphUnitary_mul_map_conj (A : GLSymplectic n ℝ) :
    (souriau (diagonalGraphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
        (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map conj =
      diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix (n ⊕ n) (n ⊕ n) ℝ,
      (diagonalGraphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
          S.map ((↑) : ℝ → ℂ) :=
    ⟨_, by rw [← coe_diagonalGraphFrameUnit]; exact coe_realOrthonormalize _⟩
  exact souriau_mul_map_conj_of_eq_mul_map_ofReal hS
    (conjTranspose_diagonalGraphFrame_mul_self_coe A)

/-- **The Souriau map of the graph.** The Souriau map of the unitary frame of the graph of `A` is
the unique `W` with `W (conj N) = N`, for the diagonal graph frame `N`, that is,
`W = N (conj N)⁻¹`. -/
theorem coe_souriau_diagonalGraphUnitary_eq {A : GLSymplectic n ℝ}
    {W : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hW : W * (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map conj =
      diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) :
    (souriau (diagonalGraphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) = W := by
  have hu : IsUnit ((diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ)).map conj) :=
    (isUnit_diagonalGraphFrame (mem_iff_mem_symplecticGroup.1 A.2)).map
      (starRingEnd ℂ).mapMatrix
  exact hu.mul_left_inj.1 ((souriau_diagonalGraphUnitary_mul_map_conj A).trans hW.symm)

/-- The graph of the identity is the diagonal: its Souriau map is the identity. -/
@[simp]
theorem souriau_diagonalGraphUnitary_one :
    souriau (diagonalGraphUnitary (1 : GLSymplectic n ℝ)) = 1 := by
  refine Subtype.ext (coe_souriau_diagonalGraphUnitary_eq ?_)
  simp only [diagonalGraphFrame]
  ext i j
  simp

/-- **Crossings with the diagonal.** The Souriau map of the graph of `A` has the eigenvalue `1`
exactly when `A` does, that is, exactly when the graph of `A` meets the diagonal nontrivially. -/
theorem det_coe_souriau_diagonalGraphUnitary_sub_one_eq_zero_iff (A : GLSymplectic n ℝ) :
    ((souriau (diagonalGraphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) - 1).det = 0 ↔
      (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1).det = 0 := by
  set M := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hconj : ((diagonalGraphFrame M).map conj).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).1 ((isUnit_diagonalGraphFrame
      (mem_iff_mem_symplecticGroup.1 A.2)).map (starRingEnd ℂ).mapMatrix)).ne_zero
  -- `(W - 1) (conj N) = N - conj N = 2 i J (1 - A)`.
  have h : ((souriau (diagonalGraphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) - 1) *
      (diagonalGraphFrame M).map conj = (2 * Complex.I) • (J n ℝ * (1 - M)).map ((↑) : ℝ → ℂ) := by
    rw [Matrix.sub_mul, souriau_diagonalGraphUnitary_mul_map_conj, Matrix.one_mul,
      diagonalGraphFrame_sub_map_conj]
  have hmap : ((J n ℝ * (1 - M)).map ((↑) : ℝ → ℂ)).det = ((J n ℝ * (1 - M)).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom _).symm
  have hdet := congrArg Matrix.det h
  rw [det_mul, det_smul, hmap, det_mul] at hdet
  have h1 : (1 - M).det = 0 ↔ (M - 1).det = 0 := by
    rw [← neg_sub, det_neg]
    simp
  rw [← h1, ← mul_eq_zero_iff_right hconj, hdet]
  simp [Complex.I_ne_zero]

/-- The unitary frame of the graph depends continuously on the symplectic matrix. -/
theorem continuous_diagonalGraphUnitary :
    Continuous (diagonalGraphUnitary : GLSymplectic n ℝ → unitaryGroup (n ⊕ n) ℂ) := by
  have hN : Continuous (diagonalGraphFrameUnit : GLSymplectic n ℝ → GL (n ⊕ n) ℂ) := by
    refine Units.isOpenEmbedding_val.continuous_iff.2 ?_
    simp only [Function.comp_def, coe_diagonalGraphFrameUnit, diagonalGraphFrame]
    have h : Continuous fun A : GLSymplectic n ℝ ↦
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
      Units.continuous_val.comp continuous_subtype_val
    fun_prop
  exact (Units.continuous_val.comp (continuous_realOrthonormalize hN)).subtype_mk _

/-! ### The Maslov index of the graphs relative to the diagonal -/

/-- The **Maslov index of a symplectic path relative to the diagonal**: the Robbin–Salamon Maslov
index `μ(Γ ∘ γ, Δ)` of the path of graphs `t ↦ Γ(γ t)` relative to the diagonal, computed by
Souriau's formula on the unitary frames of the graphs. -/
noncomputable def graphMaslovIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  Matrix.UnitaryGroup.maslovIndex (γ.map continuous_diagonalGraphUnitary)

/-- The Maslov index of the graphs is Souriau's index of the path of their unitary frames. -/
theorem graphMaslovIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ = Matrix.UnitaryGroup.maslovIndex (γ.map continuous_diagonalGraphUnitary) :=
  (rfl)

/-- The constant path has Maslov index zero. -/
@[simp]
theorem graphMaslovIndex_refl (A : GLSymplectic n ℝ) : graphMaslovIndex (Path.refl A) = 0 := by
  have h : (Path.refl A).map continuous_diagonalGraphUnitary = Path.refl _ := by
    ext
    simp
  rw [graphMaslovIndex_def, h, Matrix.UnitaryGroup.maslovIndex_refl]

/-- **Catenation.** The Maslov index of a concatenation of symplectic paths is the sum of their
indices. -/
@[simp]
theorem graphMaslovIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    graphMaslovIndex (γ₁.trans γ₂) = graphMaslovIndex γ₁ + graphMaslovIndex γ₂ := by
  rw [graphMaslovIndex_def, Path.map_trans, Matrix.UnitaryGroup.maslovIndex_trans,
    graphMaslovIndex_def, graphMaslovIndex_def]

/-- Reversing a symplectic path negates its Maslov index. -/
@[simp]
theorem graphMaslovIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ.symm = -graphMaslovIndex γ := by
  rw [graphMaslovIndex_def, ← Path.map_symm, Matrix.UnitaryGroup.maslovIndex_symm,
    graphMaslovIndex_def]

/-- **Homotopy invariance.** Symplectic paths that are homotopic relative to their endpoints have
the same Maslov index. -/
theorem graphMaslovIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : graphMaslovIndex γ₀ = graphMaslovIndex γ₁ :=
  Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_diagonalGraphUnitary⟩)

/-- **Scalar rotations.** Along a path of realified scalar rotations `t ↦ e^{i θ(t)} I` of
`ℂⁿ`, the Maslov index of the graphs relative to the diagonal is
`n ((⌊θ(1) / 2π⌋ + ⌈θ(1) / 2π⌉) - (⌊θ(0) / 2π⌋ + ⌈θ(0) / 2π⌉))`: every crossing of a multiple of
`2π` counts `2n`, and an endpoint on a multiple of `2π` counts half. -/
theorem graphMaslovIndex_eq_of_scalarRotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : I → ℝ} (hθ : Continuous θ)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (Complex.exp (θ t * Complex.I) • (1 : Matrix n n ℂ)).realify) :
    graphMaslovIndex γ = Fintype.card n *
      (((⌊θ 1 / (2 * Real.pi)⌋ + ⌈θ 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) -
        ((⌊θ 0 / (2 * Real.pi)⌋ + ⌈θ 0 / (2 * Real.pi)⌉ : ℤ) : ℝ)) := by
  -- The diagonal unitary frames `e^{i θ(t) / 2} I` have the same Souriau maps `e^{i θ(t)} I`.
  let δ : C(I, unitaryGroup (n ⊕ n) ℂ) :=
    ⟨fun t ↦ ⟨(Circle.exp (θ t / 2) : ℂ) • 1,
      Unitary.smul_mem_of_mem (Circle.exp _).coe_mem_unitary (one_mem _)⟩,
      Continuous.subtype_mk (by fun_prop) _⟩
  -- Both `hδ` and `hδ'` hold by the definitions of `δ` and `δ'` just given.
  have hδ (t : I) : (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ) = (Circle.exp (θ t / 2) : ℂ) • 1 := rfl
  have hsouriau (t : I) : souriau (diagonalGraphUnitary (γ t)) = souriau (δ t) := by
    have hc : Complex.exp (θ t * Complex.I) * conj (Complex.exp (θ t * Complex.I)) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp
    refine Subtype.ext ((coe_souriau_diagonalGraphUnitary_eq
      (W := Complex.exp (θ t * Complex.I) • 1) ?_).trans ?_)
    · rw [hγ t, Matrix.smul_mul, Matrix.one_mul]
      exact smul_map_conj_diagonalGraphFrame_realify_smul_one hc
    · rw [coe_souriau, hδ, transpose_smul, transpose_one, smul_mul_smul_comm, Matrix.one_mul,
        ← Circle.coe_mul, ← Circle.exp_add, Circle.coe_exp, add_halves]
  let δ' : Path (δ 0) (δ 1) := { toContinuousMap := δ, source' := rfl, target' := rfl }
  have hδ' (t : I) : δ' t = δ t := rfl
  have key := Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq
    (γ.map continuous_diagonalGraphUnitary) δ' fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, hδ']
      exact hsouriau t
  rw [graphMaslovIndex_def, key, Matrix.UnitaryGroup.maslovIndex_eq_sum_of_diagonal δ'
    (φ := fun _ t ↦ θ t / 2) (fun _ ↦ hθ.div_const 2) fun t ↦ by
      rw [hδ', hδ, Circle.coe_exp, smul_one_eq_diagonal]]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, nsmul_eq_mul, div_div,
    mul_comm (2 : ℝ) Real.pi]
  push_cast
  ring

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices starting at the identity:
`CZ(γ) = -μ(Γ ∘ γ, Δ)`, minus the Maslov index of its graphs relative to the diagonal. With this
sign a small positive rotation of `ℂⁿ` has index `-n`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_card_of_scalarRotation`). -/
noncomputable def conleyZehnderIndex {A : GLSymplectic n ℝ} (γ : Path 1 A) : ℝ :=
  -graphMaslovIndex γ

/-- The Conley–Zehnder index is minus the Maslov index of the graphs relative to the diagonal. -/
theorem conleyZehnderIndex_def {A : GLSymplectic n ℝ} (γ : Path 1 A) :
    conleyZehnderIndex γ = -graphMaslovIndex γ :=
  (rfl)

/-- The constant path at the identity has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl : conleyZehnderIndex (Path.refl (1 : GLSymplectic n ℝ)) = 0 := by
  simp [conleyZehnderIndex_def]

/-- **Catenation.** Continuing a path from the identity by a second path changes its
Conley–Zehnder index by minus the Maslov index of the second path. -/
theorem conleyZehnderIndex_trans {A B : GLSymplectic n ℝ} (γ : Path 1 A) (δ : Path A B) :
    conleyZehnderIndex (γ.trans δ) = conleyZehnderIndex γ - graphMaslovIndex δ := by
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, graphMaslovIndex_trans]
  ring

/-- **Homotopy invariance.** Paths from the identity that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A : GLSymplectic n ℝ} {γ₀ γ₁ : Path 1 A}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, graphMaslovIndex_eq_of_homotopic h]

/-- **Scalar rotations.** The path `t ↦ e^{i θ t} I` of realified scalar rotations of `ℂⁿ` has
Conley–Zehnder index `-n (⌊θ / 2π⌋ + ⌈θ / 2π⌉)`. -/
theorem conleyZehnderIndex_eq_of_scalarRotation {A : GLSymplectic n ℝ} (γ : Path 1 A) (θ : ℝ)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (Complex.exp ((θ * t : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realify) :
    conleyZehnderIndex γ =
      -(Fintype.card n * ((⌊θ / (2 * Real.pi)⌋ + ⌈θ / (2 * Real.pi)⌉ : ℤ) : ℝ)) := by
  rw [conleyZehnderIndex_def, graphMaslovIndex_eq_of_scalarRotation γ
    (continuous_const.mul continuous_subtype_val) hγ]
  simp

/-- **Normalization.** A positive rotation `t ↦ e^{i θ t} I` of `ℂⁿ` by an angle `0 < θ < 2π`, which
is the path `t ↦ exp (t J S)` for `S = θ I`, has Conley–Zehnder index `-n = -signature(S) / 2`. -/
theorem conleyZehnderIndex_eq_neg_card_of_scalarRotation {A : GLSymplectic n ℝ} (γ : Path 1 A)
    {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < 2 * Real.pi)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (Complex.exp ((θ * t : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realify) :
    conleyZehnderIndex γ = -Fintype.card n := by
  have hx₀ : 0 < θ / (2 * Real.pi) := div_pos h₀ (by positivity)
  have hx₁ : θ / (2 * Real.pi) < 1 := (div_lt_one (by positivity)).2 h₁
  rw [conleyZehnderIndex_eq_of_scalarRotation γ θ hγ, Int.floor_eq_zero_iff.2 ⟨hx₀.le, hx₁⟩,
    (Int.ceil_eq_iff (z := 1)).2 ⟨by simpa using hx₀, by simpa using hx₁.le⟩]
  simp

/-- **Normalization.** A negative rotation `t ↦ e^{i θ t} I` of `ℂⁿ` by an angle
`-2π < θ < 0`, for instance the flow of `H = ε |z|² / 2` with `ι_{X_H} ω = dH` and `0 < ε < 2π`,
has Conley–Zehnder index `n`. -/
theorem conleyZehnderIndex_eq_card_of_scalarRotation {A : GLSymplectic n ℝ} (γ : Path 1 A)
    {θ : ℝ} (h₀ : -(2 * Real.pi) < θ) (h₁ : θ < 0)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (Complex.exp ((θ * t : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realify) :
    conleyZehnderIndex γ = Fintype.card n := by
  have hx₀ : -1 < θ / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hx₁ : θ / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos h₁ (by positivity)
  rw [conleyZehnderIndex_eq_of_scalarRotation γ θ hγ,
    (Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
    (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
  simp

end TauCeti.GLSymplectic
