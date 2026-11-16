/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.Frobenius

/-!
# Matrix nuclear-norm trace duality, orthogonal additivity, and low-rank decomposition

Matrix specializations of the operator-level nuclear-norm theory from
`TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear`. The nuclear norm of a
rectangular matrix `A : Matrix m n 𝕜` is represented directly as
`TauCeti.UnitarilyInvariantSeminorm.nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m)` applied to
`A.toEuclideanLin`, matching the convention of `TauCeti.Analysis.Matrix.SingularValues` without
introducing a second definition.

Because `Matrix.Norms.L2Operator` and `Matrix.Norms.Frobenius` provide competing scoped `Norm`
instances on `Matrix m n 𝕜`, the two scopes are never opened simultaneously: trace-duality
estimates open only `Matrix.Norms.L2Operator` and write the Frobenius pairing explicitly as
`(Aᴴ * B).trace` or `∑ i, ∑ j, conj (A i j) * B i j`, while the low-rank decomposition opens only
`Matrix.Norms.Frobenius` and expresses Frobenius orthogonality and size via `⟪Δ₁, Δ₂⟫_𝕜 = 0` and
`‖Δ‖`.

## Main declarations

* `Matrix.trace_toEuclideanLin`, `Matrix.trace_adjoint_comp_toEuclideanLin`:
  operator traces of `M.toEuclideanLin` and `A.toEuclideanLin† ∘ₗ B.toEuclideanLin` equal
  `M.trace` and `(Aᴴ * B).trace`.
* `Matrix.opNorm_toEuclideanLin`, `Matrix.frobenius_toEuclideanLin`: bridges between the operator
  and Frobenius unitarily invariant seminorms of `A.toEuclideanLin` and the scoped matrix norms.
* `Matrix.nuclear_toEuclideanLin_conjTranspose`, `Matrix.nuclear_toEuclideanLin_vecMulVec`:
  conjugate-transpose invariance and the nuclear norm of a rank-one outer product.
* `Matrix.norm_trace_conjTranspose_mul_le_l2_opNorm_mul_nuclear`,
  `Matrix.norm_trace_conjTranspose_mul_le_nuclear_mul_l2_opNorm`,
  `Matrix.norm_sum_conj_mul_le_l2_opNorm_mul_nuclear`,
  `Matrix.abs_sum_mul_le_l2_opNorm_mul_nuclear`:
  matrix trace duality `‖tr (Aᴴ B)‖ ≤ ‖A‖ ‖B‖₁` and its entrywise and real forms.
* `Matrix.exists_l2_opNorm_le_one_trace_conjTranspose_mul_eq_nuclear`,
  `Matrix.exists_nuclear_le_one_trace_conjTranspose_mul_eq_l2_opNorm`:
  attainment of matrix trace duality for both the nuclear norm and the `ℓ²` operator norm.
* `Matrix.nuclear_toEuclideanLin_add_of_orthogonal`:
  `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁` whenever `Aᴴ * B = 0` and `A * Bᴴ = 0`.
* `Matrix.exists_lowRank_decomposition`:
  Wainwright's low-rank tangent–normal decomposition for matrices of rank at most `r`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.4.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, Section 10.2.1.
-/

public section

open scoped ComplexConjugate InnerProductSpace Matrix
open TauCeti.UnitarilyInvariantSeminorm

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The operator trace of `M.toEuclideanLin` on `EuclideanSpace 𝕜 n` is `M.trace`. -/
@[simp]
theorem trace_toEuclideanLin (M : Matrix n n 𝕜) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n) M.toEuclideanLin = M.trace := by
  rw [toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq]

variable {m : Type*} [Fintype m]

/-- The Hilbert–Schmidt operator trace pairing `tr (A† B)` of `A.toEuclideanLin` and
`B.toEuclideanLin` equals the matrix trace `(Aᴴ * B).trace`. -/
theorem trace_adjoint_comp_toEuclideanLin (A B : Matrix m n 𝕜) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n)
        (LinearMap.adjoint A.toEuclideanLin ∘ₗ B.toEuclideanLin) =
      (Aᴴ * B).trace := by
  classical
  rw [← toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin, toEuclideanLin,
    ← toLpLin_mul_same, ← toEuclideanLin, trace_toEuclideanLin]

open scoped Matrix.Norms.L2Operator in
/-- The operator seminorm of `A.toEuclideanLin` is the scoped `ℓ²` operator norm of `A`. -/
theorem opNorm_toEuclideanLin (A : Matrix m n 𝕜) :
    opNorm 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin = ‖A‖ := by
  rw [opNorm_apply, l2_opNorm_def, LinearEquiv.trans_apply]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius seminorm of `A.toEuclideanLin` is the scoped Frobenius norm of `A`. -/
theorem frobenius_toEuclideanLin (A : Matrix m n 𝕜) :
    frobenius 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin = ‖A‖ := by
  classical
  have h := LinearMap.frobenius_norm_toMatrix A.toEuclideanLin
    (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)
  rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin] at h
  exact h.symm

/-- Taking the conjugate transpose preserves the nuclear norm of a matrix. -/
theorem nuclear_toEuclideanLin_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) :
    nuclear 𝕜 (EuclideanSpace 𝕜 m) (EuclideanSpace 𝕜 n) Aᴴ.toEuclideanLin =
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint, nuclear_apply, LinearMap.singularValues_adjoint,
    ← nuclear_apply]

/-- The nuclear norm of a rank-one outer product `u vᴴ` is `‖u‖ * ‖v‖`. -/
theorem nuclear_toEuclideanLin_vecMulVec (u : EuclideanSpace 𝕜 m) (v : EuclideanSpace 𝕜 n) :
    nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m)
        (vecMulVec u.ofLp (star v.ofLp)).toEuclideanLin = ‖u‖ * ‖v‖ := by
  have h : (vecMulVec u.ofLp (star v.ofLp)).toEuclideanLin =
      (InnerProductSpace.rankOne 𝕜 u v).toLinearMap := by
    have hsymm := InnerProductSpace.symm_toEuclideanLin_rankOne u v
    exact ((LinearEquiv.symm_apply_eq toEuclideanLin).mp hsymm).symm
  rw [h, nuclear_rankOne]

/-! ### Trace duality -/

section TraceDuality

open scoped Matrix.Norms.L2Operator

/-- **Matrix trace duality**: `‖(Aᴴ * B).trace‖ ≤ ‖A‖ * ‖B‖₁`. -/
theorem norm_trace_conjTranspose_mul_le_l2_opNorm_mul_nuclear (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤
      ‖A‖ * nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) B.toEuclideanLin := by
  rw [← trace_adjoint_comp_toEuclideanLin, ← opNorm_toEuclideanLin]
  exact norm_trace_adjoint_comp_le_opNorm_mul_nuclear A.toEuclideanLin B.toEuclideanLin

/-- **Matrix trace duality (symmetric form)**: `‖(Aᴴ * B).trace‖ ≤ ‖A‖₁ * ‖B‖`. -/
theorem norm_trace_conjTranspose_mul_le_nuclear_mul_l2_opNorm (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin * ‖B‖ := by
  rw [← trace_adjoint_comp_toEuclideanLin, ← opNorm_toEuclideanLin]
  exact norm_trace_adjoint_comp_le_nuclear_mul_opNorm A.toEuclideanLin B.toEuclideanLin

/-- **Entrywise matrix trace duality**: `‖∑ i, ∑ j, conj (A i j) * B i j‖ ≤ ‖A‖ * ‖B‖₁`. -/
theorem norm_sum_conj_mul_le_l2_opNorm_mul_nuclear (A B : Matrix m n 𝕜) :
    ‖∑ i, ∑ j, conj (A i j) * B i j‖ ≤
      ‖A‖ * nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) B.toEuclideanLin := by
  have htr : ∑ i, ∑ j, conj (A i j) * B i j = (Aᴴ * B).trace := by
    simp only [trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def]
    exact Finset.sum_comm
  rw [htr]
  exact norm_trace_conjTranspose_mul_le_l2_opNorm_mul_nuclear A B

/-- **Real entrywise matrix trace duality**: `|∑ i, ∑ j, A i j * B i j| ≤ ‖A‖ * ‖B‖₁`. -/
theorem abs_sum_mul_le_l2_opNorm_mul_nuclear (A B : Matrix m n ℝ) :
    |∑ i, ∑ j, A i j * B i j| ≤
      ‖A‖ * nuclear ℝ (EuclideanSpace ℝ n) (EuclideanSpace ℝ m) B.toEuclideanLin := by
  simpa only [Real.norm_eq_abs, conj_trivial] using
    norm_sum_conj_mul_le_l2_opNorm_mul_nuclear A B

/-- **Attainment of matrix trace duality for the nuclear norm**: every matrix `B` admits a matrix
`U` with `‖U‖ ≤ 1` and `(Uᴴ * B).trace = ‖B‖₁`. -/
theorem exists_l2_opNorm_le_one_trace_conjTranspose_mul_eq_nuclear (B : Matrix m n 𝕜) :
    ∃ U : Matrix m n 𝕜, ‖U‖ ≤ 1 ∧
      (Uᴴ * B).trace =
        (nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) B.toEuclideanLin : 𝕜) := by
  obtain ⟨Uop, hU_norm, _, _, hU_tr⟩ :=
    exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear B.toEuclideanLin
  refine ⟨toEuclideanLin.symm Uop, ?_, ?_⟩
  · rw [← opNorm_toEuclideanLin, toEuclideanLin.apply_symm_apply]
    exact hU_norm
  · rw [← trace_adjoint_comp_toEuclideanLin, toEuclideanLin.apply_symm_apply]
    exact hU_tr

/-- **Attainment of matrix trace duality for the `ℓ²` operator norm**: every matrix `A` admits a
matrix `B` with `‖B‖₁ ≤ 1` and `(Aᴴ * B).trace = ‖A‖`. -/
theorem exists_nuclear_le_one_trace_conjTranspose_mul_eq_l2_opNorm (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜,
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) B.toEuclideanLin ≤ 1 ∧
      (Aᴴ * B).trace = (‖A‖ : 𝕜) := by
  obtain ⟨Bop, hB_norm, hB_tr⟩ :=
    exists_nuclear_le_one_trace_adjoint_comp_eq_opNorm A.toEuclideanLin
  refine ⟨toEuclideanLin.symm Bop, ?_, ?_⟩
  · rw [toEuclideanLin.apply_symm_apply]
    exact hB_norm
  · rw [← trace_adjoint_comp_toEuclideanLin, toEuclideanLin.apply_symm_apply, hB_tr,
      opNorm_toEuclideanLin]

end TraceDuality

/-! ### Orthogonal additivity and low-rank decomposition -/

/-- **Orthogonal additivity of the matrix nuclear norm**: if `Aᴴ * B = 0` and `A * Bᴴ = 0`, then
`‖A + B‖₁ = ‖A‖₁ + ‖B‖₁`. -/
theorem nuclear_toEuclideanLin_add_of_orthogonal {A B : Matrix m n 𝕜}
    (h₁ : Aᴴ * B = 0) (h₂ : A * Bᴴ = 0) :
    nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) (A + B).toEuclideanLin =
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin +
        nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) B.toEuclideanLin := by
  classical
  have h₁' : LinearMap.adjoint A.toEuclideanLin ∘ₗ B.toEuclideanLin = 0 := by
    rw [← toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin, toEuclideanLin,
      ← toLpLin_mul_same, h₁, map_zero]
  have h₂' : A.toEuclideanLin ∘ₗ LinearMap.adjoint B.toEuclideanLin = 0 := by
    rw [← toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin, toEuclideanLin,
      ← toLpLin_mul_same, h₂, map_zero]
  rw [map_add]
  exact nuclear_add_of_orthogonal h₁' h₂'

section LowRankDecomposition

open scoped Matrix.Norms.Frobenius

/-- **Wainwright's low-rank matrix decomposition**: if `Θ.rank ≤ r`, then every perturbation
`Δ : Matrix m n 𝕜` decomposes as `Δ = Δ₁ + Δ₂` where `Δ₁.rank ≤ 2 * r`, `Θᴴ * Δ₂ = 0`,
`Θ * Δ₂ᴴ = 0`, `⟪Δ₁, Δ₂⟫_𝕜 = 0`,
`‖Θ‖₁ + ‖Δ₂‖₁ - ‖Δ₁‖₁ ≤ ‖Θ + Δ‖₁`, and `‖Δ₁‖₁ ≤ √(2 * r) * ‖Δ‖` (Frobenius norm). -/
theorem exists_lowRank_decomposition {r : ℕ} {Θ : Matrix m n 𝕜}
    (hΘ : Θ.rank ≤ r) (Δ : Matrix m n 𝕜) :
    ∃ Δ₁ Δ₂ : Matrix m n 𝕜,
      Δ₁ + Δ₂ = Δ ∧
      Δ₁.rank ≤ 2 * r ∧
      Θᴴ * Δ₂ = 0 ∧
      Θ * Δ₂ᴴ = 0 ∧
      ⟪Δ₁, Δ₂⟫_𝕜 = 0 ∧
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) Θ.toEuclideanLin +
          nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) Δ₂.toEuclideanLin -
          nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) Δ₁.toEuclideanLin ≤
        nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) (Θ + Δ).toEuclideanLin ∧
      nuclear 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) Δ₁.toEuclideanLin ≤
        √(2 * (r : ℝ)) * ‖Δ‖ := by
  classical
  have hΘ' : Module.finrank 𝕜 (LinearMap.range Θ.toEuclideanLin) ≤ r := by
    rwa [← rank_eq_finrank_range_toEuclideanLin]
  obtain ⟨T₁, T₂, hsum, hrank, h₁, h₂, htr, hdec, hnuc⟩ :=
    TauCeti.UnitarilyInvariantSeminorm.exists_lowRank_decomposition hΘ' Δ.toEuclideanLin
  let Δ₁ : Matrix m n 𝕜 := toEuclideanLin.symm T₁
  let Δ₂ : Matrix m n 𝕜 := toEuclideanLin.symm T₂
  have hΔ₁ : Δ₁.toEuclideanLin = T₁ := toEuclideanLin.apply_symm_apply T₁
  have hΔ₂ : Δ₂.toEuclideanLin = T₂ := toEuclideanLin.apply_symm_apply T₂
  refine ⟨Δ₁, Δ₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply toEuclideanLin.injective
    rw [map_add, hΔ₁, hΔ₂, hsum]
  · rw [rank_eq_finrank_range_toEuclideanLin, hΔ₁]
    exact hrank
  · apply toEuclideanLin.injective
    rw [map_zero, toEuclideanLin, toLpLin_mul_same, ← toEuclideanLin, ← toEuclideanLin,
      toEuclideanLin_conjTranspose_eq_adjoint, hΔ₂]
    exact h₁
  · apply toEuclideanLin.injective
    rw [map_zero, toEuclideanLin, toLpLin_mul_same, ← toEuclideanLin, ← toEuclideanLin,
      toEuclideanLin_conjTranspose_eq_adjoint, hΔ₂]
    exact h₂
  · rw [frobenius_inner_eq_trace_conjTranspose_mul, ← trace_adjoint_comp_toEuclideanLin, hΔ₁, hΔ₂]
    exact htr
  · rw [map_add, hΔ₁, hΔ₂]
    exact hdec
  · rw [hΔ₁, ← frobenius_toEuclideanLin Δ]
    exact hnuc

end LowRankDecomposition

end Matrix
