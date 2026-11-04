/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Matrix.Laplace
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.Trotter
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Matrix Bernstein Inequalities

This file proves the **matrix Bernstein inequalities** for sums of independent, centered,
norm-bounded random matrices over `𝕜` (`ℝ` or `ℂ`), both in the Hermitian setting and for general
rectangular matrices via the Hermitian dilation.

## Mathematical overview

1. **Spectral characterization of the `ℓ²` operator norm**: For a Hermitian matrix `A`, unitary
   diagonalization gives `‖A‖ = ‖hA.eigenvalues‖`, so every eigenvalue satisfies `|λ_k(A)| ≤ ‖A‖`
   and (when the index type is nonempty) `‖A‖` or `-‖A‖` lies in `spectrum ℝ A`.
2. **Summand moment generating function bound**: If `Z` is an a.e. Hermitian random matrix with
   entrywise expectation `0` and `‖Z‖ ≤ L` a.e., then for `0 ≤ θ` with `θ * L < 3`, applying the
   scalar Bernstein bound `exp(θ x) ≤ 1 + θ x + g x²` (`g = θ² / (2 (1 - θ L / 3))`) via the
   continuous functional calculus and integrating entrywise yields
   `E[exp(θ Z)] ≤ 1 + g E[Z²] ≤ exp(g E[Z²])` in the Loewner order.
3. **Hermitian eigenvalue and operator-norm Bernstein bounds**: Feeding `M_i = g E[X_i²]` into the
   matrix Laplace transform bound
   (`ProbabilityTheory.iIndepFun.measureReal_exists_le_eigenvalues_sum_le`), bounding
   `∑_i E[X_i²] ≤ v • 1` where `v = ‖∑_i E[X_i²]‖`, and optimizing `θ = t / (v + L t / 3)` gives
   the upper-tail eigenvalue bound `d exp(-(t² / 2) / (v + L t / 3))`. Applying this to `±X`
   bounds the operator norm tail by `2 d exp(-(t² / 2) / (v + L t / 3))`.
4. **Hermitian dilation and rectangular matrix Bernstein**: For rectangular `Y : Matrix m n 𝕜`, the
   Hermitian dilation `Y.hermitianDilation = fromBlocks 0 Y Yᴴ 0` preserves the `ℓ²` operator norm,
   squares to `fromBlocks (Y * Yᴴ) 0 0 (Yᴴ * Y)`, and has chiral spectral symmetry (`-λ ∈ σ(D)`
   implies `λ ∈ σ(D)`). Hence `‖∑_i Y_i‖` is itself an eigenvalue of `∑_i Y_i.hermitianDilation`,
   giving the sharp prefactor `card m + card n` without doubling.

## Main definitions and results

* `Matrix.IsHermitian.l2_opNorm_eq_norm_eigenvalues`: `‖A‖ = ‖hA.eigenvalues‖`.
* `Matrix.l2_opNorm_fromBlocks_zero`: `‖fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖`.
* `Matrix.hermitianDilation`: the `(m ⊕ n) × (m ⊕ n)` Hermitian dilation `fromBlocks 0 A Aᴴ 0`.
* `Matrix.l2_opNorm_hermitianDilation`: `‖A.hermitianDilation‖ = ‖A‖`.
* `Matrix.integrable_and_posSemidef_exp_smul_integral_sub`: Loewner MGF bound for a centered,
  norm-bounded Hermitian random matrix.
* `ProbabilityTheory.iIndepFun.measureReal_exists_le_eigenvalues_sum_le_of_norm_le`: upper-tail
  eigenvalue Bernstein inequality for Hermitian summands.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le` / `TauCeti.matrix_bernstein`: two-sided
  operator-norm Bernstein inequality for Hermitian summands.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le_rectangular` /
  `TauCeti.matrix_bernstein_rectangular`: sharp rectangular matrix Bernstein inequality.

## References

* [J. A. Tropp, *User-friendly tail bounds for sums of random matrices*][tropp2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace Matrix

section SpectralNormAndDilation

variable {m₁ m₂ n₁ n₂ m n 𝕜 : Type*} [RCLike 𝕜]

/-- The `ℓ²` operator norm of a Hermitian matrix equals the `ℓ^∞` norm of its eigenvalues. -/
theorem IsHermitian.l2_opNorm_eq_norm_eigenvalues [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ‖A‖ = ‖hA.eigenvalues‖ := by
  let U : Matrix n n 𝕜 := hA.eigenvectorUnitary
  let D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU_mul : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hmul_U : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h1_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by simp
  have hU_le : ‖U‖ ≤ 1 := by
    have hsq : ‖U‖ ^ 2 ≤ 1 ^ 2 := by
      rw [sq, ← l2_opNorm_conjTranspose_mul_self, hU_mul, one_pow]
      exact h1_le
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq
  have hUh_le : ‖Uᴴ‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose]
  have hA_eq : A = U * D * Uᴴ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.spectral_theorem
  have hD_eq : D = Uᴴ * A * U := by
    rw [hA_eq]
    exact (calc Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp [Matrix.mul_assoc]
      _ = D := by simp [hU_mul]).symm
  have hD_norm : ‖D‖ = ‖hA.eigenvalues‖ := by
    rw [l2_opNorm_diagonal]
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
      simpa using norm_le_pi_norm hA.eigenvalues i
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
      simpa using norm_le_pi_norm (RCLike.ofReal (K := 𝕜) ∘ hA.eigenvalues) i
  refine le_antisymm ?_ ?_
  · rw [← hD_norm, hA_eq]
    calc ‖U * D * Uᴴ‖ ≤ ‖U * D‖ * ‖Uᴴ‖ := l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖D‖) * ‖Uᴴ‖ :=
          mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖D‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hU_le (norm_nonneg _)) hUh_le
            (norm_nonneg _) (by positivity)
      _ = ‖D‖ := by ring
  · rw [← hD_norm, hD_eq]
    calc ‖Uᴴ * A * U‖ ≤ ‖Uᴴ * A‖ * ‖U‖ := l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖A‖) * ‖U‖ :=
          mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖A‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hUh_le (norm_nonneg _)) hU_le
            (norm_nonneg _) (by positivity)
      _ = ‖A‖ := by ring

/-- Every eigenvalue of a Hermitian matrix has absolute value at most its `ℓ²` operator norm. -/
theorem IsHermitian.abs_eigenvalues_le_l2_opNorm [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) : |hA.eigenvalues i| ≤ ‖A‖ := by
  rw [hA.l2_opNorm_eq_norm_eigenvalues]
  exact norm_le_pi_norm hA.eigenvalues i

/-- For a Hermitian matrix `A` on a nonempty index type, either `‖A‖` or `-‖A‖` belongs to
`spectrum ℝ A`. -/
theorem IsHermitian.norm_or_neg_norm_mem_spectrum [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    ‖A‖ ∈ spectrum ℝ A ∨ -‖A‖ ∈ spectrum ℝ A := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ |hA.eigenvalues i|) Finset.univ_nonempty
  have hnorm_eq : ‖A‖ = |hA.eigenvalues k| := by
    rw [hA.l2_opNorm_eq_norm_eigenvalues]
    refine le_antisymm ?_ (norm_le_pi_norm hA.eigenvalues k)
    exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i ↦ hk i (Finset.mem_univ i)
  have hmem : hA.eigenvalues k ∈ spectrum ℝ A := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact Set.mem_range_self k
  rcases abs_cases (hA.eigenvalues k) with ⟨hpos, _⟩ | ⟨hneg, _⟩
  · left
    rwa [hnorm_eq, hpos]
  · right
    rw [hnorm_eq, hneg, neg_neg]
    exact hmem

/-- The `ℓ²` operator norm of a block-diagonal matrix `fromBlocks A 0 0 B` is `max ‖A‖ ‖B‖`. -/
@[simp]
theorem l2_opNorm_fromBlocks_zero [Fintype m₁] [Fintype m₂] [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (A : Matrix m₁ n₁ 𝕜) (B : Matrix m₂ n₂ 𝕜) :
    ‖Matrix.fromBlocks A (0 : Matrix m₁ n₂ 𝕜) (0 : Matrix m₂ n₁ 𝕜) B‖ = max ‖A‖ ‖B‖ := by
  set D := Matrix.fromBlocks A (0 : Matrix m₁ n₂ 𝕜) (0 : Matrix m₂ n₁ 𝕜) B
  let TD : EuclideanSpace 𝕜 (n₁ ⊕ n₂) →L[𝕜] EuclideanSpace 𝕜 (m₁ ⊕ m₂) :=
    (toEuclideanLin (𝕜 := 𝕜) (m := m₁ ⊕ m₂) (n := n₁ ⊕ n₂)).trans LinearMap.toContinuousLinearMap D
  let TA : EuclideanSpace 𝕜 n₁ →L[𝕜] EuclideanSpace 𝕜 m₁ :=
    (toEuclideanLin (𝕜 := 𝕜) (m := m₁) (n := n₁)).trans LinearMap.toContinuousLinearMap A
  let TB : EuclideanSpace 𝕜 n₂ →L[𝕜] EuclideanSpace 𝕜 m₂ :=
    (toEuclideanLin (𝕜 := 𝕜) (m := m₂) (n := n₂)).trans LinearMap.toContinuousLinearMap B
  have hTD_norm : ‖D‖ = ‖TD‖ := l2_opNorm_def D
  have hTA_norm : ‖A‖ = ‖TA‖ := l2_opNorm_def A
  have hTB_norm : ‖B‖ = ‖TB‖ := l2_opNorm_def B
  have hTD_ofLp (x : EuclideanSpace 𝕜 (n₁ ⊕ n₂)) : (TD x).ofLp = D *ᵥ x.ofLp := rfl
  have hTA_ofLp (x : EuclideanSpace 𝕜 n₁) : (TA x).ofLp = A *ᵥ x.ofLp := rfl
  have hTB_ofLp (x : EuclideanSpace 𝕜 n₂) : (TB x).ofLp = B *ᵥ x.ofLp := rfl
  refine le_antisymm ?_ (max_le_iff.mpr ⟨?_, ?_⟩)
  · rw [hTD_norm]
    refine TD.opNorm_le_bound (by positivity) fun x ↦ ?_
    let x₁ : EuclideanSpace 𝕜 n₁ := WithLp.toLp 2 (x.ofLp ∘ Sum.inl)
    let x₂ : EuclideanSpace 𝕜 n₂ := WithLp.toLp 2 (x.ofLp ∘ Sum.inr)
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    have hx_sq : ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂, Function.comp_apply]
    have hDx_sq : ‖TD x‖ ^ 2 = ‖TA x₁‖ ^ 2 + ‖TB x₂‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, hTD_ofLp, hTA_ofLp, hTB_ofLp, D, fromBlocks_mulVec,
        zero_mulVec, add_zero, zero_add, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, x₁, x₂]
    have hA_le : ‖TA x₁‖ ≤ max ‖A‖ ‖B‖ * ‖x₁‖ := by
      calc ‖TA x₁‖ ≤ ‖TA‖ * ‖x₁‖ := TA.le_opNorm x₁
        _ = ‖A‖ * ‖x₁‖ := by rw [← hTA_norm]
        _ ≤ max ‖A‖ ‖B‖ * ‖x₁‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have hB_le : ‖TB x₂‖ ≤ max ‖A‖ ‖B‖ * ‖x₂‖ := by
      calc ‖TB x₂‖ ≤ ‖TB‖ * ‖x₂‖ := TB.le_opNorm x₂
        _ = ‖B‖ * ‖x₂‖ := by rw [← hTB_norm]
        _ ≤ max ‖A‖ ‖B‖ * ‖x₂‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hA_sq : ‖TA x₁‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x₁‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA_le 2
    have hB_sq : ‖TB x₂‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x₂‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hB_le 2
    calc ‖TD x‖ ^ 2 = ‖TA x₁‖ ^ 2 + ‖TB x₂‖ ^ 2 := hDx_sq
      _ ≤ (max ‖A‖ ‖B‖ * ‖x₁‖) ^ 2 + (max ‖A‖ ‖B‖ * ‖x₂‖) ^ 2 := add_le_add hA_sq hB_sq
      _ = max ‖A‖ ‖B‖ ^ 2 * (‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by ring
      _ = (max ‖A‖ ‖B‖ * ‖x‖) ^ 2 := by rw [mul_pow, hx_sq]
  · rw [hTA_norm]
    refine TA.opNorm_le_bound (norm_nonneg _) fun x₁ ↦ ?_
    let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := WithLp.toLp 2 (Sum.elim x₁.ofLp 0)
    have hx_norm : ‖x‖ = ‖x₁‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x]
    have hDx_norm : ‖TD x‖ = ‖TA x₁‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      have hinl : (Sum.elim x₁.ofLp (0 : n₂ → 𝕜)) ∘ Sum.inl = x₁.ofLp := by ext; rfl
      have hinr : (Sum.elim x₁.ofLp (0 : n₂ → 𝕜)) ∘ Sum.inr = 0 := by ext; rfl
      simp [EuclideanSpace.norm_sq_eq, hTD_ofLp, hTA_ofLp, D, fromBlocks_mulVec,
        Fintype.sum_sum_type, x, hinl, hinr]
    calc ‖TA x₁‖ = ‖TD x‖ := hDx_norm.symm
      _ ≤ ‖TD‖ * ‖x‖ := TD.le_opNorm x
      _ = ‖D‖ * ‖x₁‖ := by rw [← hTD_norm, hx_norm]
  · rw [hTB_norm]
    refine TB.opNorm_le_bound (norm_nonneg _) fun x₂ ↦ ?_
    let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := WithLp.toLp 2 (Sum.elim 0 x₂.ofLp)
    have hx_norm : ‖x‖ = ‖x₂‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x]
    have hDx_norm : ‖TD x‖ = ‖TB x₂‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      have hinl : (Sum.elim (0 : n₁ → 𝕜) x₂.ofLp) ∘ Sum.inl = 0 := by ext; rfl
      have hinr : (Sum.elim (0 : n₁ → 𝕜) x₂.ofLp) ∘ Sum.inr = x₂.ofLp := by ext; rfl
      simp [EuclideanSpace.norm_sq_eq, hTD_ofLp, hTB_ofLp, D, fromBlocks_mulVec,
        Fintype.sum_sum_type, x, hinl, hinr]
    calc ‖TB x₂‖ = ‖TD x‖ := hDx_norm.symm
      _ ≤ ‖TD‖ * ‖x‖ := TD.le_opNorm x
      _ = ‖D‖ * ‖x₂‖ := by rw [← hTD_norm, hx_norm]

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular `m × n` matrix `A`, producing a
square `(m ⊕ n) × (m ⊕ n)` Hermitian matrix with the same `ℓ²` operator norm. -/
def hermitianDilation (A : Matrix m n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  Matrix.fromBlocks 0 A Aᴴ 0

/-- The Hermitian dilation of any matrix is Hermitian. -/
theorem isHermitian_hermitianDilation (A : Matrix m n 𝕜) : A.hermitianDilation.IsHermitian := by
  ext (i | i) (j | j) <;> simp [hermitianDilation]

/-- The Hermitian dilation of the zero matrix is zero. -/
@[simp]
theorem hermitianDilation_zero : (0 : Matrix m n 𝕜).hermitianDilation = 0 := by
  ext (i | i) (j | j) <;> simp [hermitianDilation]

/-- The Hermitian dilation is additive. -/
theorem hermitianDilation_add (A B : Matrix m n 𝕜) :
    (A + B).hermitianDilation = A.hermitianDilation + B.hermitianDilation := by
  simp [hermitianDilation, conjTranspose_add, fromBlocks_add]

/-- The Hermitian dilation commutes with finite sums. -/
theorem hermitianDilation_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix m n 𝕜) :
    (∑ i ∈ s, f i).hermitianDilation = ∑ i ∈ s, (f i).hermitianDilation := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih => rw [Finset.sum_cons, hermitianDilation_add, ih, Finset.sum_cons]

/-- The square of `A.hermitianDilation` is the block-diagonal matrix
`fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A)`. -/
theorem hermitianDilation_mul_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    A.hermitianDilation * A.hermitianDilation = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  simp [hermitianDilation, fromBlocks_multiply]

/-- The Hermitian dilation preserves the `ℓ²` operator norm: `‖A.hermitianDilation‖ = ‖A‖`. -/
@[simp]
theorem l2_opNorm_hermitianDilation [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ‖A.hermitianDilation‖ = ‖A‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hsq : ‖A.hermitianDilation‖ ^ 2 = ‖A.hermitianDilation * A.hermitianDilation‖ := by
    rw [sq, ← l2_opNorm_conjTranspose_mul_self, (isHermitian_hermitianDilation A).eq]
  have hAAh : ‖A * Aᴴ‖ = ‖A‖ ^ 2 := by
    calc ‖A * Aᴴ‖ = ‖(Aᴴ)ᴴ * Aᴴ‖ := by rw [conjTranspose_conjTranspose]
      _ = ‖Aᴴ‖ * ‖Aᴴ‖ := l2_opNorm_conjTranspose_mul_self Aᴴ
      _ = ‖A‖ ^ 2 := by rw [l2_opNorm_conjTranspose, sq]
  have hAhA : ‖Aᴴ * A‖ = ‖A‖ ^ 2 := by
    rw [l2_opNorm_conjTranspose_mul_self, sq]
  rw [hsq, hermitianDilation_mul_self, l2_opNorm_fromBlocks_zero, hAAh, hAhA, max_self]

/-- The Hermitian dilation map is continuous with respect to the entrywise/product topology. -/
theorem continuous_hermitianDilation :
    Continuous (hermitianDilation (m := m) (n := n) (𝕜 := 𝕜)) := by
  refine continuous_matrix fun p q ↦ ?_
  cases p with
  | inl p₁ =>
    cases q with
    | inl _ => exact continuous_const
    | inr q₂ => exact (continuous_apply q₂).comp (continuous_apply p₁)
  | inr p₂ =>
    cases q with
    | inl q₁ =>
      -- Unfold the `(inr p₂, inl q₁)` block entry to `star (A q₁ p₂)`.
      change Continuous fun A : Matrix m n 𝕜 ↦ (starRingEnd 𝕜) (A q₁ p₂)
      simp only [RCLike.star_def.symm]
      exact continuous_star.comp ((continuous_apply p₂).comp (continuous_apply q₁))
    | inr _ => exact continuous_const

/-- Chiral symmetry of the Hermitian dilation: if `-x` lies in the real spectrum of
`A.hermitianDilation`, then so does `x`. -/
theorem mem_spectrum_hermitianDilation_of_neg_mem [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {A : Matrix m n 𝕜} {x : ℝ}
    (hx :
      letI : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal;
      -x ∈ spectrum ℝ A.hermitianDilation) :
    letI : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
    x ∈ spectrum ℝ A.hermitianDilation := by
  let : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
  let J : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜)
  have hJJ : J * J = 1 := by simp [J, fromBlocks_multiply]
  let u : (Matrix (m ⊕ n) (m ⊕ n) 𝕜)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hconj : J * A.hermitianDilation * J = -A.hermitianDilation := by
    simp [J, hermitianDilation, fromBlocks_multiply, fromBlocks_neg]
  rw [spectrum.mem_iff] at hx ⊢
  intro hunit
  apply hx
  have hid : algebraMap ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) (-x) - A.hermitianDilation =
      -(J * (algebraMap ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) x - A.hermitianDilation) * J) := by
    rw [map_neg, Matrix.mul_sub, Matrix.sub_mul, hconj, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hJJ]
    abel
  rw [hid, IsUnit.neg_iff]
  exact (u.isUnit.mul hunit).mul u.isUnit

end SpectralNormAndDilation

section SummandMGF

variable {Ω n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

private def entryCLM' (i j : n) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap :=
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := (continuous_apply j).comp (continuous_apply i) }

private theorem cfc_exp_smul_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    cfc (fun x : ℝ ↦ Real.exp (θ * x)) A = NormedSpace.exp (θ • A) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hθA : IsSelfAdjoint (θ • A) := (hA.smul (IsSelfAdjoint.all θ)).isSelfAdjoint
  rw [← CFC.real_exp_eq_normedSpace_exp hθA, ← cfc_smul_id (R := ℝ) θ A hA.isSelfAdjoint,
    ← cfc_comp' Real.exp (θ • ·) A Real.continuous_exp.continuousOn
      (continuous_const_smul θ).continuousOn hA.isSelfAdjoint]
  rfl

/-- **Summand MGF Loewner bound for Matrix Bernstein.** If `Z` is an a.e. Hermitian random matrix
with entrywise expectation `0` and `‖Z‖ ≤ L` a.e., then for `0 ≤ θ` with `θ * L < 3` and
`g = θ ^ 2 / (2 * (1 - θ * L / 3))`, `exp (θ • Z)` and `Z * Z` are Bochner integrable, the matrix
second moment `V = E[Z²]` is positive semidefinite, and `E[exp(θ • Z)] ≤ exp(g • V)` in the
Loewner order. -/
theorem integrable_and_posSemidef_exp_smul_integral_sub [IsProbabilityMeasure μ]
    {Z : Ω → Matrix n n 𝕜} {L θ : ℝ} (hZ_meas : AEMeasurable Z μ)
    (hZ_herm : ∀ᵐ ω ∂μ, (Z ω).IsHermitian) (hZ_mean : ∀ p q, ∫ ω, Z ω p q ∂μ = 0)
    (hZ_norm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ L) (hθ0 : 0 ≤ θ) (hθL : θ * L < 3) :
    let g := θ ^ 2 / (2 * (1 - θ * L / 3))
    let V := Matrix.of fun p q ↦ ∫ ω, (Z ω * Z ω) p q ∂μ
    Integrable (fun ω ↦ NormedSpace.exp (θ • Z ω)) μ ∧
      Integrable (fun ω ↦ Z ω * Z ω) μ ∧
      V.PosSemidef ∧
      (NormedSpace.exp (g • V) -
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ).PosSemidef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  obtain ⟨ω₀, hω₀⟩ := hZ_norm.exists
  have hL : 0 ≤ L := (norm_nonneg _).trans hω₀
  set g : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  set V : Matrix n n 𝕜 := Matrix.of fun p q ↦ ∫ ω, (Z ω * Z ω) p q ∂μ
  have hZ_int : Integrable Z μ := Integrable.of_bound hZ_meas.aestronglyMeasurable L hZ_norm
  have hZ2_int : Integrable (fun ω ↦ Z ω * Z ω) μ := by
    refine Integrable.of_bound (hZ_meas.aestronglyMeasurable.mul hZ_meas.aestronglyMeasurable)
      (L * L) (hZ_norm.mono fun ω hω ↦ ?_)
    exact (norm_mul_le _ _).trans (mul_le_mul hω hω (norm_nonneg _) hL)
  have hexp_int : Integrable (fun ω ↦ NormedSpace.exp (θ • Z ω)) μ := by
    have hcont : Continuous (fun A : Matrix n n 𝕜 ↦ NormedSpace.exp (θ • A)) :=
      NormedSpace.exp_continuous.comp (continuous_const_smul θ)
    refine Integrable.of_bound (hcont.comp_aestronglyMeasurable hZ_meas.aestronglyMeasurable)
      (Real.exp (θ * L) + ‖(1 : Matrix n n 𝕜)‖) (hZ_norm.mono fun ω hω ↦ ?_)
    have hsub := NormedSpace.norm_exp_sub_one_le (θ • Z ω)
    have hθZ : ‖θ • Z ω‖ ≤ θ * L := by
      rw [norm_smul, Real.norm_of_nonneg hθ0]
      exact mul_le_mul_of_nonneg_left hω hθ0
    have hexp_le : Real.exp ‖θ • Z ω‖ ≤ Real.exp (θ * L) := Real.exp_le_exp.mpr hθZ
    calc ‖NormedSpace.exp (θ • Z ω)‖
        ≤ ‖NormedSpace.exp (θ • Z ω) - 1‖ + ‖(1 : Matrix n n 𝕜)‖ := norm_le_norm_sub_add _ _
      _ ≤ Real.exp ‖θ • Z ω‖ - 1 + ‖(1 : Matrix n n 𝕜)‖ := by linarith
      _ ≤ Real.exp (θ * L) + ‖(1 : Matrix n n 𝕜)‖ := by linarith
  have hV_psd : V.PosSemidef := by
    refine TauCeti.posSemidef_integral ?_ fun p q ↦ (entryCLM' p q).integrable_comp hZ2_int
    filter_upwards [hZ_herm] with ω hω
    simpa [hω.eq] using Matrix.posSemidef_conjTranspose_mul_self (Z ω)
  -- Pointwise a.e. Loewner bound `exp(θ • Z ω) ≤ 1 + θ • Z ω + g • (Z ω * Z ω)`.
  let W : Ω → Matrix n n 𝕜 := fun ω ↦
    1 + θ • Z ω + g • (Z ω * Z ω) - NormedSpace.exp (θ • Z ω)
  have hW_psd : ∀ᵐ ω ∂μ, (W ω).PosSemidef := by
    filter_upwards [hZ_herm, hZ_norm] with ω hω_herm hω_norm
    have ha : IsSelfAdjoint (Z ω) := hω_herm.isSelfAdjoint
    have hcfc_le : cfc (fun x : ℝ ↦ Real.exp (θ * x)) (Z ω) ≤
        cfc (fun x : ℝ ↦ (1 + θ * x) + g * x ^ 2) (Z ω) := by
      refine cfc_mono fun x hx ↦ ?_
      rw [hω_herm.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨k, rfl⟩ := hx
      have hxL : hω_herm.eigenvalues k ≤ L :=
        (le_abs_self _).trans ((hω_herm.abs_eigenvalues_le_l2_opNorm k).trans hω_norm)
      have hθxL : θ * hω_herm.eigenvalues k ≤ θ * L := mul_le_mul_of_nonneg_left hxL hθ0
      have hquad := Real.exp_le_one_add_add_sq_div_of_le hθxL (mul_nonneg hθ0 hL) hθL
      have hring : (θ * hω_herm.eigenvalues k) ^ 2 / (2 * (1 - θ * L / 3)) =
          g * hω_herm.eigenvalues k ^ 2 := by
        dsimp only [g]
        ring
      linarith
    have hquad_cfc : cfc (fun x : ℝ ↦ (1 + θ * x) + g * x ^ 2) (Z ω) =
        1 + θ • Z ω + g • (Z ω * Z ω) := by
      have hc1 : ContinuousOn (fun x : ℝ ↦ 1 + θ * x) (spectrum ℝ (Z ω)) :=
        continuousOn_const.add (continuous_const.mul continuous_id).continuousOn
      have hc2 : ContinuousOn (fun x : ℝ ↦ g * x ^ 2) (spectrum ℝ (Z ω)) :=
        (continuous_const.mul (continuous_pow 2)).continuousOn
      rw [cfc_add (Z ω) (fun x : ℝ ↦ 1 + θ * x) (fun x : ℝ ↦ g * x ^ 2) hc1 hc2,
        cfc_const_add (1 : ℝ) (fun x : ℝ ↦ θ * x) (Z ω)
          (continuous_const.mul continuous_id).continuousOn ha,
        Algebra.algebraMap_eq_smul_one, one_smul, cfc_const_mul_id θ (Z ω) ha,
        cfc_const_mul g (· ^ 2 : ℝ → ℝ) (Z ω) (continuous_pow 2).continuousOn,
        cfc_pow_id (Z ω) 2 ha, sq]
    rw [cfc_exp_smul_eq hω_herm θ, hquad_cfc, Matrix.le_iff] at hcfc_le
    exact hcfc_le
  have h1_int : Integrable (fun _ : Ω ↦ (1 : Matrix n n 𝕜)) μ := integrable_const 1
  have hθZ_int : Integrable (fun ω ↦ θ • Z ω) μ := hZ_int.smul θ
  have hgZ2_int : Integrable (fun ω ↦ g • (Z ω * Z ω)) μ := hZ2_int.smul g
  have hW_int : Integrable W μ := ((h1_int.add hθZ_int).add hgZ2_int).sub hexp_int
  have hEW_psd : (Matrix.of fun p q ↦ ∫ ω, W ω p q ∂μ).PosSemidef :=
    TauCeti.posSemidef_integral hW_psd fun p q ↦ (entryCLM' p q).integrable_comp hW_int
  have hEW_eq : (Matrix.of fun p q ↦ ∫ ω, W ω p q ∂μ) =
      1 + g • V - Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := by
    have hEZ_zero : ∫ ω, Z ω ∂μ = 0 := by
      ext p q
      exact ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hZ_int).symm.trans (hZ_mean p q)
    have hEZ2_eq : ∫ ω, (Z ω * Z ω) ∂μ = V := by
      ext p q
      exact ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hZ2_int).symm
    have hEexp_eq : ∫ ω, NormedSpace.exp (θ • Z ω) ∂μ =
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := by
      ext p q
      exact ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hexp_int).symm
    have hEW_bochner : ∫ ω, W ω ∂μ =
        1 + g • V - Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := by
      have hsub1 : ∫ ω, W ω ∂μ =
          ∫ ω, ((1 : Matrix n n 𝕜) + θ • Z ω + g • (Z ω * Z ω)) ∂μ -
            ∫ ω, NormedSpace.exp (θ • Z ω) ∂μ :=
        integral_sub (f := fun ω ↦ (1 : Matrix n n 𝕜) + θ • Z ω + g • (Z ω * Z ω))
          (g := fun ω ↦ NormedSpace.exp (θ • Z ω)) (h1_int.add hθZ_int |>.add hgZ2_int) hexp_int
      have hadd1 : ∫ ω, ((1 : Matrix n n 𝕜) + θ • Z ω + g • (Z ω * Z ω)) ∂μ =
          ∫ ω, ((1 : Matrix n n 𝕜) + θ • Z ω) ∂μ + ∫ ω, g • (Z ω * Z ω) ∂μ :=
        integral_add (f := fun ω ↦ (1 : Matrix n n 𝕜) + θ • Z ω)
          (g := fun ω ↦ g • (Z ω * Z ω)) (h1_int.add hθZ_int) hgZ2_int
      have hadd2 : ∫ ω, ((1 : Matrix n n 𝕜) + θ • Z ω) ∂μ =
          ∫ _ : Ω, (1 : Matrix n n 𝕜) ∂μ + ∫ ω, θ • Z ω ∂μ :=
        integral_add (f := fun _ ↦ (1 : Matrix n n 𝕜)) (g := fun ω ↦ θ • Z ω) h1_int hθZ_int
      rw [hsub1, hadd1, hadd2, integral_const, probReal_univ, one_smul, integral_smul, hEZ_zero,
        smul_zero, add_zero, integral_smul, hEZ2_eq, hEexp_eq]
    ext p q
    rw [Matrix.of_apply, ← hEW_bochner]
    exact (entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hW_int
  rw [hEW_eq] at hEW_psd
  -- Bound `1 + g • V ≤ exp (g • V)` via `1 + x ≤ exp x` in the continuous functional calculus.
  have hgV_sa : IsSelfAdjoint (g • V) := (hV_psd.1.smul (IsSelfAdjoint.all g)).isSelfAdjoint
  have hexp_ge_lin : (NormedSpace.exp (g • V) - (1 + g • V)).PosSemidef := by
    have hcfc_le : cfc (fun x : ℝ ↦ 1 + x) (g • V) ≤ cfc Real.exp (g • V) :=
      cfc_mono fun x _ ↦ by linarith [Real.add_one_le_exp x]
    have hlin_cfc : cfc (fun x : ℝ ↦ 1 + x) (g • V) = 1 + g • V := by
      rw [cfc_const_add (1 : ℝ) (fun x : ℝ ↦ x) (g • V) continuousOn_id hgV_sa,
        Algebra.algebraMap_eq_smul_one, one_smul, cfc_id' ℝ (g • V) hgV_sa]
    rw [hlin_cfc, CFC.real_exp_eq_normedSpace_exp hgV_sa, Matrix.le_iff] at hcfc_le
    exact hcfc_le
  refine ⟨hexp_int, hZ2_int, hV_psd, ?_⟩
  simpa only [sub_add_sub_cancel] using hexp_ge_lin.add hEW_psd

end SummandMGF

end Matrix

namespace ProbabilityTheory.iIndepFun

section Bernstein

variable {ι Ω m n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

private def diagEntryCLM (p : n) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap :=
      { toFun := fun A ↦ A p p
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := (continuous_apply p).comp (continuous_apply p) }

private theorem not_exists_le_eigenvalues_zero {t : ℝ} (ht : 0 < t) :
    ¬ ∃ k : n, ∃ hS : (0 : Matrix n n 𝕜).IsHermitian, t ≤ hS.eigenvalues k := by
  rintro ⟨k, hS, htk⟩
  have hle : hS.eigenvalues k ≤ 0 := by
    have hnorm := hS.abs_eigenvalues_le_l2_opNorm k
    rw [norm_zero] at hnorm
    exact (le_abs_self _).trans hnorm
  linarith

omit [DecidableEq n] in
private theorem re_mul_self_diag_eq_sum_norm_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : n) :
    RCLike.re ((A * A) p p) = ∑ q : n, ‖A p q‖ ^ 2 := by
  have hdiag : (A * A) p p = ∑ q : n, ((‖A p q‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hqp : A q p = star (A p q) := by
      have h := hA.apply q p
      simpa [Matrix.conjTranspose_apply] using h.symm
    rw [hqp, RCLike.star_def, RCLike.mul_conj]
    norm_cast
  rw [hdiag, map_sum]
  simp only [RCLike.ofReal_re]

private theorem ae_eq_zero_of_integral_mul_self_eq_zero [IsProbabilityMeasure μ]
    {Z : Ω → Matrix n n 𝕜} (hZ_herm : ∀ᵐ ω ∂μ, (Z ω).IsHermitian)
    (hZ2_int : Integrable (fun ω ↦ Z ω * Z ω) μ)
    (hV_diag : ∀ p : n, RCLike.re (∫ ω, (Z ω * Z ω) p p ∂μ) = 0) :
    Z =ᵐ[μ] 0 := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hentry_zero (p q : n) : ∀ᵐ ω ∂μ, Z ω p q = 0 := by
    have hdiag_int : Integrable (fun ω ↦ (Z ω * Z ω) p p) μ :=
      (diagEntryCLM p).integrable_comp hZ2_int
    let f : Ω → ℝ := fun ω ↦ RCLike.re ((Z ω * Z ω) p p)
    have hf_int : Integrable f μ := RCLike.reCLM.integrable_comp hdiag_int
    have hf_nonneg : 0 ≤ᵐ[μ] f := hZ_herm.mono fun ω hω ↦ by
      -- Unfold `f` to rewrite the diagonal of `(Z ω)²` as a sum of squared norms.
      change 0 ≤ RCLike.re ((Z ω * Z ω) p p)
      rw [re_mul_self_diag_eq_sum_norm_sq hω p]
      exact Finset.sum_nonneg fun r _ ↦ sq_nonneg _
    have hf_int_eq : ∫ ω, f ω ∂μ = 0 := by
      have hcomm : ∫ ω, f ω ∂μ = RCLike.re (∫ ω, (Z ω * Z ω) p p ∂μ) :=
        RCLike.reCLM.integral_comp_comm hdiag_int
      rw [hcomm, hV_diag p]
    have hf_ae_zero : f =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hf_nonneg hf_int).mp hf_int_eq
    filter_upwards [hZ_herm, hf_ae_zero] with ω hω hzero
    have hsum_zero : ∑ r : n, ‖Z ω p r‖ ^ 2 = 0 := by
      rw [← re_mul_self_diag_eq_sum_norm_sq hω p]
      exact hzero
    have hterm_zero : ‖Z ω p q‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun r _ ↦ sq_nonneg _)).mp hsum_zero q (Finset.mem_univ q)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hterm_zero)
  have hall : ∀ᵐ ω ∂μ, ∀ p q, Z ω p q = 0 :=
    Filter.eventually_all.mpr fun p ↦ Filter.eventually_all.mpr fun q ↦ hentry_zero p q
  exact hall.mono fun ω hω ↦ Matrix.ext fun p q ↦ hω p q

private theorem re_trace_exp_smul_one (r : ℝ) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    RCLike.re (NormedSpace.exp (r • (1 : Matrix n n 𝕜))).trace =
      Fintype.card n * Real.exp r := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hexp : NormedSpace.exp (r • (1 : Matrix n n 𝕜)) = Real.exp r • (1 : Matrix n n 𝕜) := by
    have hr : Real.exp r = NormedSpace.exp r := congr_fun Real.exp_eq_exp_ℝ r
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm, ← hr,
      Algebra.algebraMap_eq_smul_one]
  rw [hexp, Matrix.trace_smul, Matrix.trace_one, RCLike.smul_re, RCLike.natCast_re, mul_comm]

/-- **Upper-tail Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4). For independent
a.e.-measurable, a.e.-Hermitian random `n × n` matrices `X i` (`i ∈ s`) with entrywise mean zero
and `‖X i‖ ≤ L` a.e., let `v = ‖∑ i ∈ s, E[(X i)²]‖`. For every `t > 0`, the probability that
`∑ i ∈ s, X i` has an eigenvalue at least `t` is at most
`card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_exists_le_eigenvalues_sum_le_of_norm_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {L t : ℝ}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i ∈ s, ∀ p q, ∫ ω, X i ω p q ∂μ = 0)
    (hX_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L) (ht : 0 < t) :
    let v := ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖
    μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set V_i : ι → Matrix n n 𝕜 := fun i ↦ Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ
  set V : Matrix n n 𝕜 := ∑ i ∈ s, V_i i
  set v : ℝ := ‖V‖
  by_cases hs : s.Nonempty
  · by_cases hv : v = 0
    · -- Degenerate zero-variance case: `V = 0` forces `X i =ᵐ 0` for all `i ∈ s`.
      have hV_zero : V = 0 := norm_eq_zero.mp hv
      have h0_step (i : ι) (hi : i ∈ s) :=
        Matrix.integrable_and_posSemidef_exp_smul_integral_sub (θ := 0) (hX_meas i hi)
          (hX_herm i hi) (hX_mean i hi) (hX_norm i hi) le_rfl (by norm_num)
      have hVi_psd (i : ι) (hi : i ∈ s) : (V_i i).PosSemidef := (h0_step i hi).2.2.1
      have hX_ae_zero (i : ι) (hi : i ∈ s) : X i =ᵐ[μ] 0 := by
        refine ae_eq_zero_of_integral_mul_self_eq_zero (hX_herm i hi) (h0_step i hi).2.1 fun p ↦ ?_
        have hdiag_nonneg (j : ι) (hj : j ∈ s) : 0 ≤ RCLike.re (V_i j p p) := by
          have h := (hVi_psd j hj).dotProduct_mulVec_nonneg (Pi.single p 1)
          simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using (RCLike.nonneg_iff.mp h).1
        have hsum_diag : ∑ j ∈ s, RCLike.re (V_i j p p) = 0 := by
          have hVp : V p p = 0 := by rw [hV_zero]; rfl
          simpa [V, Matrix.sum_apply] using congrArg RCLike.re hVp
        exact (Finset.sum_eq_zero_iff_of_nonneg hdiag_nonneg).mp hsum_diag i hi
      have hsum_ae_zero : ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω = 0 := by
        filter_upwards [(Filter.eventually_all_finset s).2 hX_ae_zero] with ω hω
        exact Finset.sum_eq_zero hω
      have hev_null :
          μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} = 0 := by
        rw [measureReal_eq_zero_iff]
        refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.mp hsum_ae_zero)
        intro hsum0
        rw [Set.mem_ofPred, hsum0] at hω
        exact not_exists_le_eigenvalues_zero ht hω
      rw [hev_null]
      positivity
    · -- Main case `0 < v`: optimize `θ = t / (v + L * t / 3)`.
      have hv_pos : 0 < v := lt_of_le_of_ne (norm_nonneg V) (Ne.symm hv)
      obtain ⟨i₀, hi₀⟩ := hs
      obtain ⟨ω₀, hω₀⟩ := (hX_norm i₀ hi₀).exists
      have hL : 0 ≤ L := (norm_nonneg _).trans hω₀
      have hdenom_pos : 0 < v + L * t / 3 := by positivity
      let θ : ℝ := t / (v + L * t / 3)
      have hθ0 : 0 ≤ θ := by positivity
      have hθL : θ * L < 3 := by
        dsimp only [θ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom_pos]
        linarith
      let g : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
      have h1_pos : 0 < 1 - θ * L / 3 := by linarith
      have hg0 : 0 ≤ g := by positivity
      have hstep (i : ι) (hi : i ∈ s) :=
        Matrix.integrable_and_posSemidef_exp_smul_integral_sub (hX_meas i hi) (hX_herm i hi)
          (hX_mean i hi) (hX_norm i hi) hθ0 hθL
      have hVi_psd (i : ι) (hi : i ∈ s) : (V_i i).PosSemidef := (hstep i hi).2.2.1
      have hlap := h_indep.measureReal_exists_le_eigenvalues_sum_le (t := t)
        (M := fun i ↦ g • V_i i) hX_meas hX_herm
        (fun i hi ↦ (hstep i hi).1)
        (fun i hi ↦ (hVi_psd i hi).1.smul (IsSelfAdjoint.all g))
        (fun i hi ↦ (hstep i hi).2.2.2) hθ0
      have hV_psd : V.PosSemidef :=
        Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h₁ h₂ ↦ h₁.add h₂)
          Matrix.PosSemidef.zero hVi_psd
      have hV_le_norm : ((g * v) • (1 : Matrix n n 𝕜) - g • V).PosSemidef := by
        have hv1 : (v • (1 : Matrix n n 𝕜) - V).PosSemidef := by
          have hcfc_le : cfc (fun x : ℝ ↦ x) V ≤ cfc (fun _ : ℝ ↦ v) V := by
            refine cfc_mono fun x hx ↦ ?_
            rw [hV_psd.1.spectrum_real_eq_range_eigenvalues] at hx
            obtain ⟨k, rfl⟩ := hx
            exact (le_abs_self _).trans (hV_psd.1.abs_eigenvalues_le_l2_opNorm k)
          rw [cfc_id' ℝ V hV_psd.1.isSelfAdjoint, cfc_const v V hV_psd.1.isSelfAdjoint,
            Algebra.algebraMap_eq_smul_one, Matrix.le_iff] at hcfc_le
          exact hcfc_le
        have hsmul : (g • (v • (1 : Matrix n n 𝕜) - V)).PosSemidef := hv1.smul hg0
        simpa [smul_sub, smul_smul] using hsmul
      have hgV_herm : (g • V).IsHermitian := hV_psd.1.smul (IsSelfAdjoint.all g)
      have hgv1_herm : ((g * v) • (1 : Matrix n n 𝕜)).IsHermitian :=
        Matrix.isHermitian_one.smul (IsSelfAdjoint.all (g * v))
      have htr_mono : RCLike.re (NormedSpace.exp (∑ i ∈ s, g • V_i i)).trace ≤
          Fintype.card n * Real.exp (g * v) := by
        rw [← Finset.smul_sum]
        exact (hgV_herm.re_trace_exp_mono hgv1_herm hV_le_norm).trans_eq
          (re_trace_exp_smul_one (g * v))
      have hexp_alg : -θ * t + g * v = -(t ^ 2 / 2) / (v + L * t / 3) := by
        have hsub_eq : 1 - θ * L / 3 = v / (v + L * t / 3) := by
          dsimp only [θ]
          field_simp
          ring
        dsimp only [g]
        rw [hsub_eq]
        dsimp only [θ]
        field_simp
        ring
      calc μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k}
          ≤ Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ i ∈ s, g • V_i i)).trace := hlap
        _ ≤ Real.exp (-θ * t) * (Fintype.card n * Real.exp (g * v)) :=
            mul_le_mul_of_nonneg_left htr_mono (Real.exp_pos _).le
        _ = Fintype.card n * Real.exp (-θ * t + g * v) := by
            rw [Real.exp_add]
            ring
        _ = Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by rw [hexp_alg]
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    have hempty :
        {ω : Ω | ∃ k : n, ∃ hS : (∑ i ∈ (∅ : Finset ι), X i ω).IsHermitian,
          t ≤ hS.eigenvalues k} = ∅ := by
      ext ω
      simp only [Finset.sum_empty, Set.mem_ofPred, Set.mem_empty_iff_false, iff_false]
      exact not_exists_le_eigenvalues_zero ht
    rw [hempty, measureReal_empty]
    positivity

private theorem neg_mem_spectrum_neg {S : Matrix n n 𝕜} {x : ℝ}
    (hx :
      letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal;
      -x ∈ spectrum ℝ S) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    x ∈ spectrum ℝ (-S) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [spectrum.mem_iff] at hx ⊢
  intro hunit
  apply hx
  have hid : algebraMap ℝ (Matrix n n 𝕜) (-x) - S = -(algebraMap ℝ (Matrix n n 𝕜) x - -S) := by
    rw [map_neg]
    abel
  rw [hid, IsUnit.neg_iff]
  exact hunit

/-- **Two-sided Hermitian matrix Bernstein inequality** over a `Finset` (Tropp 2012, Theorem 1.4).
For independent a.e.-measurable, a.e.-Hermitian random `n × n` matrices `X i` (`i ∈ s`) with
entrywise mean zero and `‖X i‖ ≤ L` a.e., let `v = ‖∑ i ∈ s, E[(X i)²]‖`. For every `t > 0`,
`μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖} ≤ 2 * card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_norm_sum_ge_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {L t : ℝ}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i ∈ s, ∀ p q, ∫ ω, X i ω p q ∂μ = 0)
    (hX_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L) (ht : 0 < t) :
    let v := ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖} ≤
      2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  by_cases hn : Nonempty n
  · let Epos := {ω : Ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k}
    let Eneg := {ω : Ω | ∃ k : n, ∃ hS : (∑ i ∈ s, -X i ω).IsHermitian, t ≤ hS.eigenvalues k}
    let H := {ω : Ω | ∀ i ∈ s, (X i ω).IsHermitian}
    have hHc_null : μ.real Hᶜ = 0 := by
      rw [measureReal_eq_zero_iff]
      exact ae_iff.mp ((Filter.eventually_all_finset s).2 hX_herm)
    have hsub : {ω : Ω | t ≤ ‖∑ i ∈ s, X i ω‖} ⊆ (Epos ∪ Eneg) ∪ Hᶜ := by
      intro ω hω
      by_cases hωH : ω ∈ H
      · left
        set S := ∑ i ∈ s, X i ω
        have hS : S.IsHermitian := by
          refine Finset.sum_induction _ Matrix.IsHermitian (fun _ _ h₁ h₂ ↦ h₁.add h₂)
            Matrix.isHermitian_zero hωH
        rcases hS.norm_or_neg_norm_mem_spectrum with hmem | hmem
        · left
          rw [hS.spectrum_real_eq_range_eigenvalues] at hmem
          obtain ⟨k, hk⟩ := hmem
          exact ⟨k, hS, hk ▸ hω⟩
        · right
          have hmem_neg : ‖S‖ ∈ spectrum ℝ (-S) := neg_mem_spectrum_neg hmem
          have hS_neg : (∑ i ∈ s, -X i ω).IsHermitian := by
            rw [Finset.sum_neg_distrib]
            exact hS.neg
          rw [← Finset.sum_neg_distrib, hS_neg.spectrum_real_eq_range_eigenvalues] at hmem_neg
          obtain ⟨k, hk⟩ := hmem_neg
          exact ⟨k, hS_neg, hk ▸ hω⟩
      · exact Or.inr hωH
    have hpos := h_indep.measureReal_exists_le_eigenvalues_sum_le_of_norm_le
      hX_meas hX_herm hX_mean hX_norm ht
    have hindep_neg : iIndepFun (fun i ω ↦ -X i ω) μ :=
      h_indep.comp (fun _ M ↦ -M) (fun _ ↦ measurable_neg)
    have hneg := hindep_neg.measureReal_exists_le_eigenvalues_sum_le_of_norm_le
      (L := L) (s := s)
      (fun i hi ↦ (hX_meas i hi).neg)
      (fun i hi ↦ (hX_herm i hi).mono fun _ h ↦ h.neg)
      (fun i hi p q ↦ by simp [Matrix.neg_apply, integral_neg, hX_mean i hi p q])
      (fun i hi ↦ (hX_norm i hi).mono fun _ h ↦ by simpa using h) ht
    simp only [neg_mul_neg] at hneg
    calc μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖}
        ≤ μ.real ((Epos ∪ Eneg) ∪ Hᶜ) := measureReal_mono hsub
      _ ≤ μ.real (Epos ∪ Eneg) + μ.real Hᶜ := measureReal_union_le _ _
      _ ≤ μ.real Epos + μ.real Eneg + 0 := by
          rw [hHc_null]
          gcongr
          exact measureReal_union_le _ _
      _ ≤ 2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) /
            (‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖ + L * t / 3)) := by
          linarith
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have hempty : {ω : Ω | t ≤ ‖∑ i ∈ s, X i ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Subsingleton.elim (∑ i ∈ s, X i ω) 0, norm_zero]
      exact ht
    rw [hempty, measureReal_empty]
    positivity

/-- **Sharp rectangular matrix Bernstein inequality** over a `Finset` (Tropp 2012, Theorem 1.6).
For independent a.e.-measurable random `m × n` matrices `Y i` (`i ∈ s`) with entrywise mean zero
and `‖Y i‖ ≤ L` a.e., let
`v = max ‖∑ i ∈ s, E[Y i * (Y i)ᴴ]‖ ‖∑ i ∈ s, E[(Y i)ᴴ * Y i]‖`.
For every `t > 0`,
`μ.real {ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ≤ (card m + card n) * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_norm_sum_ge_le_rectangular {Y : ι → Ω → Matrix m n 𝕜}
    (h_indep : iIndepFun Y μ) {s : Finset ι} {L t : ℝ}
    (hY_meas : ∀ i ∈ s, AEMeasurable (Y i) μ)
    (hY_mean : ∀ i ∈ s, ∀ p q, ∫ ω, Y i ω p q ∂μ = 0)
    (hY_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ L) (ht : 0 < t) :
    let v := max
      ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
      ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
  by_cases hmn : Nonempty (m ⊕ n)
  · let Z : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) 𝕜 := fun i ω ↦ (Y i ω).hermitianDilation
    have hZ_indep : iIndepFun Z μ :=
      h_indep.comp (fun _ A ↦ A.hermitianDilation)
        (fun _ ↦ Matrix.continuous_hermitianDilation.measurable)
    have hZ_meas (i : ι) (hi : i ∈ s) : AEMeasurable (Z i) μ :=
      Matrix.continuous_hermitianDilation.measurable.comp_aemeasurable (hY_meas i hi)
    have hZ_herm (i : ι) (_ : i ∈ s) : ∀ᵐ ω ∂μ, (Z i ω).IsHermitian :=
      Eventually.of_forall fun ω ↦ Matrix.isHermitian_hermitianDilation (Y i ω)
    have hZ_mean (i : ι) (hi : i ∈ s) (p q : m ⊕ n) : ∫ ω, Z i ω p q ∂μ = 0 := by
      cases p with
      | inl p₁ =>
        cases q with
        | inl _ => simp [Z, Matrix.hermitianDilation]
        | inr q₂ => simpa [Z, Matrix.hermitianDilation] using hY_mean i hi p₁ q₂
      | inr p₂ =>
        cases q with
        | inl q₁ =>
          have hstar : (fun ω ↦ Z i ω (Sum.inr p₂) (Sum.inl q₁)) =
              fun ω ↦ star (Y i ω q₁ p₂) := by
            ext ω
            simp [Z, Matrix.hermitianDilation, Matrix.conjTranspose_apply]
          have hY_int : Integrable (fun ω ↦ Y i ω q₁ p₂) μ := by
            let proj : Matrix m n 𝕜 →L[𝕜] 𝕜 :=
              { toLinearMap :=
                  { toFun := fun A ↦ A q₁ p₂
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := fun _ _ ↦ rfl }
                cont := (continuous_apply p₂).comp (continuous_apply q₁) }
            refine Integrable.of_bound
              (proj.continuous.measurable.comp_aemeasurable (hY_meas i hi)).aestronglyMeasurable
              (‖proj‖ * |L|) ?_
            filter_upwards [hY_norm i hi] with ω hω
            exact (proj.le_opNorm (Y i ω)).trans
              (mul_le_mul_of_nonneg_left (hω.trans (le_abs_self L)) (norm_nonneg proj))
          rw [hstar]
          have hcomm := (starL' ℝ (A := 𝕜) : 𝕜 →L[ℝ] 𝕜).integral_comp_comm hY_int
          -- Identify `star` with the continuous `ℝ`-linear equivalence `starL' ℝ`.
          change ∫ ω, (starL' ℝ (A := 𝕜) : 𝕜 →L[ℝ] 𝕜) (Y i ω q₁ p₂) ∂μ = 0
          rw [hcomm, hY_mean i hi q₁ p₂, map_zero]
        | inr _ => simp [Z, Matrix.hermitianDilation]
    have hZ_norm (i : ι) (hi : i ∈ s) : ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ L :=
      (hY_norm i hi).mono fun ω hω ↦ by simpa [Z] using hω
    -- Chiral symmetry makes `‖∑ Y_i‖` itself a positive eigenvalue of `∑ Z_i`.
    have hsub : {ω : Ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ⊆
        {ω : Ω | ∃ k : m ⊕ n, ∃ hS : (∑ i ∈ s, Z i ω).IsHermitian, t ≤ hS.eigenvalues k} := by
      intro ω hω
      set A := ∑ i ∈ s, Y i ω
      have hsumZ : ∑ i ∈ s, Z i ω = A.hermitianDilation :=
        (Matrix.hermitianDilation_sum s (fun i ↦ Y i ω)).symm
      have hS : (∑ i ∈ s, Z i ω).IsHermitian := by
        rw [hsumZ]
        exact Matrix.isHermitian_hermitianDilation A
      have hmem : ‖A.hermitianDilation‖ ∈ spectrum ℝ A.hermitianDilation := by
        rcases (Matrix.isHermitian_hermitianDilation A).norm_or_neg_norm_mem_spectrum with
            hpos | hneg
        · exact hpos
        · exact Matrix.mem_spectrum_hermitianDilation_of_neg_mem hneg
      rw [← hsumZ, hS.spectrum_real_eq_range_eigenvalues] at hmem
      obtain ⟨k, hk⟩ := hmem
      refine ⟨k, hS, ?_⟩
      rw [hk, hsumZ, Matrix.l2_opNorm_hermitianDilation]
      exact hω
    have hupper := hZ_indep.measureReal_exists_le_eigenvalues_sum_le_of_norm_le
      hZ_meas hZ_herm hZ_mean hZ_norm ht
    have hv_eq : ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Z i ω * Z i ω) p q ∂μ‖ =
        max ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
            ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖ := by
      have hblock_sum : (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Z i ω * Z i ω) p q ∂μ) =
          Matrix.fromBlocks
            (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ) 0 0
            (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ) := by
        ext (p | p) (q | q) <;>
          simp [Z, Matrix.hermitianDilation_mul_self, Matrix.sum_apply]
      rw [hblock_sum, Matrix.l2_opNorm_fromBlocks_zero]
    rw [hv_eq, Fintype.card_sum, Nat.cast_add] at hupper
    exact (measureReal_mono hsub).trans hupper
  · have : IsEmpty (m ⊕ n) := not_nonempty_iff.mp hmn
    have : IsEmpty m := ⟨fun x ↦ IsEmpty.false (Sum.inl x : m ⊕ n)⟩
    have hempty : {ω : Ω | t ≤ ‖∑ i ∈ s, Y i ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Subsingleton.elim (∑ i ∈ s, Y i ω) 0, norm_zero]
      exact ht
    rw [hempty, measureReal_empty]
    positivity

end Bernstein

end ProbabilityTheory.iIndepFun

namespace TauCeti

variable {ι Ω m n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4). For independent
a.e.-measurable, a.e.-Hermitian random `n × n` matrices `X i` with entrywise mean zero and
`‖X i‖ ≤ L` a.e., and `v = ‖Matrix.of fun p q ↦ ∑ i, ∫ ω, (X i ω * X i ω) p q ∂μ‖`, for every
`t > 0`:
`μ.real {ω | t ≤ ‖∑ i, X i ω‖} ≤ 2 * card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem matrix_bernstein {X : ι → Ω → Matrix n n 𝕜} (h_indep : iIndepFun X μ)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (hX_herm : ∀ i, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i p q, ∫ ω, X i ω p q ∂μ = 0) {L : ℝ} (hX_norm : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖∑ i, X i ω‖} ≤
      2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun p q ↦ ∑ i, ∫ ω, (X i ω * X i ω) p q ∂μ‖ + L * t / 3)) := by
  have h := h_indep.measureReal_norm_sum_ge_le (s := Finset.univ)
    (fun i _ ↦ hX_meas i) (fun i _ ↦ hX_herm i) (fun i _ ↦ hX_mean i) (fun i _ ↦ hX_norm i) ht
  have hmat : (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ) =
      Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, (X i ω * X i ω) p q ∂μ := by
    ext p q
    simp [Matrix.sum_apply]
  rwa [hmat] at h

/-- **Sharp rectangular matrix Bernstein inequality** (Tropp 2012, Theorem 1.6). For independent
a.e.-measurable random `m × n` matrices `Y i` with entrywise mean zero and `‖Y i‖ ≤ L` a.e., let
`v = max ‖∑ i, E[Y i * (Y i)ᴴ]‖ ‖∑ i, E[(Y i)ᴴ * Y i]‖`. For every `t > 0`:
`μ.real {ω | t ≤ ‖∑ i, Y i ω‖} ≤ (card m + card n) * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem matrix_bernstein_rectangular {Y : ι → Ω → Matrix m n 𝕜} (h_indep : iIndepFun Y μ)
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) (hY_mean : ∀ i p q, ∫ ω, Y i ω p q ∂μ = 0)
    {L : ℝ} (hY_norm : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ L) {t : ℝ} (ht : 0 < t) :
    let v := max
      ‖Matrix.of fun p q ↦ ∑ i, ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
      ‖Matrix.of fun p q ↦ ∑ i, ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i, Y i ω‖} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have h := h_indep.measureReal_norm_sum_ge_le_rectangular (s := Finset.univ)
    (fun i _ ↦ hY_meas i) (fun i _ ↦ hY_mean i) (fun i _ ↦ hY_norm i) ht
  have hmat₁ : (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ) =
      Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ := by
    ext p q
    simp [Matrix.sum_apply]
  have hmat₂ : (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ) =
      Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ := by
    ext p q
    simp [Matrix.sum_apply]
  rwa [hmat₁, hmat₂] at h

end TauCeti

end
