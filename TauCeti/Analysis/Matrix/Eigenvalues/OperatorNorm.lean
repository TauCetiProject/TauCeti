/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Euclidean operator norms and the largest Gram eigenvalue

For a rectangular matrix `A`, the square of its Euclidean operator norm is the largest
real eigenvalue of its source Gram matrix `Aᴴ * A`. We express this both with the decreasing
eigenvalue list and as an `IsGreatest` statement about the real spectrum. A unit eigenvector
for this eigenvalue attains the operator norm, including when `A = 0`.

The source must be nonempty for a largest eigenvalue or a unit attaining vector to exist.
For an empty source the operator norm is zero by subsingleton elimination, and
`spectrum.of_subsingleton` gives the empty Gram spectrum.

All matrix norms here use `Matrix.Norms.L2Operator`, hence agree with the norms of the
native maps on `EuclideanSpace`. The proof uses Mathlib's
`Matrix.IsHermitian.spectral_theorem`, its orthonormal eigenvector basis, and
`Matrix.l2_opNorm_conjTranspose_mul_self`.
-/

public section

open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- The Euclidean operator norm of a Hermitian matrix is the sup norm of its real
eigenvalue list. This includes the empty index type. -/
theorem IsHermitian.l2_opNorm_eq_norm_eigenvalues {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) : ‖B‖ = ‖hB.eigenvalues‖ := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  simp only [Pi.norm_def]
  congr 2
  funext i
  apply NNReal.eq
  simp

/-- On a nonempty carrier, the Euclidean operator norm of a positive-semidefinite matrix
is the first entry of its decreasing eigenvalue list. -/
theorem PosSemidef.l2_opNorm_eq_eigenvalues₀_zero [Nonempty n] {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) :
    ‖B‖ = hB.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have he (i : Fin (Fintype.card n)) : hB.isHermitian.eigenvalues (e i) =
      hB.isHermitian.eigenvalues₀ i := by
    simp [IsHermitian.eigenvalues, e]
  have hnonneg : 0 ≤ hB.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
    rw [← he]
    exact hB.eigenvalues_nonneg _
  rw [hB.isHermitian.l2_opNorm_eq_norm_eigenvalues]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun i ↦ ?_
    rw [Real.norm_of_nonneg (hB.eigenvalues_nonneg i)]
    exact hB.isHermitian.eigenvalues₀_antitone (Fin.zero_le (e.symm i))
  · simpa only [he, Real.norm_of_nonneg hnonneg] using
      norm_le_pi_norm hB.isHermitian.eigenvalues (e ⟨0, Fintype.card_pos⟩)

/-- The square of the Euclidean operator norm of a rectangular matrix is the largest
eigenvalue of its source Gram matrix, enumerated in decreasing order. -/
theorem l2_opNorm_sq_eq_eigenvalues₀_conjTranspose_mul_self [Nonempty n]
    (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues₀
      ⟨0, Fintype.card_pos⟩ := by
  rw [pow_two, ← l2_opNorm_conjTranspose_mul_self]
  exact (posSemidef_conjTranspose_mul_self A).l2_opNorm_eq_eigenvalues₀_zero

/-- The squared Euclidean operator norm is the greatest point of the real spectrum of
the source Gram matrix. Nonemptiness of the source excludes the empty spectrum. -/
theorem isGreatest_spectrum_conjTranspose_mul_self [Nonempty n] (A : Matrix m n 𝕜) :
    IsGreatest (spectrum ℝ (Aᴴ * A)) (‖A‖ ^ 2) := by
  let hG := isHermitian_conjTranspose_mul_self A
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [l2_opNorm_sq_eq_eigenvalues₀_conjTranspose_mul_self,
    hG.spectrum_real_eq_range_eigenvalues]
  refine ⟨⟨e ⟨0, Fintype.card_pos⟩, ?_⟩, ?_⟩
  · simp [IsHermitian.eigenvalues, e]
  · rintro _ ⟨i, rfl⟩
    exact hG.eigenvalues₀_antitone (Fin.zero_le (e.symm i))

/-- The largest real Gram eigenvalue is attained by a unit vector on which `A` attains
its Euclidean operator norm. The statement also applies to the zero matrix. -/
theorem exists_unit_eigenvector_conjTranspose_mul_self [Nonempty n]
    (A : Matrix m n 𝕜) :
    ∃ v : EuclideanSpace 𝕜 n, ‖v‖ = 1 ∧
      (Aᴴ * A).toEuclideanLin v = ((‖A‖ ^ 2 : ℝ) : 𝕜) • v ∧
      ‖A.toEuclideanLin v‖ = ‖A‖ := by
  classical
  let hG := isHermitian_conjTranspose_mul_self A
  obtain ⟨i, hi⟩ := hG.spectrum_real_eq_range_eigenvalues ▸
    (A.isGreatest_spectrum_conjTranspose_mul_self).1
  let v := hG.eigenvectorBasis i
  have hv : ‖v‖ = 1 := hG.eigenvectorBasis.norm_eq_one i
  have heig : (Aᴴ * A).toEuclideanLin v = ((‖A‖ ^ 2 : ℝ) : 𝕜) • v := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_smul, hi,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), v] using hG.mulVec_eigenvectorBasis i
  refine ⟨v, hv, heig, ?_⟩
  have hinner : ⟪A.toEuclideanLin v, A.toEuclideanLin v⟫_𝕜 =
      ⟪v, (Aᴴ * A).toEuclideanLin v⟫_𝕜 := by
    simpa only [toEuclideanLin, toLpLin_one, LinearMap.id_apply, Matrix.mul_one] using
      A.inner_toEuclideanLin_toEuclideanLin 1 v
  rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, hv] at hinner
  have hsq : ‖A.toEuclideanLin v‖ ^ 2 = ‖A‖ ^ 2 := by
    have hcast : ((‖A.toEuclideanLin v‖ ^ 2 : ℝ) : 𝕜) = ((‖A‖ ^ 2 : ℝ) : 𝕜) := by
      simpa using hinner
    exact_mod_cast hcast
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end Matrix
