/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Normed.Group.Pi

/-!
# Euclidean operator norms and extreme real eigenvalues

For a rectangular matrix `A` with nonempty source type (`[Nonempty n]`), the square of its
Euclidean operator norm is the largest real eigenvalue of its source Gram matrix `Aᴴ * A`. We
express this both with the decreasing eigenvalue list and as an `IsGreatest` statement about the
real spectrum. A unit eigenvector for this eigenvalue attains the operator norm, including when
`A = 0`. When the source type is empty, the operator norm is `0` while the Gram spectrum is empty.

For a Hermitian matrix on a nonempty carrier, `sSup (spectrum ℝ A)` and `sInf (spectrum ℝ A)`
agree with the first and last entries of `eigenvalues₀` (proved in
`TauCeti.Analysis.Matrix.Spectrum`), and the Euclidean operator norm equals
`max (sSup (spectrum ℝ A)) (sSup (spectrum ℝ (-A)))`. For the Hermitian dilation
`fromBlocks 0 A Aᴴ 0` (`A.hermitianDilation`) of a rectangular matrix `A`, symmetry of the
spectrum under negation shows that `sSup (spectrum ℝ (fromBlocks 0 A Aᴴ 0)) = ‖A‖`.

For a Hermitian matrix, each ordered eigenvalue is bounded in absolute value by the operator
norm, and the `2 * k`-th power of the operator norm is bounded by the real trace of the
`2 * k`-th matrix power, provided the matrix is nonempty when `k = 0`. This is the trace bound
behind moment estimates for the operator norm of random matrices.

All matrix norms here use `Matrix.Norms.L2Operator`, hence agree with the norms of the
native maps on `EuclideanSpace`. The proof uses Mathlib's
`Matrix.IsHermitian.spectral_theorem`, its orthonormal eigenvector basis, and
`Matrix.l2_opNorm_conjTranspose_mul_self`.
-/

public section

open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Pointwise

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
  have hnonneg : 0 ≤ hB.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
    rw [← hB.isHermitian.eigenvalues_apply_equivOfCardEq]
    exact hB.eigenvalues_nonneg _
  rw [hB.isHermitian.l2_opNorm_eq_norm_eigenvalues]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun i ↦ ?_
    rw [Real.norm_of_nonneg (hB.eigenvalues_nonneg i), ← e.apply_symm_apply i,
      hB.isHermitian.eigenvalues_apply_equivOfCardEq]
    exact hB.isHermitian.eigenvalues₀_antitone (Fin.zero_le (e.symm i))
  · simpa only [e, hB.isHermitian.eigenvalues_apply_equivOfCardEq,
      Real.norm_of_nonneg hnonneg] using
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
  refine ⟨⟨e ⟨0, Fintype.card_pos⟩, hG.eigenvalues_apply_equivOfCardEq _⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [← e.apply_symm_apply i, hG.eigenvalues_apply_equivOfCardEq]
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

/-- On a nonempty index type, the `ℓ²` operator norm of a Hermitian matrix is
`max (λ_max A) (λ_max (-A))`. -/
theorem IsHermitian.l2_opNorm_eq_max_sSup_spectrum_real [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ‖A‖ = max (sSup (spectrum ℝ A)) (sSup (spectrum ℝ (-A))) := by
  have hmem (i : n) := hA.eigenvalues_mem_spectrum_real i
  have hle (i : n) : hA.eigenvalues i ≤ sSup (spectrum ℝ A) :=
    le_csSup A.finite_real_spectrum.bddAbove (hmem i)
  have hge (i : n) : sInf (spectrum ℝ A) ≤ hA.eigenvalues i :=
    csInf_le A.finite_real_spectrum.bddBelow (hmem i)
  rw [hA.l2_opNorm_eq_norm_eigenvalues, TauCeti.sSup_spectrum_real_neg A]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun i ↦ by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hge i, le_max_right (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A))],
        (hle i).trans (le_max_left _ _)⟩
    have hi := Classical.arbitrary n
    linarith [hle hi, hge hi, le_max_left (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A)),
      le_max_right (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A))]
  · refine max_le (hA.sSup_spectrum_real_eq_ciSup_eigenvalues ▸ ciSup_le fun i ↦
        (le_abs_self _).trans (by simpa using norm_le_pi_norm hA.eigenvalues i))
      (hA.sInf_spectrum_real_eq_ciInf_eigenvalues ▸ neg_le.2 (le_ciInf fun i ↦ by
        have h := norm_le_pi_norm hA.eigenvalues i
        rw [Real.norm_eq_abs] at h; linarith [neg_abs_le (hA.eigenvalues i)]))

/-- On a nonempty sum index type `m ⊕ p`, the largest eigenvalue of the Hermitian dilation
`fromBlocks 0 A Aᴴ 0` equals the `ℓ²` operator norm of `A`. -/
@[simp]
theorem sSup_spectrum_real_fromBlocks_zero_diagonal {p : Type*}
    [Fintype p] [DecidableEq m] [DecidableEq p] [Nonempty (m ⊕ p)] (A : Matrix m p 𝕜) :
    sSup (spectrum ℝ (fromBlocks (0 : Matrix m m 𝕜) A Aᴴ 0)) = ‖A‖ := by
  let D : Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fromBlocks 0 A Aᴴ 0
  let J : (Matrix (m ⊕ p) (m ⊕ p) 𝕜)ˣ :=
    ⟨fromBlocks 1 0 0 (-1), fromBlocks 1 0 0 (-1),
      by simp [fromBlocks_multiply, fromBlocks_one], by simp [fromBlocks_multiply, fromBlocks_one]⟩
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have hspec : spectrum ℝ (-D) = spectrum ℝ D := by
    have hJDJ : (J : Matrix (m ⊕ p) (m ⊕ p) 𝕜) * D * (↑J⁻¹ : Matrix (m ⊕ p) (m ⊕ p) 𝕜) = -D := by
      simp [J, D, fromBlocks_multiply, fromBlocks_neg]
    rw [← hJDJ, spectrum.units_conjugate]
  rw [← l2_opNorm_fromBlocks_zero_diagonal, hD.l2_opNorm_eq_max_sSup_spectrum_real, hspec,
    max_self]

/-- On a nonempty sum index type `m ⊕ p`, the largest eigenvalue of `A.hermitianDilation` equals
the `ℓ²` operator norm of `A`. -/
@[simp]
theorem sSup_spectrum_real_hermitianDilation {p : Type*}
    [Fintype p] [DecidableEq m] [DecidableEq p] [Nonempty (m ⊕ p)] (A : Matrix m p 𝕜) :
    sSup (spectrum ℝ A.hermitianDilation) = ‖A‖ :=
  A.sSup_spectrum_real_fromBlocks_zero_diagonal

/-- The absolute value of each ordered Hermitian eigenvalue is bounded by the Euclidean
operator norm. -/
theorem IsHermitian.norm_eigenvalues₀_le_l2_opNorm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (j : Fin (Fintype.card n)) : ‖hA.eigenvalues₀ j‖ ≤ ‖A‖ := by
  rw [hA.l2_opNorm_eq_norm_eigenvalues]
  simpa only [hA.eigenvalues_apply_equivOfCardEq] using
    norm_le_pi_norm hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) j)

/-- For a Hermitian matrix, the `2*k`-th power of the Euclidean operator norm is bounded by the
real trace of its `2*k`-th power. The dimension must be nonempty only for `k = 0`, where the
power of the norm is `1` and the trace is the dimension. -/
theorem IsHermitian.l2_opNorm_pow_two_mul_le_re_trace_pow_two_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) (hn : k = 0 → Nonempty n) :
    ‖A‖ ^ (2 * k) ≤ RCLike.re (A ^ (2 * k)).trace := by
  rw [hA.l2_opNorm_eq_norm_eigenvalues, hA.trace_pow_eq_sum_eigenvalues_pow]
  simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rcases eq_or_ne k 0 with rfl | hk
  · have := hn rfl
    simpa using (Nat.one_le_cast.mpr Fintype.card_pos : (1 : ℝ) ≤ Fintype.card n)
  · simpa only [Real.norm_eq_abs, pow_abs_two_mul] using
      Pi.norm_pow_le_sum_norm_pow hA.eigenvalues (mul_ne_zero two_ne_zero hk)

end Matrix
