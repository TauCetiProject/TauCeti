/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Euclidean operator norms and extreme real eigenvalues

For a rectangular matrix `A`, the square of its Euclidean operator norm is the largest
real eigenvalue of its source Gram matrix `Aᴴ * A`. We express this both with the decreasing
eigenvalue list and as an `IsGreatest` statement about the real spectrum. A unit eigenvector
for this eigenvalue attains the operator norm, including when `A = 0`.

For a Hermitian matrix on a nonempty carrier, `sSup (spectrum ℝ A)` and `sInf (spectrum ℝ A)`
agree with the first and last entries of `eigenvalues₀`, and the Euclidean operator norm equals
`max (sSup (spectrum ℝ A)) (sSup (spectrum ℝ (-A)))`. For the Hermitian dilation
`fromBlocks 0 A Aᴴ 0` of a rectangular matrix `A`, symmetry of the spectrum under negation shows
that `sSup (spectrum ℝ (fromBlocks 0 A Aᴴ 0)) = ‖A‖`.

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

/-- On a nonempty index type, the supremum of the real spectrum of a Hermitian matrix is its
largest sorted eigenvalue `eigenvalues₀ 0`. -/
theorem IsHermitian.sSup_spectrum_real_eq_eigenvalues₀_zero [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    sSup (spectrum ℝ A) = hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  rw [hA.spectrum_real_eq_range_eigenvalues]
  refine IsGreatest.csSup_eq ⟨⟨e ⟨0, Fintype.card_pos⟩, ?_⟩, ?_⟩
  · simp [IsHermitian.eigenvalues, e]
  · rintro _ ⟨i, rfl⟩
    exact hA.eigenvalues₀_antitone (Fin.zero_le (e.symm i))

/-- The supremum of the real spectrum of a Hermitian matrix equals the indexed supremum
`⨆ i, hA.eigenvalues i`. -/
theorem IsHermitian.sSup_spectrum_real_eq_ciSup_eigenvalues {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    sSup (spectrum ℝ A) = ⨆ i, hA.eigenvalues i := by
  rw [hA.spectrum_real_eq_range_eigenvalues, sSup_range]

/-- On a nonempty index type, the infimum of the real spectrum of a Hermitian matrix is its
smallest sorted eigenvalue `eigenvalues₀ (card n - 1)`. -/
theorem IsHermitian.sInf_spectrum_real_eq_eigenvalues₀_last [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    sInf (spectrum ℝ A) =
      hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos one_pos⟩ := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  let last : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos one_pos⟩
  rw [hA.spectrum_real_eq_range_eigenvalues]
  refine IsLeast.csInf_eq ⟨⟨e last, ?_⟩, ?_⟩
  · simp [IsHermitian.eigenvalues, e, last]
  · rintro _ ⟨i, rfl⟩
    exact hA.eigenvalues₀_antitone (Nat.le_sub_one_of_lt (e.symm i).isLt)

/-- The infimum of the real spectrum of a Hermitian matrix equals the indexed infimum
`⨅ i, hA.eigenvalues i`. -/
theorem IsHermitian.sInf_spectrum_real_eq_ciInf_eigenvalues {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    sInf (spectrum ℝ A) = ⨅ i, hA.eigenvalues i := by
  rw [hA.spectrum_real_eq_range_eigenvalues, sInf_range]

/-- Negating a matrix negates its extreme real spectral values:
`sSup (spectrum ℝ (-A)) = -sInf (spectrum ℝ A)`. -/
theorem sSup_spectrum_real_neg (A : Matrix n n 𝕜) :
    sSup (spectrum ℝ (-A)) = -sInf (spectrum ℝ A) := by
  have hspec : spectrum ℝ (-A) = -spectrum ℝ A := by
    ext x
    rw [spectrum.mem_iff, Set.mem_neg, spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, sub_neg_eq_add]
    have hneg : (-x : ℝ) • (1 : Matrix n n 𝕜) - A = -(x • (1 : Matrix n n 𝕜) + A) := by
      rw [neg_smul, neg_add, sub_eq_add_neg]
    rw [hneg, IsUnit.neg_iff]
  rw [hspec, Real.sSup_neg]

/-- Scaling a matrix by a nonnegative real scalar scales the supremum of its real spectrum. -/
theorem sSup_spectrum_real_smul_of_nonneg (A : Matrix n n 𝕜) {θ : ℝ} (hθ : 0 ≤ θ) :
    sSup (spectrum ℝ (θ • A)) = θ * sSup (spectrum ℝ A) := by
  rcases hθ.eq_or_lt with rfl | hθ
  · simp only [zero_smul, zero_mul]
    by_cases hn : Nonempty n
    · let : Nonempty n := hn
      have hspec : spectrum ℝ (0 : Matrix n n 𝕜) = {0} := by
        ext x
        simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, sub_zero,
          Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hne
          apply hx
          refine ⟨⟨x • (1 : Matrix n n 𝕜), x⁻¹ • (1 : Matrix n n 𝕜), ?_, ?_⟩, rfl⟩ <;>
            simp [smul_smul, hne]
        · rintro rfl
          simp only [zero_smul]
          exact not_isUnit_zero
      rw [hspec, csSup_singleton]
    · have : Subsingleton (Matrix n n 𝕜) := by
        have := not_nonempty_iff.1 hn
        infer_instance
      rw [spectrum.of_subsingleton, Real.sSup_empty]
  · have hspec : spectrum ℝ (θ • A) = (fun x : ℝ ↦ θ * x) '' spectrum ℝ A := by
      ext y
      simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Set.mem_image]
      constructor
      · intro hy
        refine ⟨θ⁻¹ * y, ?_, mul_inv_cancel_left₀ hθ.ne' y⟩
        intro hu
        apply hy
        have hmul : y • (1 : Matrix n n 𝕜) - θ • A =
            (θ • (1 : Matrix n n 𝕜)) * ((θ⁻¹ * y) • (1 : Matrix n n 𝕜) - A) := by
          rw [smul_mul_assoc, one_mul, smul_sub, smul_smul, mul_inv_cancel_left₀ hθ.ne']
        have hθu : IsUnit (θ • (1 : Matrix n n 𝕜)) :=
          ⟨⟨θ • (1 : Matrix n n 𝕜), θ⁻¹ • (1 : Matrix n n 𝕜),
            by simp [smul_smul, hθ.ne'], by simp [smul_smul, hθ.ne']⟩, rfl⟩
        rw [hmul]
        exact hθu.mul hu
      · rintro ⟨x, hx, rfl⟩ hu
        apply hx
        have hmul : x • (1 : Matrix n n 𝕜) - A =
            (θ⁻¹ • (1 : Matrix n n 𝕜)) * ((θ * x) • (1 : Matrix n n 𝕜) - θ • A) := by
          rw [smul_mul_assoc, one_mul, smul_sub, smul_smul, smul_smul, inv_mul_cancel_left₀ hθ.ne',
            inv_mul_cancel₀ hθ.ne', one_smul]
        have hθu : IsUnit (θ⁻¹ • (1 : Matrix n n 𝕜)) :=
          ⟨⟨θ⁻¹ • (1 : Matrix n n 𝕜), θ • (1 : Matrix n n 𝕜),
            by simp [smul_smul, hθ.ne'], by simp [smul_smul, hθ.ne']⟩, rfl⟩
        rw [hmul]
        exact hθu.mul hu
    rw [hspec]
    by_cases hne : (spectrum ℝ A).Nonempty
    · have hbdd : BddAbove (spectrum ℝ A) := A.finite_real_spectrum.bddAbove
      apply le_antisymm
      · refine csSup_le (hne.image _) ?_
        rintro _ ⟨x, hx, rfl⟩
        exact mul_le_mul_of_nonneg_left (le_csSup hbdd hx) hθ.le
      · rw [← le_div_iff₀' hθ]
        refine csSup_le hne fun x hx ↦ ?_
        rw [le_div_iff₀' hθ]
        exact le_csSup (A.finite_real_spectrum.image _).bddAbove ⟨x, hx, rfl⟩
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.image_empty, Real.sSup_empty, mul_zero]

/-- On a nonempty index type, the `ℓ²` operator norm of a Hermitian matrix is
`max (λ_max A) (λ_max (-A))`. -/
theorem IsHermitian.l2_opNorm_eq_max_sSup_spectrum_real [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ‖A‖ = max (sSup (spectrum ℝ A)) (sSup (spectrum ℝ (-A))) := by
  have hbdd : BddAbove (spectrum ℝ A) := A.finite_real_spectrum.bddAbove
  have hbdd' : BddBelow (spectrum ℝ A) := A.finite_real_spectrum.bddBelow
  have hmem (i : n) : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
  rw [hA.l2_opNorm_eq_norm_eigenvalues, A.sSup_spectrum_real_neg]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun i ↦ ?_
    · have hi := Classical.arbitrary n
      have h1 : hA.eigenvalues hi ≤ sSup (spectrum ℝ A) := le_csSup hbdd (hmem hi)
      have h2 : sInf (spectrum ℝ A) ≤ hA.eigenvalues hi := csInf_le hbdd' (hmem hi)
      linarith [le_max_left (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A)),
        le_max_right (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A))]
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [csInf_le hbdd' (hmem i),
          le_max_right (sSup (spectrum ℝ A)) (-sInf (spectrum ℝ A))],
        (le_csSup hbdd (hmem i)).trans (le_max_left _ _)⟩
  · refine max_le ?_ ?_
    · rw [hA.sSup_spectrum_real_eq_ciSup_eigenvalues]
      refine ciSup_le fun i ↦ (le_abs_self _).trans ?_
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm hA.eigenvalues i
    · rw [hA.sInf_spectrum_real_eq_ciInf_eigenvalues, neg_le]
      refine le_ciInf fun i ↦ ?_
      have h := norm_le_pi_norm hA.eigenvalues i
      rw [Real.norm_eq_abs] at h
      linarith [neg_abs_le (hA.eigenvalues i)]

/-- On a nonempty sum index type `m ⊕ p`, the largest eigenvalue of the Hermitian dilation
`fromBlocks 0 A Aᴴ 0` equals the `ℓ²` operator norm of `A`. -/
theorem sSup_spectrum_real_fromBlocks_zero_conjTranspose {p : Type*}
    [Fintype p] [DecidableEq m] [DecidableEq p] [Nonempty (m ⊕ p)] (A : Matrix m p 𝕜) :
    sSup (spectrum ℝ (fromBlocks (0 : Matrix m m 𝕜) A Aᴴ 0)) = ‖A‖ := by
  let D : Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fromBlocks 0 A Aᴴ 0
  let J : Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fromBlocks 1 0 0 (-1)
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have hJJ : J * J = 1 := by
    simp [J, fromBlocks_multiply, fromBlocks_one]
  have hJu : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  have hJDJ : J * D * J = -D := by
    simp [J, D, fromBlocks_multiply, fromBlocks_neg]
  have hspec : spectrum ℝ (-D) = spectrum ℝ D := by
    ext r
    simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    have hmul : r • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) - (-D) =
        J * (r • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) - D) * J := by
      rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hJJ, hJDJ, sub_neg_eq_add]
    rw [hmul]
    refine not_congr ⟨fun h ↦ ?_, fun h ↦ (hJu.mul h).mul hJu⟩
    have hback : r • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) - D =
        J * (J * (r • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) - D) * J) * J := by
      rw [← mul_assoc, ← mul_assoc, hJJ, one_mul, mul_assoc, hJJ, mul_one]
    rw [hback]
    exact (hJu.mul h).mul hJu
  have hnorm : ‖D‖ = sSup (spectrum ℝ D) := by
    rw [hD.l2_opNorm_eq_max_sSup_spectrum_real, hspec, max_self]
  rw [← hnorm, l2_opNorm_fromBlocks_zero_conjTranspose]

end Matrix
