/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Determinants of compressions and Horn's product inequality

For a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces and orthonormal
families `v : Fin k → F` and `w : Fin k → E`, the `k × k` matrix `(⟪vᵢ, A wⱼ⟫)` is the compression
of `A` to these families. Its determinant has norm at most the product `∏_{i < k} σᵢ(A)` of the
`k` largest singular values of `A`. The bound is sharp: cutting `A` down along the first `k` right
singular vectors attains it.

The compression `V† A W` is the composite of `A` with the analysis map of `v` and the synthesis map
of `w`, both contractions, so the bound is `LinearMap.normDet_comp_comp_le_prod_singularValues`.
These products of singular values are the volume factors that multiplicative eigenvalue and
singular value inequalities compare. The first of them is Horn's product inequality
`∏_{i < k} σᵢ(A B) ≤ ∏_{i < k} σᵢ(A) σᵢ(B)`: cutting `A B` down along the top `k` right singular
vectors of `A B` realizes the left side as `normDet`, and `normDet` of a composite factors through
the image of `B`.

## Main results

* `LinearMap.exists_linearIsometry_normDet_comp_eq_prod_singularValues`: for `k ≤ dim E`, some
  linear isometry `W` from `𝕜ᵏ` into `E` has `normDet (A W) = ∏_{i < k} σᵢ(A)`.
* `LinearMap.norm_det_compression_le`: `‖det (⟪vᵢ, A wⱼ⟫)‖ ≤ ∏_{i < k} σᵢ(A)` for orthonormal
  `v` and `w`.
* `LinearMap.exists_orthonormal_norm_det_compression_eq_prod_singularValues`: for `k` at most both
  dimensions, some orthonormal families attain this bound.
* `LinearMap.prod_singularValues_comp_le`: **Horn's product inequality**
  `∏_{i < k} σᵢ(A B) ≤ ∏_{i < k} σᵢ(A) σᵢ(B)`, for every `k` and maps between different spaces.

## References

* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  Lemma 3.3.1 and Theorem 3.3.4.
* A. W. Marshall, I. Olkin and B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer, 2011, 9.H.1.
-/

public section

noncomputable section

open Module Finset
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- Cutting `A` down along its first `k` right singular vectors attains the bound
`LinearMap.normDet_comp_comp_le_prod_singularValues`: some linear isometry `W` from `𝕜ᵏ` into `E`
has `normDet (A W) = ∏_{i < k} σᵢ(A)`. -/
theorem exists_linearIsometry_normDet_comp_eq_prod_singularValues (A : E →ₗ[𝕜] F) {k : ℕ}
    (hk : k ≤ finrank 𝕜 E) :
    ∃ W : EuclideanSpace 𝕜 (Fin k) →ₗᵢ[𝕜] E,
      (A ∘ₗ W.toLinearMap).normDet = ∏ i ∈ Finset.range k, A.singularValues i := by
  let w : Fin k → E := fun j ↦ A.rightSingularBasis (Fin.castLE hk j)
  have hw : Orthonormal 𝕜 w :=
    A.rightSingularBasis.orthonormal.comp _ (Fin.castLE_injective hk)
  refine ⟨hw.synthesisMapIsometry, ?_⟩
  -- The images `A wⱼ` are orthogonal with `‖A wⱼ‖² = σⱼ²`, so their Gram matrix is diagonal.
  have hgram : Matrix.gram 𝕜 (fun j ↦ (A ∘ₗ hw.synthesisMapIsometry.toLinearMap)
      (EuclideanSpace.basisFun (Fin k) 𝕜 j)) =
      Matrix.diagonal fun j : Fin k ↦ ((A.singularValues j ^ 2 : ℝ) : 𝕜) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.diagonal_apply]
    simp only [comp_apply, LinearIsometry.coe_toLinearMap, EuclideanSpace.basisFun_apply,
      Orthonormal.synthesisMapIsometry_single, one_smul, w]
    rw [A.inner_apply_rightSingularBasis, orthonormal_iff_ite.1 A.rightSingularBasis.orthonormal]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Fin.castLE_injective hk |>.ne hij]
  have hsq := (A ∘ₗ hw.synthesisMapIsometry.toLinearMap).normDet_sq_eq_det_gram
    (EuclideanSpace.basisFun (Fin k) 𝕜)
  rw [hgram, Matrix.det_diagonal, ← RCLike.ofReal_prod, RCLike.ofReal_inj, Finset.prod_pow,
    Fin.prod_univ_eq_prod_range (fun j ↦ A.singularValues j)] at hsq
  exact (pow_left_inj₀ (normDet_nonneg _) (prod_nonneg fun j _ ↦ A.singularValues_nonneg j)
    two_ne_zero).1 hsq

/-- **Determinants of compressions.** For orthonormal families `v` in `F` and `w` in `E` with `k`
members, the determinant of the compressed matrix `(⟪vᵢ, A wⱼ⟫)` has norm at most the product of
the `k` largest singular values of `A` (Horn–Johnson, *Topics in Matrix Analysis*,
Lemma 3.3.1(b)). -/
theorem norm_det_compression_le {k : ℕ} (A : E →ₗ[𝕜] F) {v : Fin k → F} {w : Fin k → E}
    (hv : Orthonormal 𝕜 v) (hw : Orthonormal 𝕜 w) :
    ‖(Matrix.of fun i j ↦ ⟪v i, A (w j)⟫_𝕜).det‖ ≤ ∏ i ∈ Finset.range k, A.singularValues i := by
  let C := TauCeti.analysisMap 𝕜 v ∘ₗ A ∘ₗ hw.synthesisMapIsometry.toLinearMap
  -- The compressed matrix is the matrix of `C` in the standard basis of `𝕜ᵏ`.
  have hM : (Matrix.of fun i j ↦ ⟪v i, A (w j)⟫_𝕜) =
      toMatrix (EuclideanSpace.basisFun (Fin k) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin k) 𝕜).toBasis C := by
    ext i j
    simp [C, toMatrix_apply, TauCeti.analysisMap_apply]
  rw [hM, det_toMatrix, ← normDet_eq_norm_det]
  simpa [C] using
    normDet_comp_comp_le_prod_singularValues _ A _ hv.norm_analysisMap_le fun x ↦
      (hw.synthesisMapIsometry.norm_map x).le

/-- The bound `LinearMap.norm_det_compression_le` is attained: when `k` is at most the dimensions
of `E` and `F`, some orthonormal families `v` and `w` with `k` members have
`‖det (⟪vᵢ, A wⱼ⟫)‖ = ∏_{i < k} σᵢ(A)`. -/
theorem exists_orthonormal_norm_det_compression_eq_prod_singularValues (A : E →ₗ[𝕜] F)
    {k : ℕ} (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
    ∃ v : Fin k → F, ∃ w : Fin k → E, Orthonormal 𝕜 v ∧ Orthonormal 𝕜 w ∧
      ‖(Matrix.of fun i j ↦ ⟪v i, A (w j)⟫_𝕜).det‖ = ∏ i ∈ Finset.range k, A.singularValues i := by
  -- Pair the first `k` right singular vectors with an orthonormal basis of `F` extending the
  -- nonzero left singular vectors; the compressed matrix is then `diag (σ₀, …, σ_{k-1})`.
  obtain ⟨b, hb⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  refine ⟨fun i ↦ b (Fin.castLE hkF i), fun j ↦ A.rightSingularBasis (Fin.castLE hkE j),
    b.orthonormal.comp _ (Fin.castLE_injective hkF),
    A.rightSingularBasis.orthonormal.comp _ (Fin.castLE_injective hkE), ?_⟩
  have hM : (Matrix.of fun i j ↦
      ⟪b (Fin.castLE hkF i), A (A.rightSingularBasis (Fin.castLE hkE j))⟫_𝕜) =
      Matrix.diagonal fun j : Fin k ↦ ((A.singularValues j : ℝ) : 𝕜) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_apply, apply_rightSingularBasis, inner_smul_right]
    by_cases hσ : A.singularValues j = 0
    · rw [Fin.val_castLE, hσ, RCLike.ofReal_zero, zero_mul]
      split_ifs with hij <;> simp [hij, hσ]
    · rw [← hb (Fin.castLE hkE j) (Fin.castLE hkF j) rfl hσ,
        orthonormal_iff_ite.1 b.orthonormal]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, (Fin.castLE_injective hkF).ne hij]
  rw [hM, Matrix.det_diagonal, ← RCLike.ofReal_prod, RCLike.norm_ofReal,
    Fin.prod_univ_eq_prod_range (fun j ↦ A.singularValues j)]
  exact abs_of_nonneg (prod_nonneg fun j _ ↦ A.singularValues_nonneg j)

/-- **Horn's product inequality.** For `A : F →ₗ[𝕜] G` and `B : E →ₗ[𝕜] F`, the product of the
`k` largest singular values of `A B` is at most `∏_{i < k} σᵢ(A) σᵢ(B)`, for every `k`
(Horn–Johnson, *Topics in Matrix Analysis*, Theorem 3.3.4; Marshall–Olkin–Arnold, 9.H.1). -/
theorem prod_singularValues_comp_le (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) (k : ℕ) :
    ∏ i ∈ Finset.range k, (A ∘ₗ B).singularValues i ≤
      ∏ i ∈ Finset.range k, A.singularValues i * B.singularValues i := by
  have hA := prod_nonneg fun i (_ : i ∈ Finset.range k) ↦ A.singularValues_nonneg i
  have hB := prod_nonneg fun i (_ : i ∈ Finset.range k) ↦ B.singularValues_nonneg i
  rw [prod_mul_distrib]
  rcases lt_or_ge (finrank 𝕜 E) k with hk | hk
  · -- Beyond the dimension of `E` the left side has the factor `σ_{dim E}(A B) = 0`.
    rw [prod_eq_zero (Finset.mem_range.2 hk) ((A ∘ₗ B).singularValues_of_finrank_le le_rfl)]
    exact mul_nonneg hA hB
  -- Cut `A B` down along an isometry `W` attaining the left side, and factor `normDet (A B W)`
  -- through the image of `B W`.
  obtain ⟨W, hW⟩ := (A ∘ₗ B).exists_linearIsometry_normDet_comp_eq_prod_singularValues hk
  rw [← hW, comp_assoc, normDet_comp]
  have hBW : (B ∘ₗ W.toLinearMap).normDet ≤ ∏ i ∈ Finset.range k, B.singularValues i := by
    simpa using normDet_comp_comp_le_prod_singularValues LinearMap.id B W.toLinearMap
      (fun _ ↦ le_rfl) fun x ↦ (W.norm_map x).le
  by_cases hker : (B ∘ₗ W.toLinearMap).ker = ⊥
  · -- `B W` is injective, so its image `R` has dimension `k`.
    set R := (B ∘ₗ W.toLinearMap).range
    have hR : finrank 𝕜 R = k := by
      rw [finrank_range_of_inj (ker_eq_bot.1 hker), finrank_euclideanSpace_fin]
    have hAR : (A.domRestrict R).normDet ≤ ∏ i ∈ Finset.range k, A.singularValues i := by
      have hres : A.domRestrict R = A ∘ₗ R.subtype := by ext; simp
      simpa [hR, hres] using normDet_comp_comp_le_prod_singularValues LinearMap.id A R.subtype
        (fun _ ↦ le_rfl) fun _ ↦ le_rfl
    exact mul_le_mul hAR hBW (normDet_nonneg _) hA
  · rw [normDet_eq_zero_iff_ker_ne_bot.2 hker, mul_zero]
    exact mul_nonneg hA hB

end LinearMap
