/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import TauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Hoffman–Wielandt inequality for singular values

For two linear maps with the same finite-dimensional domain and codomain, the squared Euclidean
distance between their decreasingly ordered singular values is at most the squared Frobenius
distance between the maps.

The proof uses the rectangular von Neumann trace inequality, obtained from a Ky Fan bound and
summation by parts.

## References

* J. von Neumann, *Some matrix-inequalities and metrization of matric-space*, Tomsk Univ. Rev.
  **1** (1937), 286–300.
* A. J. Hoffman and H. W. Wielandt, *The variation of the spectrum of a normal matrix*,
  Duke Math. J. **20** (1953), 37–39.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. **11**
  (1960), 50–59.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Chapter IV.
-/

public section

open Module
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **The singular-value Hoffman–Wielandt inequality** when the domain dimension does not exceed
the codomain dimension. The squared distance between the ordered singular values is at most the
squared Frobenius seminorm of the difference. -/
private theorem sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le
    (A B : E →ₗ[𝕜] F) (hEF : finrank 𝕜 E ≤ finrank 𝕜 F) :
    ∑ i : Fin (finrank 𝕜 E), (A.singularValues i - B.singularValues i) ^ 2 ≤
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) ^ 2 := by
  obtain ⟨w, hw⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  let u : Fin (finrank 𝕜 E) → F := fun i ↦ w (Fin.castLE hEF i)
  let v := A.rightSingularBasis
  have hu : Orthonormal 𝕜 u := w.orthonormal.comp _ (Fin.castLE_injective hEF)
  have hAv (i : Fin (finrank 𝕜 E)) :
      A (v i) = ((A.singularValues i : ℝ) : 𝕜) • u i := by
    rw [A.apply_rightSingularBasis]
    by_cases hσ : A.singularValues i = 0
    · simp [hσ]
    · have hwi := hw i (Fin.castLE hEF i) (by simp) hσ
      simpa [u] using congrArg (fun z : F ↦
        ((A.singularValues i : ℝ) : 𝕜) • z) hwi.symm
  have hv : Orthonormal 𝕜 v := v.orthonormal
  have hcross := B.sum_antitone_mul_re_inner_le_sum_mul_singularValues
    u v hu hv (fun i _ ↦ A.singularValues_antitone (Nat.le_succ i))
    (A.singularValues_nonneg _)
  have hBbasis :
      ∑ i : Fin (finrank 𝕜 E), ‖B (v i)‖ ^ 2 =
        ∑ i : Fin (finrank 𝕜 E), B.singularValues i ^ 2 := by
    rw [← TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply v B,
      B.sq_frobenius_apply_eq_sum_sq_singularValues]
  have hexp (i : Fin (finrank 𝕜 E)) :
      ‖(A - B) (v i)‖ ^ 2 =
        A.singularValues i ^ 2 -
          2 * (A.singularValues i *
            RCLike.re ⟪u i, B (v i)⟫_𝕜) + ‖B (v i)‖ ^ 2 := by
    rw [LinearMap.sub_apply, hAv i, norm_sub_sq (𝕜 := 𝕜)]
    simp [norm_smul, u, inner_smul_left, RCLike.conj_ofReal]
  have hexpSum :
      ∑ i : Fin (finrank 𝕜 E), ‖(A - B) (v i)‖ ^ 2 =
        (∑ i : Fin (finrank 𝕜 E), A.singularValues i ^ 2) -
          2 * (∑ i : Fin (finrank 𝕜 E),
            A.singularValues i * RCLike.re ⟪u i, B (v i)⟫_𝕜) +
            ∑ i : Fin (finrank 𝕜 E), ‖B (v i)‖ ^ 2 := by
    simp_rw [hexp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsingexp :
      ∑ i : Fin (finrank 𝕜 E), (A.singularValues i - B.singularValues i) ^ 2 =
        (∑ i : Fin (finrank 𝕜 E), A.singularValues i ^ 2) -
          2 * (∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i) +
            ∑ i : Fin (finrank 𝕜 E), B.singularValues i ^ 2 := by
    simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum]
  rw [hsingexp, TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply v (A - B),
    hexpSum, hBbasis]
  nlinarith [hcross]

/-- **The singular-value Hoffman–Wielandt inequality** for arbitrary finite-dimensional maps.
The sum may run over any initial segment of the singular values: beyond the smaller dimension,
both maps' singular values are zero. -/
theorem sum_sq_singularValues_sub_le_sq_frobenius_apply_sub
    (A B : E →ₗ[𝕜] F) {k : ℕ} :
    ∑ i : Fin k, (A.singularValues i - B.singularValues i) ^ 2 ≤
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) ^ 2 := by
  let d := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hmin : ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
      (A.singularValues i - B.singularValues i) ^ 2 ≤
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) ^ 2 := by
    rcases le_total (finrank 𝕜 E) (finrank 𝕜 F) with hEF | hFE
    · rw [min_eq_left hEF]
      exact A.sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le B hEF
    · rw [min_eq_right hFE]
      have h := (adjoint A).sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le
        (adjoint B) hFE
      rw [singularValues_adjoint, singularValues_adjoint, ← map_sub,
        ← TauCeti.UnitarilyInvariantSeminorm.schatten_two (𝕜 := 𝕜) (E := F) (F := E),
        TauCeti.UnitarilyInvariantSeminorm.schatten_apply_adjoint,
        TauCeti.UnitarilyInvariantSeminorm.schatten_two] at h
      exact h
  have hzero (T : E →ₗ[𝕜] F) (i : ℕ) (hi : d ≤ i) : T.singularValues i = 0 := by
    rcases le_total (finrank 𝕜 E) (finrank 𝕜 F) with hEF | hFE
    · exact T.singularValues_of_finrank_le (by simpa [d, min_eq_left hEF] using hi)
    · exact T.singularValues_of_finrank_le_right (by simpa [d, min_eq_right hFE] using hi)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (A.singularValues i - B.singularValues i) ^ 2)]
    at hmin ⊢
  calc
    _ ≤ ∑ i ∈ Finset.range (max k d), (A.singularValues i - B.singularValues i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ i ∈ Finset.range d, (A.singularValues i - B.singularValues i) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
      intro i _ hi
      have hi' : d ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
      simp [hzero A i hi', hzero B i hi']
    _ ≤ _ := hmin

end LinearMap
