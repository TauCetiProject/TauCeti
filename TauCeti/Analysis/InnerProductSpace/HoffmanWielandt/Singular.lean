/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Algebra.Order.BigOperators.Sum.ByParts

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

/-- **Weighted Ky Fan trace core.** If the partial real diagonal pairings of two orthonormal
families are bounded by the Ky Fan sums, pairing them with any nonnegative antitone weights is
bounded by the same weighted pairing with the singular values. -/
theorem sum_antitone_mul_re_inner_le_sum_mul_singularValues (B : E →ₗ[𝕜] F) {n : ℕ}
    (u : Fin n → F) (v : Fin n → E) (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    {w : ℕ → ℝ} (hw : Antitone w) (hw0 : ∀ i, 0 ≤ w i) :
    ∑ i : Fin n, w i * RCLike.re ⟪u i, B (v i)⟫_𝕜 ≤
      ∑ i : Fin n, w i * B.singularValues i := by
  let f : ℕ → ℝ := fun i ↦
    if hi : i < n then RCLike.re ⟪u ⟨i, hi⟩, B (v ⟨i, hi⟩)⟫_𝕜 else 0
  let g : ℕ → ℝ := fun i ↦ B.singularValues i
  have hfg : ∀ k ≤ n, ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range k, g i := by
    intro k hk
    have hsum : ∑ i : Fin k, f i =
        ∑ i : Fin k, RCLike.re ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_𝕜 := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcast : (⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩ : Fin n) = Fin.castLE hk i := by
        exact Fin.ext rfl
      simp [f, hcast, lt_of_lt_of_le i.isLt hk]
    have hreal : ∑ i ∈ Finset.range k, f i ≤ B.kyFanSum k := by
      calc
        _ = ∑ i : Fin k, f i := by rw [Fin.sum_univ_eq_sum_range]
        _ = ∑ i : Fin k,
            RCLike.re ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_𝕜 := hsum
        _ ≤ B.kyFanSum k := by
          simpa only [Fintype.card_fin] using B.sum_re_inner_apply_le_kyFanSum
            (fun i ↦ u (Fin.castLE hk i)) (fun i ↦ v (Fin.castLE hk i))
            (hu.comp _ (Fin.castLE_injective hk)) (hv.comp _ (Fin.castLE_injective hk))
    simpa [LinearMap.kyFanSum_def, g] using hreal
  have hcross := TauCeti.sum_range_mul_le_sum_range_mul (w := w) hfg
    (fun i _ ↦ hw (Nat.le_succ i)) (hw0 _)
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ w i * f i),
    ← Fin.sum_univ_eq_sum_range (fun i ↦ w i * g i)] at hcross
  simpa [f, g] using hcross

/-- **The singular-value Hoffman–Wielandt inequality** when the domain dimension does not exceed
the codomain dimension. The squared distance between the ordered singular values is at most the
squared Frobenius seminorm of the difference. -/
theorem sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le
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
    u v hu hv A.singularValues_antitone A.singularValues_nonneg
  have hB2 :
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F B ^ 2 =
          ∑ i : Fin (finrank 𝕜 E), B.singularValues i ^ 2 := by
    rw [TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
      ← B.sum_fin_singularValues (· ^ 2) (by simp)]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg (B.singularValues i))
  have hBbasis :
      ∑ i : Fin (finrank 𝕜 E), ‖B (v i)‖ ^ 2 =
        ∑ i : Fin (finrank 𝕜 E), B.singularValues i ^ 2 := by
    rw [← TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply v B, hB2]
  have hexp (i : Fin (finrank 𝕜 E)) :
      ‖(A - B) (v i)‖ ^ 2 =
        A.singularValues i ^ 2 -
          2 * (A.singularValues i *
            RCLike.re ⟪u i, B (v i)⟫_𝕜) + ‖B (v i)‖ ^ 2 := by
    rw [sub_apply, hAv i, norm_sub_sq (𝕜 := 𝕜)]
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
The sum runs over the first `min (finrank 𝕜 E) (finrank 𝕜 F)` singular values; beyond that index,
both maps' singular values are zero. -/
theorem sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_min
    (A B : E →ₗ[𝕜] F) :
    ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
        (A.singularValues i - B.singularValues i) ^ 2 ≤
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) ^ 2 := by
  by_cases hEF : finrank 𝕜 E ≤ finrank 𝕜 F
  · have hm : min (finrank 𝕜 E) (finrank 𝕜 F) = finrank 𝕜 E :=
      Nat.min_eq_left hEF
    rw [hm]
    exact A.sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le B hEF
  · have hFE : finrank 𝕜 F ≤ finrank 𝕜 E := le_of_not_ge hEF
    have h := (adjoint A).sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_of_finrank_le
      (adjoint B) hFE
    have hm : min (finrank 𝕜 E) (finrank 𝕜 F) = finrank 𝕜 F :=
      Nat.min_eq_right hFE
    have hadj_sub : adjoint A - adjoint B = adjoint (A - B) :=
      (map_sub LinearMap.adjoint A B).symm
    have hnorm :
        TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 F E (adjoint (A - B)) =
          TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) := by
      rw [← TauCeti.UnitarilyInvariantSeminorm.schatten_two (𝕜 := 𝕜) (E := F) (F := E),
        ← TauCeti.UnitarilyInvariantSeminorm.schatten_two (𝕜 := 𝕜) (E := E) (F := F),
        TauCeti.UnitarilyInvariantSeminorm.schatten_apply_adjoint]
    rw [hm]
    rw [singularValues_adjoint, singularValues_adjoint, hadj_sub, hnorm] at h
    exact h

end LinearMap
