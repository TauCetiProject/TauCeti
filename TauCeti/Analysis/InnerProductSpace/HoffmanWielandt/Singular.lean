/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.Algebra.Order.BigOperators.Sum.ByParts
public import TauCeti.Analysis.InnerProductSpace.HoffmanWielandt.Basic

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

/-- The real diagonal pairing of two orthonormal families under `B` is bounded by the Ky Fan
sum of its singular values. -/
theorem sum_re_inner_apply_le_kyFanSum (B : E →ₗ[𝕜] F) {k : ℕ}
    (u : Fin k → F) (v : Fin k → E) (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ i, RCLike.re ⟪u i, B (v i)⟫_𝕜 ≤ B.kyFanSum k := by
  calc
    ∑ i, RCLike.re ⟪u i, B (v i)⟫_𝕜 =
        RCLike.re (∑ i, ⟪u i, B (v i)⟫_𝕜) := by rw [← map_sum]
    _ ≤ ‖∑ i, ⟪u i, B (v i)⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ B.kyFanSum k := by simpa using B.norm_sum_inner_le_kyFanSum hu hv

/-- **The von Neumann trace inequality for rectangular maps.** For decreasing singular values of
`A`, their weighted pairing with the diagonal coefficients of `B` in any orthonormal family of
`F` paired with `A`'s right singular basis is bounded by the sorted pairing of the singular values
of `A` and `B`. -/
theorem sum_singularValues_mul_re_inner_le_sum_singularValues_mul_singularValues
    (A B : E →ₗ[𝕜] F) {u : Fin (finrank 𝕜 E) → F} (hu : Orthonormal 𝕜 u) :
    ∑ i : Fin (finrank 𝕜 E), A.singularValues i *
        RCLike.re ⟪u i, B (A.rightSingularBasis i)⟫_𝕜 ≤
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i := by
  let v := A.rightSingularBasis
  have hv : Orthonormal 𝕜 v := v.orthonormal
  let x : Fin (finrank 𝕜 E) → ℝ := fun i ↦
    RCLike.re ⟪u i, B (v i)⟫_𝕜
  let y : Fin (finrank 𝕜 E) → ℝ := fun i ↦ B.singularValues i
  let f : ℕ → ℝ := fun i ↦ if hi : i < finrank 𝕜 E then x ⟨i, hi⟩ else 0
  let g : ℕ → ℝ := fun i ↦ B.singularValues i
  have hf : (fun i : Fin (finrank 𝕜 E) ↦ f i) = x := by
    ext i
    simp [f]
  have hg : (fun i : Fin (finrank 𝕜 E) ↦ g i) = y := by
    ext i
    rfl
  have hprefix (k : ℕ) (hk : k ≤ finrank 𝕜 E) :
      TauCeti.prefixSum k x ≤ TauCeti.prefixSum k y := by
    have hsum : ∑ i : Fin k, f i =
        ∑ i : Fin k, x (Fin.castLE hk i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcast : (⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩ : Fin (finrank 𝕜 E)) =
          Fin.castLE hk i := by
        exact Fin.ext rfl
      simp [f, x, hcast, lt_of_lt_of_le i.isLt hk]
    have hreal : (∑ i ∈ Finset.range k, f i) ≤ B.kyFanSum k := by
      calc
        _ = ∑ i : Fin k, f i := by
          symm
          rw [Fin.sum_univ_eq_sum_range f]
        _ = ∑ i : Fin k, RCLike.re
            ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_𝕜 := by
          simpa [x] using hsum
        _ = RCLike.re
            (∑ i : Fin k, ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_𝕜) := by
          rw [← map_sum]
        _ ≤ B.kyFanSum k := by
          simpa only [← map_sum] using B.sum_re_inner_apply_le_kyFanSum
            (fun i ↦ u (Fin.castLE hk i)) (fun i ↦ v (Fin.castLE hk i))
            (hu.comp _ (Fin.castLE_injective hk)) (hv.comp _ (Fin.castLE_injective hk))
    rw [← hf, ← hg, TauCeti.prefixSum_eq_sum_range k f,
      TauCeti.prefixSum_eq_sum_range k g]
    simpa [LinearMap.kyFanSum_def, Nat.min_eq_left hk] using hreal
  have hfg : ∀ k ≤ finrank 𝕜 E, ∑ i ∈ Finset.range k, f i ≤
      ∑ i ∈ Finset.range k, g i := by
    intro k hk
    have h := hprefix k hk
    rw [← hf, ← hg, TauCeti.prefixSum_eq_sum_range k f,
      TauCeti.prefixSum_eq_sum_range k g] at h
    rw [Nat.min_eq_left hk] at h
    exact h
  have hcross := TauCeti.sum_range_mul_le_sum_range_mul
    (w := fun i ↦ A.singularValues i) hfg
    (fun i hi ↦ A.singularValues_antitone (by omega))
    (A.singularValues_nonneg (finrank 𝕜 E - 1))
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ A.singularValues i * f i),
    ← Fin.sum_univ_eq_sum_range (fun i ↦ A.singularValues i * g i)] at hcross
  have hf' (i : Fin (finrank 𝕜 E)) : f i = x i := congrFun hf i
  have hg' (i : Fin (finrank 𝕜 E)) : g i = y i := congrFun hg i
  have hcross' :
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * x i ≤
        ∑ i : Fin (finrank 𝕜 E), A.singularValues i * y i := by
    simpa only [hf', hg'] using hcross
  simpa [x, y, v] using hcross'

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
  have hcross := A.sum_singularValues_mul_re_inner_le_sum_singularValues_mul_singularValues
    B (w.orthonormal.comp _ (Fin.castLE_injective hEF))
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
  have hcross' :
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i *
          RCLike.re ⟪u i, B (v i)⟫_𝕜 ≤
        ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i := by
    simpa [u, v] using hcross
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
  nlinarith [hcross']

/-- **The singular-value Hoffman–Wielandt inequality** for arbitrary finite-dimensional maps,
with the sum indexed by the smaller of the domain and codomain dimensions. -/
theorem sum_sq_singularValues_sub_le_sq_frobenius_apply_sub
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

open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The singular-value Hoffman–Wielandt inequality** for same-shaped rectangular matrices:
the squared distance between their ordered singular values, summed up to the smaller dimension,
is bounded by the squared Frobenius norm of their difference. -/
theorem sum_sq_singularValues_toEuclideanLin_sub_le_frobenius_norm_sub_sq
    {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix m n 𝕜) :
    ∑ i : Fin (min (Fintype.card n) (Fintype.card m)),
        ((Matrix.toEuclideanLin A).singularValues i -
          (Matrix.toEuclideanLin B).singularValues i) ^ 2 ≤ ‖A - B‖ ^ 2 := by
  let e := EuclideanSpace.basisFun n 𝕜
  let f := EuclideanSpace.basisFun m 𝕜
  have hF : ‖A - B‖ = TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜
      (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) (Matrix.toEuclideanLin (A - B)) := by
    rw [← LinearMap.frobenius_norm_toMatrix _ e f, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have h := LinearMap.sum_sq_singularValues_sub_le_sq_frobenius_apply_sub
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
  have hn : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  have hm : finrank 𝕜 (EuclideanSpace 𝕜 m) = Fintype.card m := finrank_euclideanSpace
  have hF' :
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜
          (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m)
          (Matrix.toEuclideanLin A - Matrix.toEuclideanLin B) = ‖A - B‖ := by
    rw [← map_sub, hF]
  rw [hn, hm] at h
  simpa only [hF'] using h

end Matrix
