/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.Matrix.SingularValues

/-!
# Hoffman–Wielandt inequality for singular values

For two linear maps with the same finite-dimensional domain and codomain, the squared Euclidean
distance between their decreasingly ordered singular values is at most the squared Frobenius
distance between the maps.
-/

public section

open Module
open scoped InnerProductSpace

namespace LinearMap

private theorem weighted_sum_le_of_prefixSum_le {n : ℕ} (c x y : Fin n → ℝ)
    (hc : Antitone c) (hc0 : ∀ i, 0 ≤ c i)
    (hxy : ∀ k, k ≤ n → TauCeti.prefixSum k x ≤ TauCeti.prefixSum k y) :
    ∑ i, c i * x i ≤ ∑ i, c i * y i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let c' : Fin n → ℝ := fun i ↦ c i.castSucc - c (Fin.last n)
      have hc' : Antitone c' := by
        intro i j hij
        exact sub_le_sub_right (hc (by simpa using hij)) _
      have hc'0 : ∀ i, 0 ≤ c' i := by
        intro i
        exact sub_nonneg.mpr (hc (Fin.le_last i.castSucc))
      have hxy' : ∀ k, k ≤ n →
          TauCeti.prefixSum k (fun i : Fin n ↦ x i.castSucc) ≤
            TauCeti.prefixSum k (fun i : Fin n ↦ y i.castSucc) := by
        intro k hk
        change TauCeti.prefixSum k (Fin.init x) ≤ TauCeti.prefixSum k (Fin.init y)
        rw [TauCeti.prefixSum_init hk x, TauCeti.prefixSum_init hk y]
        exact hxy k (by omega)
      have h' := ih c' (fun i : Fin n ↦ x i.castSucc)
        (fun i : Fin n ↦ y i.castSucc) hc' hc'0 hxy'
      have htotal := hxy (n + 1) le_rfl
      rw [TauCeti.prefixSum_of_le (n := n + 1) (k := n + 1) le_rfl,
        TauCeti.prefixSum_of_le (n := n + 1) (k := n + 1) le_rfl] at htotal
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at htotal ⊢
      have hdecomp (z : Fin (n + 1) → ℝ) :
          (∑ i : Fin n, c' i * z i.castSucc) +
              c (Fin.last n) * (∑ i : Fin n, z i.castSucc + z (Fin.last n)) =
            ∑ i : Fin n, c i.castSucc * z i.castSucc +
              c (Fin.last n) * z (Fin.last n) := by
        simp only [c', sub_mul, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        ring
      rw [← hdecomp x, ← hdecomp y]
      exact add_le_add h' (mul_le_mul_of_nonneg_left htotal (hc0 (Fin.last n)))

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **The von Neumann trace inequality for rectangular maps.** For decreasing singular values of
`A`, their weighted pairing with the diagonal matrix coefficients of `B` in the singular bases of
`A` is bounded by the sorted pairing of the singular values of `A` and `B`. -/
theorem sum_singularValues_mul_re_inner_le_sum_singularValues_mul_singularValues
    (A B : E →ₗ[𝕜] F) (hEF : finrank 𝕜 E ≤ finrank 𝕜 F)
    (w : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) :
    ∑ i : Fin (finrank 𝕜 E), A.singularValues i *
        RCLike.re ⟪w (Fin.castLE hEF i), B (A.rightSingularBasis i)⟫_𝕜 ≤
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i * B.singularValues i := by
  let u : Fin (finrank 𝕜 E) → F := fun i ↦ w (Fin.castLE hEF i)
  let v := A.rightSingularBasis
  have hu : Orthonormal 𝕜 u :=
    w.orthonormal.comp _ (Fin.castLE_injective hEF)
  have hv : Orthonormal 𝕜 v := v.orthonormal
  let c : Fin (finrank 𝕜 E) → ℝ := fun i ↦ A.singularValues i
  let x : Fin (finrank 𝕜 E) → ℝ := fun i ↦
    RCLike.re ⟪u i, B (v i)⟫_𝕜
  let y : Fin (finrank 𝕜 E) → ℝ := fun i ↦ B.singularValues i
  have hprefix (k : ℕ) (hk : k ≤ finrank 𝕜 E) :
      TauCeti.prefixSum k x ≤ TauCeti.prefixSum k y := by
    let f : ℕ → ℝ := fun i ↦ if hi : i < finrank 𝕜 E then x ⟨i, hi⟩ else 0
    let g : ℕ → ℝ := fun i ↦ B.singularValues i
    have hf : (fun i : Fin (finrank 𝕜 E) ↦ f i) = x := by
      ext i
      simp [f]
    have hg : (fun i : Fin (finrank 𝕜 E) ↦ g i) = y := by
      ext i
      rfl
    have hnorm :
        ‖∑ i : Fin k, ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_𝕜‖ ≤ B.kyFanSum k :=
      by
        simpa using B.norm_sum_inner_le_kyFanSum
          (hu.comp _ (Fin.castLE_injective hk)) (hv.comp _ (Fin.castLE_injective hk))
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
        _ ≤ _ := RCLike.re_le_norm _
        _ ≤ _ := hnorm
    rw [← hf, ← hg, TauCeti.prefixSum_eq_sum_range k f,
      TauCeti.prefixSum_eq_sum_range k g]
    simpa [LinearMap.kyFanSum_def, Nat.min_eq_left hk] using hreal
  have hc : Antitone c := fun i j hij ↦
    A.singularValues_antitone (Fin.le_def.mp hij)
  have hc0 : ∀ i, 0 ≤ c i := fun i ↦ A.singularValues_nonneg i
  have hcross := weighted_sum_le_of_prefixSum_le c x y hc hc0
    (fun k hk ↦ hprefix k hk)
  simpa [c, x, y, u, v] using hcross

/-- **The singular-value Hoffman–Wielandt inequality** for maps whose domain dimension does not
exceed their codomain dimension. The squared Euclidean distance between the ordered singular
values is at most the squared Frobenius seminorm of the difference. -/
theorem sum_sq_singularValues_sub_le_frobenius_sq
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
    B hEF w
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

theorem frobenius_apply_adjoint (A : E →ₗ[𝕜] F) :
    TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 F E (adjoint A) =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F A := by
  rw [TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    singularValues_adjoint]

/-- **The singular-value Hoffman–Wielandt inequality** for arbitrary finite-dimensional maps,
with zero padding to the smaller of the domain and codomain dimensions. -/
theorem sum_sq_singularValues_sub_le_frobenius_sq_min
    (A B : E →ₗ[𝕜] F) :
    ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
        (A.singularValues i - B.singularValues i) ^ 2 ≤
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) ^ 2 := by
  by_cases hEF : finrank 𝕜 E ≤ finrank 𝕜 F
  · have hm : min (finrank 𝕜 E) (finrank 𝕜 F) = finrank 𝕜 E :=
      Nat.min_eq_left hEF
    rw [hm]
    exact A.sum_sq_singularValues_sub_le_frobenius_sq B hEF
  · have hFE : finrank 𝕜 F ≤ finrank 𝕜 E := le_of_not_ge hEF
    have h := (adjoint A).sum_sq_singularValues_sub_le_frobenius_sq (adjoint B) hFE
    have hm : min (finrank 𝕜 E) (finrank 𝕜 F) = finrank 𝕜 F :=
      Nat.min_eq_right hFE
    have hadj_sub : adjoint A - adjoint B = adjoint (A - B) := by
      ext y
      refine ext_inner_right 𝕜 fun x ↦ ?_
      calc
        ⟪(adjoint A - adjoint B) y, x⟫_𝕜 =
            ⟪adjoint A y, x⟫_𝕜 - ⟪adjoint B y, x⟫_𝕜 := by
              rw [sub_apply, inner_sub_left]
        _ = ⟪y, A x⟫_𝕜 - ⟪y, B x⟫_𝕜 := by
              rw [adjoint_inner_left, adjoint_inner_left]
        _ = ⟪y, (A - B) x⟫_𝕜 := by rw [sub_apply, inner_sub_right]
        _ = ⟪adjoint (A - B) y, x⟫_𝕜 := by rw [adjoint_inner_left]
    have hnorm :
        TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 F E (adjoint (A - B)) =
          TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F (A - B) := by
      exact (A - B).frobenius_apply_adjoint
    rw [hm]
    rw [singularValues_adjoint, singularValues_adjoint, hadj_sub, hnorm] at h
    exact h

end LinearMap

open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The singular-value Hoffman–Wielandt inequality** for same-shaped rectangular matrices:
the squared Euclidean distance between their ordered, zero-padded singular values is bounded by
the squared Frobenius norm of their difference. -/
theorem sum_sq_singularValues_sub_le_frobenius_norm_sub_sq
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
  have h := LinearMap.sum_sq_singularValues_sub_le_frobenius_sq_min
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
