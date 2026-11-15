/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.SinTheta
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Procrustes

/-!
# Population-gap bounds for a single eigenvector

Unit population and sample eigenvectors at the same sorted eigenvalue index can be aligned
by a unit scalar with distance at most `2 √2 ‖B-A‖ / δ`. Only the population spectrum needs
to be separated; the chosen sample eigenvector may lie in a repeated eigenspace.

Adapted from `yuWangSamworth_eigenvector_frame_le` in
`YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean`, Kitware DKPS
(Jon Crall and GPT 5.6 High; Apache-2.0), following Yu, Wang and Samworth,
Biometrika 102 (2015), Corollary 1.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-- Unit eigenvectors at corresponding sorted indices can be phase aligned with discrepancy
at most `2 √2 ‖B-A‖ / δ`, using only a gap in the population spectrum. Over `ℝ` the unit
scalar is a sign; over `ℂ` it is a phase. No sample simplicity is assumed. -/
theorem exists_norm_eq_one_and_norm_smul_sub_eigenvector_le
    {hA : A.IsSymmetric} {hB : B.IsSymmetric} {hn : finrank 𝕜 E = n}
    {j : Fin n} {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : 𝕜) • u)
    (hBv : B v = (hB.eigenvalues hn j : 𝕜) • v)
    {δ : ℝ} (hd : 0 < δ)
    (hgap : ∀ k : Fin n, k ≠ j → δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / δ := by
  classical
  let e : Fin 1 ↪ Fin n := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩
  have hon : ∀ x : E, ‖x‖ = 1 → Orthonormal 𝕜 (fun _ : Fin 1 => x) :=
    fun _ hx => orthonormal_subsingleton_iff.mpr fun _ => hx
  have hframeA : IsOrderedEigenframe hA hn e (fun _ => u) :=
    isOrderedEigenframe_iff.mpr ⟨hon u hu, fun _ => hAu⟩
  have hframeB : IsOrderedEigenframe hB hn e (fun _ => v) :=
    isOrderedEigenframe_iff.mpr ⟨hon v hv, fun _ => hBv⟩
  have hgapIdx : ∀ (i : Fin 1) (k : Fin n), k ∉ Set.range e →
      δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k| := by
    intro i k hk
    exact hgap k fun hkj => hk ⟨i, hkj.symm⟩
  let U := Submodule.span 𝕜 (Set.range (fun _ : Fin 1 => u))
  let V := Submodule.span 𝕜 (Set.range (fun _ : Fin 1 => v))
  have hsine : U.sinThetaFrobenius V ≤ 2 * ‖(B - A).toContinuousLinearMap‖ / δ := by
    have h := sinThetaFrobenius_orderedEigenframe_le hframeA hframeB hd hgapIdx
    refine h.trans ?_
    simp only [Fintype.card_fin, Nat.cast_one, Real.sqrt_one, one_mul]
    gcongr
    exact min_le_left _ _
  obtain ⟨w, hw, hspan, hsum⟩ :=
    TauCeti.exists_orthonormal_span_eq_sum_norm_sub_sq_le (hon u hu) (hon v hv)
  have hdim : finrank 𝕜 U = finrank 𝕜 V :=
    hframeA.finrank_span.trans hframeB.finrank_span.symm
  have hbridge := U.sq_sinThetaFrobenius_eq_sinThetaSq_of_orthonormal V
    (hon u hu) (hon v hv) rfl rfl
  rw [← hbridge, V.sinThetaFrobenius_comm U hdim.symm] at hsum
  have hmem : w 0 ∈ Submodule.span 𝕜 {v} := by
    have hwmem : w 0 ∈ Submodule.span 𝕜 (Set.range w) := Submodule.subset_span ⟨0, rfl⟩
    rw [hspan, Set.range_const] at hwmem
    exact hwmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcnorm : ‖c‖ = 1 := by
    have hnorm := hw.norm_eq_one 0
    rw [← hc, norm_smul, hv, mul_one] at hnorm
    exact hnorm
  refine ⟨c, hcnorm, ?_⟩
  calc
    ‖c • v - u‖ = Real.sqrt (∑ i : Fin 1, ‖w i - u‖ ^ 2) := by
      rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _), hc]
    _ ≤ Real.sqrt (2 * U.sinThetaFrobenius V ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * U.sinThetaFrobenius V := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq (Submodule.sinThetaFrobenius_nonneg U V)]
    _ ≤ Real.sqrt 2 * (2 * ‖(B - A).toContinuousLinearMap‖ / δ) :=
      mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = _ := by ring

end LinearMap.IsSymmetric
