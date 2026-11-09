/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.SinTheta
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Procrustes

/-!
# Population-gap alignment of ordered eigenframes

For corresponding ordered eigenframes with a population-only spectral gap, the sample
frame can be rotated inside its span to be within `√2` times the population-gap
Frobenius sine bound of the supplied population frame. The population frame stays fixed;
no gap in the sample spectrum or simplicity of its eigenvalues is assumed.

Adapted from `yuWangSamworth_alignedBasis_frame_le` in
`YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean`, Kitware DKPS
(Jon Crall and GPT 5.6 High; Apache-2.0). The alignment itself uses the accepted
orthonormal-family Procrustes theorem, rather than the donor's polar-factor construction.
The mathematical source is Yu, Wang and Samworth, Biometrika 102 (2015), Theorem 2.
-/

public section

open Module (finrank)

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-- Corresponding ordered eigenframes admit an aligned sample frame with discrepancy at most
`2 √2 min(√d ‖B-A‖, ‖B-A‖_F) / δ`. The population frame is held fixed, and the finite
index type may be empty. Only the population eigenvalues need a gap. -/
theorem exists_orthonormal_span_eq_sqrt_sum_norm_sub_sq_le_of_orderedEigenframe
    {hA : A.IsSymmetric} {hB : B.IsSymmetric} {hn : finrank 𝕜 E = n}
    {ι : Type*} [Fintype ι] {e : ι ↪ Fin n} {u v : ι → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {δ : ℝ} (hd : 0 < δ)
    (hgap : ∀ (i : ι) (k : Fin n), k ∉ Set.range e →
      δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ w : ι → E, Orthonormal 𝕜 w ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range v) ∧
      Real.sqrt (∑ i, ‖w i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 * min (Real.sqrt (Fintype.card ι) * ‖(B - A).toContinuousLinearMap‖)
          (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)) / δ := by
  classical
  let U := Submodule.span 𝕜 (Set.range u)
  let V := Submodule.span 𝕜 (Set.range v)
  have huon := (isOrderedEigenframe_iff.mp hu).orthonormal
  have hvon := (isOrderedEigenframe_iff.mp hv).orthonormal
  obtain ⟨w, hw, hspan, hsum⟩ :=
    TauCeti.exists_orthonormal_span_eq_sum_norm_sub_sq_le huon hvon
  refine ⟨w, hw, hspan, ?_⟩
  have hdim : finrank 𝕜 U = finrank 𝕜 V := hu.finrank_span.trans hv.finrank_span.symm
  have hbridge := U.sq_sinThetaFrobenius_eq_sinThetaSq_of_orthonormal V huon hvon rfl rfl
  rw [← hbridge, V.sinThetaFrobenius_comm U hdim.symm] at hsum
  have hsine := sinThetaFrobenius_orderedEigenframe_le hu hv hd hgap
  calc
    Real.sqrt (∑ i, ‖w i - u i‖ ^ 2) ≤ Real.sqrt (2 * U.sinThetaFrobenius V ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * U.sinThetaFrobenius V := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq (Submodule.sinThetaFrobenius_nonneg U V)]
    _ ≤ Real.sqrt 2 *
        (2 * min (Real.sqrt (Fintype.card ι) * ‖(B - A).toContinuousLinearMap‖)
          (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)) / δ) :=
      mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = _ := by ring

end LinearMap.IsSymmetric
