/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Block
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Reflection
import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# The strict quarter-angle branch on complex Hilbert spaces

Ordered form bounds for an operator and its off-diagonal perturbation force the gap between
their upper invariant subspaces to be strictly below `√2/2`. The proof uses reflected centered
operators, a Lyapunov identity, similarity by a positive square root, and the continuous
functional calculus of the unitary reflection product. No finite-dimensionality or norm
attainment is assumed.

Adapted from `DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`, Kitware
DKPS (Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5; Apache-2.0).
The mathematical argument belongs to the off-diagonal Davis--Kahan tan(2Θ) theory.
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace Submodule

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive real-part spectral bound for the product of two subspace reflections
forces their projection gap to be strictly below `√2/2`. -/
theorem projectionGap_lt_sqrt_two_div_two_of_reflection_spectrum
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {α : ℝ} (hα : 0 < α)
    (hspec : ∀ z ∈ spectrum ℂ
      ((V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E)), α ≤ z.re) :
    U.projectionGap V < Real.sqrt 2 / 2 := by
  let W := (V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E)
  have hWunit : W ∈ unitary (E →L[ℂ] E) :=
    (unitary (E →L[ℂ] E)).mul_mem V.reflection_mem_unitary U.reflection_mem_unitary
  let : IsStarNormal W := isStarNormal_of_mem_unitary hWunit
  let D := U.starProjection - V.starProjection
  have hDstar : IsSelfAdjoint D :=
    (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  have hpoint (x : E) : ‖D x‖ ^ 2 ≤ (1 - α) / 2 * ‖x‖ ^ 2 := by
    have hpos := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (ContinuousLinearMap.nonneg_add_star_sub_smul_of_spectrum_re W hspec)).re_inner_nonneg_left x
    have hpoly : W + star W = (2 : ℂ) • 1 - (4 : ℂ) • (D * D) := by
      dsimp only [W]
      rw [star_mul, U.isSelfAdjoint_reflection.star_eq, V.isSelfAdjoint_reflection.star_eq]
      simpa only [← ContinuousLinearMap.mul_def, D] using reflection_comp_add_comp_reflection U V
    rw [hpoly] at hpos
    have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
      calc
        RCLike.re ⟪D (D x), x⟫_ℂ = RCLike.re ⟪(star D) (D x), x⟫_ℂ := by rw [hDstar.star_eq]
        _ = RCLike.re ⟪D x, D x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
        _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      mul_apply_eq_comp, map_sub] at hpos
    have htwo : RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) = 2 * ‖x‖ ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
    have hfour : RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
        4 * RCLike.re ⟪D (D x), x⟫_ℂ := by simp
    have halpha : RCLike.re ((starRingEnd ℂ) (((2 * α : ℝ) : ℂ)) * ⟪x, x⟫_ℂ) =
        (2 * α) * ‖x‖ ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
    rw [htwo, hfour, halpha, hDsq] at hpos
    linarith
  have hnorm : ‖D‖ ≤ Real.sqrt (max ((1 - α) / 2) 0) :=
    D.opNorm_le_sqrt_of_forall_sq_norm_le (le_max_right _ _) fun x =>
      (hpoint x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  rw [projectionGap_def]
  apply hnorm.trans_lt
  apply (Real.sqrt_lt' (by positivity : 0 < Real.sqrt 2 / 2)).2
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact max_lt (by linarith) (by norm_num)

/-- Dimension-free strict quarter-angle branch from the paper's ordered form
hypotheses and full off-diagonality. -/
theorem projectionGap_lt_sqrt_two_div_two_of_orderedFormGap
    (U V : Submodule ℂ E) (A H : E →L[ℂ] E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    U.projectionGap V < Real.sqrt 2 / 2 := by
  let c : ℝ := (a + b) / 2
  let δ : ℝ := (b - a) / 2
  let J : E →L[ℂ] E := U.reflection
  let K : E →L[ℂ] E := V.reflection
  let T := A - (c : ℂ) • (1 : E →L[ℂ] E)
  let S := A + H - (c : ℂ) • (1 : E →L[ℂ] E)
  let B := J * T
  let C := K * S
  let W := K * J
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAH := hA.add hH
  have hAHsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hJcommT : Commute J T :=
    (hAsym.commute_reflection U hAU).sub_right ((Commute.one_right J).smul_right (c : ℂ))
  have hKcommS : Commute K S :=
    (hAHsym.commute_reflection V hAplusH_V).sub_right ((Commute.one_right K).smul_right (c : ℂ))
  have hcenter : IsSelfAdjoint ((c : ℂ) • (1 : E →L[ℂ] E)) := by
    simp [isSelfAdjoint_iff, star_smul]
  have hJstar : star J = J := U.isSelfAdjoint_reflection.star_eq
  have hKstar : star K = K := V.isSelfAdjoint_reflection.star_eq
  have hSstar : IsSelfAdjoint S := hAH.sub hcenter
  have hCstar : IsSelfAdjoint C := by
    rw [isSelfAdjoint_iff]
    simp only [C, star_mul, hSstar.star_eq, hKstar]
    exact hKcommS.eq.symm
  have hBcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ (⟪B x, x⟫_ℂ).re := by
    intro x
    exact reflection_centered_form_lower U A hAsym hAU hUhigh hUperpLow x
  have hCcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ (⟪C x, x⟫_ℂ).re := by
    intro x
    exact reflection_centered_form_lower V (A + H) hAHsym hAplusH_V hVhigh hVperpLow x
  have hCnonneg : (0 : E →L[ℂ] E) ≤ C := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hCstar, ?_⟩
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (mul_nonneg hδ.le (sq_nonneg ‖x‖)).trans (hCcoer x)
  have hCunit := ContinuousLinearMap.isUnit_of_coercive C hδ hCcoer
  have hJH : J * H = -(H * J) := by
    simpa only [J, ContinuousLinearMap.mul_def] using
      reflection_comp_eq_neg_comp_of_maps_orthogonal U H hHU hHUperp
  have hS : S = T + H := by dsimp [S, T]; abel
  have hKSK : K * S * K = S := by
    rw [hKcommS.eq, mul_assoc, V.reflection_mul_self, mul_one]
  have hlyap : C * W + star W * C = B + B := by
    calc
      C * W + star W * C = (K * S * K) * J + J * (K * K) * S := by
        simp only [C, W, star_mul, hJstar, hKstar]
        noncomm_ring
      _ = S * J + J * S := by rw [hKSK, V.reflection_mul_self, mul_one]
      _ = J * T + J * T := by
        rw [hS, add_mul, mul_add, ← hJcommT.eq, hJH]
        abel
  let α := δ / (1 + ‖C ^ (1 / 2 : ℝ)‖ ^ 2)
  have hα : 0 < α := div_pos hδ (by positivity)
  apply projectionGap_lt_sqrt_two_div_two_of_reflection_spectrum U V hα
  intro z hz
  exact ContinuousLinearMap.le_re_of_mem_spectrum_of_positive_lyapunov B C W
    ⟨hCnonneg, hCunit⟩ (by simpa only [ContinuousLinearMap.mul_def] using hlyap) hδ.le hBcoer hz

end

end Submodule
