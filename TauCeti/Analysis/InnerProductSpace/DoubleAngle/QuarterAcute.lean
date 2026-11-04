/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Reflection
import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
import Mathlib.Analysis.RCLike.ContinuousMap

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
  classical
  let c : ℝ := (a + b) / 2
  let δ : ℝ := (b - a) / 2
  let T0 : E →L[ℂ] E := A - (c : ℂ) • ContinuousLinearMap.id ℂ E
  let S0 : E →L[ℂ] E := A + H - (c : ℂ) • ContinuousLinearMap.id ℂ E
  let J : E →L[ℂ] E := (U.reflection : E →L[ℂ] E)
  let K : E →L[ℂ] E := (V.reflection : E →L[ℂ] E)
  let B : E →L[ℂ] E := J ∘L T0
  let C : E →L[ℂ] E := K ∘L S0
  let W : E →L[ℂ] E := K ∘L J
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hAH : IsSelfAdjoint (A + H) := hA.add hH
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAHsym : (A + H).toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hJcommA : J ∘L A = A ∘L J := by
    ext x
    -- Expose the reflection evaluation before applying its pointwise formula.
    change U.reflection (A x) = A (U.reflection x)
    have hc := hAsym.starProjection_apply_comm hAU x
    simp only [ContinuousLinearMap.coe_coe] at hc
    rw [Submodule.reflection_apply, Submodule.reflection_apply, hc, map_sub, map_nsmul]
  have hKcommAH : K ∘L (A + H) = (A + H) ∘L K := by
    ext x
    -- Expose the reflection evaluation before applying its pointwise formula.
    change V.reflection ((A + H) x) = (A + H) (V.reflection x)
    have hc := hAHsym.starProjection_apply_comm hAplusH_V x
    simp only [ContinuousLinearMap.coe_coe] at hc
    rw [Submodule.reflection_apply, Submodule.reflection_apply, hc, map_sub, map_nsmul]
  have hJstar : star J = J := by
    -- Use the continuous linear map underlying the reflection isometry.
    change star (U.reflection : E →L[ℂ] E) = _
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm,
      Submodule.reflection_symm]
  have hKstar : star K = K := by
    -- Use the continuous linear map underlying the reflection isometry.
    change star (V.reflection : E →L[ℂ] E) = _
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm,
      Submodule.reflection_symm]
  have hJ2 : J ∘L J = ContinuousLinearMap.id ℂ E := by
    ext x
    exact U.reflection_reflection x
  have hK2 : K ∘L K = ContinuousLinearMap.id ℂ E := by
    ext x
    exact V.reflection_reflection x
  have hT0star : IsSelfAdjoint T0 := by
    rw [isSelfAdjoint_iff]
    dsimp [T0, c]
    rw [star_sub, star_smul, hA.star_eq,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
    simp
  have hS0star : IsSelfAdjoint S0 := by
    rw [isSelfAdjoint_iff]
    dsimp [S0, c]
    rw [star_sub, star_smul, hAH.star_eq,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
    simp
  have hJcommT0 : J ∘L T0 = T0 ∘L J := by
    dsimp [T0]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      hJcommA]
    ext x
    simp
  have hKcommS0 : K ∘L S0 = S0 ∘L K := by
    dsimp [S0]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      hKcommAH]
    ext x
    simp
  have hCstar : IsSelfAdjoint C := by
    rw [isSelfAdjoint_iff]
    dsimp [C]
    -- Read composition as multiplication in the bounded-operator algebra.
    change star (K * S0) = K * S0
    rw [star_mul, hS0star.star_eq, hKstar]
    -- Return the commutation identity to the composition representation.
    change S0 ∘L K = K ∘L S0
    exact hKcommS0.symm
  have hBcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
    intro x
    simpa [B, T0, J, c, δ, ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, ContinuousLinearMap.id_apply] using
      Submodule.reflection_centered_form_lower U A hAsym hAU hUhigh hUperpLow x
  have hCcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪C x, x⟫_ℂ := by
    intro x
    simpa [C, S0, K, c, δ, ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, ContinuousLinearMap.id_apply] using
      Submodule.reflection_centered_form_lower V (A + H) hAHsym hAplusH_V
        hVhigh hVperpLow x
  have hCnonneg : (0 : E →L[ℂ] E) ≤ C := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hCstar, ?_⟩
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (mul_nonneg hδ.le (sq_nonneg ‖x‖)).trans (hCcoer x)
  have hCunit : IsUnit C := ContinuousLinearMap.isUnit_of_coercive C hδ hCcoer
  -- The positive square root supplies a bounded similarity and its inverse.
  let R : E →L[ℂ] E := C ^ (1 / 2 : ℝ)
  let Rinv : E →L[ℂ] E := C ^ (-1 / 2 : ℝ)
  have hRinvR : Rinv ∘L R = ContinuousLinearMap.id ℂ E := by
    -- Read composition as multiplication in the bounded-operator algebra.
    change Rinv * R = 1
    calc
      Rinv * R = C ^ (-1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) := rfl
      _ = C ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero C hCnonneg
  have hRRinv : R ∘L Rinv = ContinuousLinearMap.id ℂ E := by
    -- Read composition as multiplication in the bounded-operator algebra.
    change R * Rinv = 1
    calc
      R * Rinv = C ^ (1 / 2 : ℝ) * C ^ (-1 / 2 : ℝ) := rfl
      _ = C ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero C hCnonneg
  have hRR : R ∘L R = C := by
    -- Read composition as multiplication in the bounded-operator algebra.
    change R * R = C
    calc
      R * R = C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) := rfl
      _ = C ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (1 : ℝ) := by norm_num
      _ = C := CFC.rpow_one C hCnonneg
  have hRstar : star R = R := by
    exact (CFC.rpow_nonneg (a := C) (y := (1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hRinvstar : star Rinv = Rinv := by
    exact (CFC.rpow_nonneg (a := C) (y := (-1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hJH : J ∘L H = -(H ∘L J) := by
    simpa only [J] using Submodule.reflection_comp_eq_neg_comp_of_maps_orthogonal U H hHU hHUperp
  have hWstar : star W = J ∘L K := by
    dsimp [W]
    -- Read composition as multiplication in the bounded-operator algebra.
    change star (K * J) = J * K
    rw [star_mul, hJstar, hKstar]
  -- Invariance and off-diagonality give the exact Lyapunov identity.
  have hlyap : C ∘L W + star W ∘L C = B + B := by
    rw [hWstar]
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    -- Expose the block compositions on the chosen vector.
    change K (S0 (K (J x))) + J (K (K (S0 x))) =
      J (T0 x) + J (T0 x)
    have hKcomm_apply (y : E) : K (S0 y) = S0 (K y) := by
      have h := DFunLike.congr_fun hKcommS0 y
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hK2_apply (y : E) : K (K y) = y := by
      have h := DFunLike.congr_fun hK2 y
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    have hJT0_apply (y : E) : J (T0 y) = T0 (J y) := by
      have h := DFunLike.congr_fun hJcommT0 y
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hJH_apply (y : E) : J (H y) = -H (J y) := by
      have h := DFunLike.congr_fun hJH y
      simpa only [ContinuousLinearMap.comp_apply, neg_apply] using h
    have hS0_apply (y : E) : S0 y = T0 y + H y := by
      dsimp [S0, T0]
      simp only [sub_apply, add_apply, smul_apply,
        ContinuousLinearMap.id_apply]
      module
    have hfirst : K (S0 (K (J x))) = S0 (J x) := by
      rw [hKcomm_apply, hK2_apply]
    have hsecond : J (K (K (S0 x))) = J (S0 x) := by
      rw [hK2_apply]
    rw [hfirst, hsecond, hS0_apply, hS0_apply,
      map_add, hJT0_apply, hJH_apply]
    abel
  -- Conjugation by the square root makes the reflection product coercive.
  let Z : E →L[ℂ] E := R ∘L W ∘L Rinv
  have hZstar : star Z = Rinv ∘L star W ∘L R := by
    dsimp [Z]
    -- Read composition as multiplication in the bounded-operator algebra.
    change star (R * W * Rinv) = Rinv * star W * R
    rw [star_mul, star_mul, hRstar, hRinvstar]
    simp only [mul_assoc]
  have hleft : Rinv ∘L C = R := by
    apply ContinuousLinearMap.ext
    intro x
    have hRRx := DFunLike.congr_fun hRR x
    have hInv := DFunLike.congr_fun hRinvR (R x)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hRRx hInv ⊢
    rw [← hRRx]
    exact hInv
  have hright : C ∘L Rinv = R := by
    apply ContinuousLinearMap.ext
    intro x
    have hRRx := DFunLike.congr_fun hRR (Rinv x)
    have hInv := DFunLike.congr_fun hRRinv x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hRRx hInv ⊢
    rw [← hRRx, hInv]
  have hZherm :
      Z + star Z =
        (Rinv ∘L B ∘L Rinv) + (Rinv ∘L B ∘L Rinv) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [hZstar]
    dsimp [Z]
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    have hlyapx := DFunLike.congr_fun hlyap (Rinv x)
    have hconj := congrArg (fun y : E => Rinv y) hlyapx
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add] at hconj
    have hleftx := DFunLike.congr_fun hleft (W (Rinv x))
    have hrightx := DFunLike.congr_fun hright x
    simp only [ContinuousLinearMap.comp_apply] at hleftx hrightx
    rw [hleftx, hrightx] at hconj
    exact hconj
  let α : ℝ := δ / (1 + ‖R‖ ^ 2)
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hZcoer : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪Z x, x⟫_ℂ := by
    intro x
    let y : E := Rinv x
    have hxy : R y = x := by
      dsimp [y]
      have := DFunLike.congr_fun hRRinv x
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using this
    have hreal : RCLike.re ⟪Z x, x⟫_ℂ = RCLike.re ⟪B y, y⟫_ℂ := by
      have hsum := congrArg
        (fun T : E →L[ℂ] E => RCLike.re ⟪T x, x⟫_ℂ) hZherm
      simp only [add_apply, inner_add_left, map_add,
        ContinuousLinearMap.comp_apply] at hsum
      have hstarReal : RCLike.re ⟪star Z x, x⟫_ℂ =
          RCLike.re ⟪Z x, x⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
        exact inner_re_symm x (Z x)
      have hRinvAdj : ContinuousLinearMap.adjoint Rinv = Rinv := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact hRinvstar
      have hRinvInner : RCLike.re ⟪Rinv (B y), x⟫_ℂ =
          RCLike.re ⟪B y, y⟫_ℂ := by
        rw [← hRinvAdj, ContinuousLinearMap.adjoint_inner_left]
      rw [hstarReal, hRinvInner] at hsum
      linarith
    have hB := hBcoer y
    have hnorm : ‖x‖ ≤ ‖R‖ * ‖y‖ := by
      rw [← hxy]
      exact R.le_opNorm y
    have hsq : ‖x‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖y‖ ^ 2 := by
      nlinarith [hnorm, norm_nonneg x, norm_nonneg R, norm_nonneg y]
    rw [hreal]
    dsimp [α]
    have hden : 0 < 1 + ‖R‖ ^ 2 := by positivity
    have hcoef : δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2 ≤ δ := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith [hδ]
    have hscaled : δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤ δ * ‖y‖ ^ 2 := by
      calc
        δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
            δ / (1 + ‖R‖ ^ 2) * (‖R‖ ^ 2 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg hδ.le hden.le)
        _ = (δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2) * ‖y‖ ^ 2 := by ring
        _ ≤ δ * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
    exact hscaled.trans hB
  -- Transport the coercive half-plane bound through similarity.
  have hspecZ : ∀ z ∈ spectrum ℂ Z, α ≤ z.re :=
    fun z hz => _root_.ContinuousLinearMap.le_re_of_mem_spectrum_of_coercive Z hZcoer hz
  have hspecWZ : spectrum ℂ W = spectrum ℂ Z := by
    let e : E ≃L[ℂ] E := ContinuousLinearEquiv.equivOfInverse' R Rinv hRRinv hRinvR
    have he : e.conjContinuousAlgEquiv.toAlgEquiv W = Z := by
      ext x
      rfl
    exact ((AlgEquiv.spectrum_eq e.conjContinuousAlgEquiv.toAlgEquiv W).symm).trans
      (congrArg (spectrum ℂ) he)
  have hspecW : ∀ z ∈ spectrum ℂ W, α ≤ z.re := by
    intro z hz
    rw [hspecWZ] at hz
    exact hspecZ z hz
  have hWunit : W ∈ unitary (E →L[ℂ] E) := by
    simpa only [W, K, J, ContinuousLinearMap.mul_def,
      Unitary.coe_symm_linearIsometryEquiv_apply] using
      (unitary (E →L[ℂ] E)).mul_mem
        (Unitary.linearIsometryEquiv.symm V.reflection).property
        (Unitary.linearIsometryEquiv.symm U.reflection).property
  let hWnormal : IsStarNormal W := isStarNormal_of_mem_unitary hWunit
  let : IsStarNormal W := hWnormal
  -- The unitary reflection product is normal, so its spectrum controls its real part.
  have hshiftForm : ∀ x : E,
      0 ≤ RCLike.re
        ⟪(W + star W - ((2 * α : ℝ) : ℂ) • 1) x, x⟫_ℂ := by
    intro x
    let X : C(spectrum ℂ W, ℂ) :=
      (ContinuousMap.id ℂ).restrict (spectrum ℂ W)
    let g : C(spectrum ℂ W, ℝ) :=
      ⟨fun z => 2 * (z : ℂ).re - 2 * α,
        (continuous_const.mul
          (Complex.continuous_re.comp continuous_subtype_val)).sub continuous_const⟩
    have hg : ∀ z, 0 ≤ g z := by
      intro z
      dsimp [g]
      have hz := hspecW (z : ℂ) z.property
      linarith
    have hpos : 0 ≤
        (⟪x, cfcHom hWnormal
          ((ContinuousMap.realToRCLikeStarAlgHom _ ℂ) g) x⟫_ℂ).re := by
      have hT : 0 ≤ cfcHom hWnormal
          ((ContinuousMap.realToRCLikeStarAlgHom _ ℂ) g) := by
        apply map_nonneg (cfcHom hWnormal)
        intro z
        simpa using hg z
      exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right x
    have hsymbol :
        (ContinuousMap.realToRCLikeStarAlgHom _ ℂ) g =
          X + star X - ((2 * α : ℝ) : ℂ) • 1 := by
      ext z
      dsimp [g, X]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [hsymbol, map_sub, map_add, map_star, map_smul, map_one,
      cfcHom_id] at hpos
    -- Evaluate the CFC operator through its quadratic form.
    change 0 ≤ RCLike.re
      ⟪x, (W + star W - ((2 * α : ℝ) : ℂ) • 1) x⟫_ℂ at hpos
    exact hpos.trans_eq (inner_re_symm x
      ((W + star W - ((2 * α : ℝ) : ℂ) • 1) x))
  -- The real part of the reflection product equals a polynomial in the projection gap.
  let D : E →L[ℂ] E := U.starProjection - V.starProjection
  have hreflectionAlgebra :
      W + star W =
        (2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D) := by
    rw [hWstar]
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self,
      mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
    dsimp [W, J, K, D]
    have hKJ :
        (V.reflection : E →L[ℂ] E) ((U.reflection : E →L[ℂ] E) x) =
          (4 : ℂ) • V.starProjection (U.starProjection x) -
            (2 : ℂ) • V.starProjection x -
            (2 : ℂ) • U.starProjection x + x := by
      simp only [LinearIsometryEquiv.coe_coe'']
      rw [Submodule.reflection_apply (K := V), Submodule.reflection_apply (K := U)]
      simp only [map_sub, map_nsmul]
      module
    have hJK :
        (U.reflection : E →L[ℂ] E) ((V.reflection : E →L[ℂ] E) x) =
          (4 : ℂ) • U.starProjection (V.starProjection x) -
            (2 : ℂ) • U.starProjection x -
            (2 : ℂ) • V.starProjection x + x := by
      simp only [LinearIsometryEquiv.coe_coe'']
      rw [Submodule.reflection_apply (K := U), Submodule.reflection_apply (K := V)]
      simp only [map_sub, map_nsmul]
      module
    have hPU : U.starProjection (U.starProjection x) = U.starProjection x :=
      Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
    have hPV : V.starProjection (V.starProjection x) = V.starProjection x :=
      Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
    have hDDx :
        (U.starProjection - V.starProjection)
            ((U.starProjection - V.starProjection) x) =
          U.starProjection x - U.starProjection (V.starProjection x) -
            V.starProjection (U.starProjection x) + V.starProjection x := by
      simp only [sub_apply, map_sub, hPU, hPV]
      abel
    simp only [LinearIsometryEquiv.coe_coe''] at hKJ hJK
    rw [hKJ, hJK, hDDx]
    module
  have hpoint : ∀ x, ‖D x‖ ^ 2 ≤ (1 - α) / 2 * ‖x‖ ^ 2 := by
    intro x
    have hpositive := hshiftForm x
    rw [hreflectionAlgebra] at hpositive
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, mul_apply_eq_comp] at hpositive
    have hDstar : IsSelfAdjoint D := by
      dsimp [D]
      exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
    have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
      calc
        RCLike.re ⟪D (D x), x⟫_ℂ =
            RCLike.re ⟪(star D) (D x), x⟫_ℂ := by rw [hDstar.star_eq]
        _ = RCLike.re ⟪D x, D x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
        _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
    rw [map_sub, map_sub] at hpositive
    have htwo :
        RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) =
          2 * ‖x‖ ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
    have hfour :
        RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
          4 * RCLike.re ⟪D (D x), x⟫_ℂ := by
      simp
    have halpha :
        RCLike.re ((starRingEnd ℂ) (((2 * α : ℝ) : ℂ)) * ⟪x, x⟫_ℂ) =
          (2 * α) * ‖x‖ ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
    rw [htwo, hfour, halpha, hDsq] at hpositive
    linarith
  rcases subsingleton_or_nontrivial E with htriv | hnontriv
  · rw [Submodule.projectionGap_def]
    have hzero : U.starProjection - V.starProjection = 0 :=
      ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
    rw [hzero, norm_zero]
    positivity
  · have hαle1 : α ≤ 1 := by
      obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne (0 : E)
      have hp := hpoint x
      have hxn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hmul : 0 ≤ (1 - α) / 2 * ‖x‖ ^ 2 :=
        (sq_nonneg ‖D x‖).trans hp
      have hc0 : 0 ≤ (1 - α) / 2 :=
        nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using hmul) hxn
      linarith
    have hc : 0 ≤ (1 - α) / 2 := by linarith
    have hDnorm : ‖D‖ ≤ Real.sqrt ((1 - α) / 2) := by
      refine D.opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
      calc
        ‖D x‖ = Real.sqrt (‖D x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((1 - α) / 2 * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hpoint x)
        _ = Real.sqrt ((1 - α) / 2) * ‖x‖ := by
          rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg x)]
    have hDsq : ‖D‖ ^ 2 < (1 : ℝ) / 2 := by
      have hsquare := pow_le_pow_left₀ (norm_nonneg D) hDnorm 2
      rw [Real.sq_sqrt hc] at hsquare
      have hstrict : (1 - α) / 2 < (1 : ℝ) / 2 := by linarith
      exact hsquare.trans_lt hstrict
    rw [Submodule.projectionGap_def]
    have hthresholdSq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hthresholdPos : 0 < Real.sqrt 2 / 2 := by positivity
    by_contra hnot
    have hle : Real.sqrt 2 / 2 ≤ ‖D‖ := le_of_not_gt hnot
    have hsqle := pow_le_pow_left₀ hthresholdPos.le hle 2
    rw [hthresholdSq] at hsqle
    exact (not_le_of_gt hDsq) hsqle

end

end Submodule
