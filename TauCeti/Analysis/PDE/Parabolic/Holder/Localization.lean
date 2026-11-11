/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.Bilinear

/-!
# Localization errors for parabolic operators

For a scalar parabolic operator `P = ∂ₜ - A·D_x² - B·D_x - C` and a space-time cutoff `χ`,
the commutator `P(χu) - χ Pu` contains only the value and first spatial derivative of `u`.
This file proves its product formula in bounded parabolic Hölder spaces and estimates it by
`‖u‖_{α,par} + ‖D_x u‖_{α,par}`. In particular the zeroth-order coefficient cancels, and no
ellipticity assumption is needed.

For `α < 1`, interpolation makes this error at most `η ‖u‖_{2+α,par} + K ‖u‖_∞`, for any
`η > 0`. The constant is uniform over slabs, coefficients and cutoffs with the stated bound
on their derivative norms. This is the lower-order error estimate used when localizing a
parabolic Schauder estimate; it does not assert the principal-part estimate itself.

Multiplying by a cutoff `χ` with values in `[0, 1]` does not increase the supremum norm, keeps a
vanishing trace, and makes the Hessian vanish wherever `χ` vanishes nearby; these are the
properties of the localizations `χ u` that a localized estimate uses.

The Hessian cross terms are kept separately, so the formula also applies to nonsymmetric
second-order coefficients. Time derivatives include the one-sided derivatives at both endpoints
of the closed slab.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 3 (localization
  and a priori estimates).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- A proof-local shortcut needed to infer the norm of the rank-one Hessian bilinear map. -/
private local instance instGradientNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
/-- The corresponding proof-local scalar-operation shortcut. -/
private local instance instGradientSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- Reuse the operator module's Hessian shortcuts for instance search in coefficient types.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

variable (hα : α ≤ 1)
  (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ))
  (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
  (C : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ))
  (χ u : ParabolicC2HolderSpace α E ℝ ht)

/-- **The localization commutator.** In `P(χu) - χ Pu`, the zeroth-order coefficient and the
second derivatives of `u` cancel. The two Hessian cross terms are the tensors
`Dχ ⊗ Du` and `Du ⊗ Dχ`, respectively. -/
theorem parabolicOperatorL_mul_sub_mul_parabolicOperatorL :
    parabolicOperatorL hα A B C ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) -
      (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
        (parabolicOperatorL hα A B C u) =
    (ContinuousLinearMap.mul ℝ ℝ).compHolder₂
        (timeDerivL χ - spatialOperatorL hα A B 0 χ) (valueHolderL hα u) -
      (ContinuousLinearMap.id ℝ _).compHolder₂ A
        ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂
            (spatialFDerivHolderL hα χ) (spatialFDerivHolderL hα u) +
          (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂
            (spatialFDerivHolderL hα u) (spatialFDerivHolderL hα χ)) := by
  ext p
  have hH : spatialSecondFDerivL
      ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) p =
      χ p • spatialSecondFDerivL u p + u p • spatialSecondFDerivL χ p +
        (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))
          (spatialFDerivL χ p) (spatialFDerivL u p) +
        (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))
          (spatialFDerivL u p) (spatialFDerivL χ p) := by
    ext h k
    simp
    ring
  have hD : spatialFDerivL
      ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) p =
      χ p • spatialFDerivL u p + u p • spatialFDerivL χ p := by
    ext h
    simp
    ring
  simp only [HolderSpace.sub_apply, ContinuousLinearMap.compHolder₂_apply,
    ContinuousLinearMap.mul_apply', valueHolderL_apply, parabolicOperatorL_apply,
    ContinuousLinearMap.timeDerivL_compParabolicC2Holder₂, hH, hD, map_add, map_smul,
    ContinuousLinearMap.compParabolicC2Holder₂_apply, spatialOperatorL_apply,
    HolderSpace.zero_apply, _root_.zero_apply, add_zero,
    ContinuousLinearMap.id_apply, HolderSpace.add_apply, spatialFDerivHolderL_apply,
    smul_eq_mul]
  have hc : C p (χ p * u p) = χ p * C p (u p) := by
    simpa only [smul_eq_mul] using (C p).map_smul (χ p) (u p)
  rw [hc]
  ring

/-- **The lower-order commutator bound.** Only the time derivative, spatial Hessian and
spatial gradient of the cutoff enter the bound. In particular it is independent of `C` and
of the second derivatives and time derivative of `u`. -/
theorem norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le :
    ‖parabolicOperatorL hα A B C
        ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) -
      (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
        (parabolicOperatorL hα A B C u)‖ ≤
      (‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
        (‖B‖ + 2 * ‖A‖) * ‖spatialFDerivHolderL hα χ‖) *
        (‖valueHolderL hα u‖ + ‖spatialFDerivHolderL hα u‖) := by
  -- The two cross terms are rank-one Hessians, each with the product bound.
  let T := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  have hT : ‖T‖ ≤ 1 := by
    simpa only [T] using
      (ContinuousLinearMap.norm_smulRightL_le (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ))
  have hcross (f g : HolderSpace α (slab (E := E) t₀ t₁) (E →L[ℝ] ℝ)) :
      ‖T.compHolder₂ f g‖ ≤ ‖f‖ * ‖g‖ :=
    (T.norm_compHolder₂_apply_le f g).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hT (norm_nonneg f)) (norm_nonneg g))
  -- The other error is multiplication by the time/spatial operator applied to the cutoff.
  have hZ : ‖timeDerivL χ - spatialOperatorL hα A B 0 χ‖ ≤
      ‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
        ‖B‖ * ‖spatialFDerivHolderL hα χ‖ := by
    have h := norm_spatialOperatorL_apply_le (A := A) (B := B) (C := 0) hα χ
    rw [norm_zero, zero_mul, add_zero] at h
    linarith [norm_sub_le (timeDerivL χ) (spatialOperatorL hα A B 0 χ)]
  -- Combine the three errors; every factor involving the solution has order at most one.
  rw [parabolicOperatorL_mul_sub_mul_parabolicOperatorL]
  have hvalue := (ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le
    (timeDerivL χ - spatialOperatorL hα A B 0 χ) (valueHolderL hα u)
  have hfirst : ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂
      (timeDerivL χ - spatialOperatorL hα A B 0 χ) (valueHolderL hα u)‖ ≤
      (‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
        ‖B‖ * ‖spatialFDerivHolderL hα χ‖) * ‖valueHolderL hα u‖ :=
    hvalue.trans (mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hZ)
      (norm_nonneg _))
  have hsecond := ContinuousLinearMap.norm_id_compHolder₂_apply_le A
    (T.compHolder₂ (spatialFDerivHolderL hα χ) (spatialFDerivHolderL hα u) +
      T.compHolder₂ (spatialFDerivHolderL hα u) (spatialFDerivHolderL hα χ))
  have hsum := (norm_add_le _ _).trans (add_le_add
    (hcross (spatialFDerivHolderL hα χ) (spatialFDerivHolderL hα u))
    (hcross (spatialFDerivHolderL hα u) (spatialFDerivHolderL hα χ)))
  refine (norm_sub_le _ _).trans ((add_le_add hfirst (hsecond.trans
    (mul_le_mul_of_nonneg_left hsum (norm_nonneg A)))).trans ?_)
  nlinarith [mul_nonneg
    (by positivity : 0 ≤ ‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
      ‖B‖ * ‖spatialFDerivHolderL hα χ‖) (norm_nonneg (spatialFDerivHolderL hα u)),
    mul_nonneg (by positivity : 0 ≤ ‖A‖ * ‖spatialFDerivHolderL hα χ‖)
      (norm_nonneg (valueHolderL hα u))]

/-- **The operator on a localization.** `P(χu)` is `χ P u` up to the localization commutator:
`‖P(χu)‖ ≤ 24 ‖χ‖ ‖P u‖ + ‖P(χu) - χ P u‖`. -/
theorem norm_parabolicOperatorL_mul_le :
    ‖parabolicOperatorL hα A B C ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖ ≤
      24 * ‖χ‖ * ‖parabolicOperatorL hα A B C u‖ +
        ‖parabolicOperatorL hα A B C ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) -
          (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
            (parabolicOperatorL hα A B C u)‖ := by
  refine (norm_le_insert' _ ((ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
    (parabolicOperatorL hα A B C u))).trans (add_le_add_left ?_ _)
  have hm : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hχ : ‖valueHolderL hα χ‖ ≤ 24 * ‖χ‖ := by
    linarith [norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα χ,
      norm_nonneg (spatialFDerivHolderL hα χ)]
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le _ _).trans ?_
  calc _ ≤ 1 * (24 * ‖χ‖) * ‖parabolicOperatorL hα A B C u‖ := by gcongr
    _ = _ := by ring

/-- **Uniform absorption of localization errors.** Given a common bound `M` on the cutoff
derivative/coefficient expression, the remainder constant depends only on `α`, `M` and `η`.
It is independent of the slab, the particular cutoff and the zeroth-order coefficient. -/
theorem exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le
    (hα : α < 1) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁}
      (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (C : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ))
      (χ : ParabolicC2HolderSpace α E ℝ ht),
      ‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
        (‖B‖ + 2 * ‖A‖) * ‖spatialFDerivHolderL hα.le χ‖ ≤ M →
      ∀ u : ParabolicC2HolderSpace α E ℝ ht,
      ‖parabolicOperatorL hα.le A B C
          ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα.le χ u) -
        (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα.le χ)
          (parabolicOperatorL hα.le A B C u)‖ ≤ η * ‖u‖ + K * ‖valueL u‖ := by
  have hMp : 0 < M + 1 := by positivity
  obtain ⟨K, hK⟩ := exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le
    (E := E) (F := ℝ) hα (div_pos hη hMp)
  refine ⟨(M + 1) * max K 0, by positivity, fun A B C χ hχ u ↦ ?_⟩
  calc
    _ ≤ (M + 1) * (‖valueHolderL hα.le u‖ + ‖spatialFDerivHolderL hα.le u‖) :=
      (norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le hα.le A B C χ u).trans
        (mul_le_mul_of_nonneg_right (hχ.trans (by linarith)) (by positivity))
    _ ≤ (M + 1) * (η / (M + 1) * ‖u‖ + max K 0 * ‖valueL u‖) := by
      exact mul_le_mul_of_nonneg_left ((hK u).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _)))) hMp.le
    _ = _ := by field_simp


/-! ### Localizations by cutoffs -/

section Localizations

variable {χ}

/-- Multiplying by a cutoff with values in `[0, 1]` does not increase the supremum norm. -/
theorem norm_valueL_mul_le (hχ : ∀ p, χ p ∈ Icc 0 1) (u : ParabolicC2HolderSpace α E ℝ ht) :
    ‖valueL ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖ ≤ ‖valueL u‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun p ↦ by
    rw [valueL_apply, ContinuousLinearMap.compParabolicC2Holder₂_apply,
      ContinuousLinearMap.mul_apply', norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ((valueL u).norm_coe_le_norm p)
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ p).1]
    exact (hχ p).2

/-- A localization `χ u` has vanishing trace wherever `u` does. -/
theorem spatialTrace_mul_eq_zero {u : ParabolicC2HolderSpace α E ℝ ht} {t : Icc t₀ t₁}
    (hu : u.spatialTrace t = 0) :
    ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u).spatialTrace t = 0 := by
  ext x
  have hx := congrArg (fun g : CkHolderSpace 2 α E ℝ ↦ g x) hu
  simp only [spatialTrace_apply] at hx
  simp [spatialTrace_apply, hx]

/-- The Hessian of a localization `χ u` vanishes wherever `χ` vanishes near the point. -/
theorem spatialSecondFDerivL_mul_eq_zero {p : slab (E := E) t₀ t₁} {r : ℝ}
    (hχ : ∀ q, r ≤ dist q p → χ q = 0) (u : ParabolicC2HolderSpace α E ℝ ht)
    {q : slab (E := E) t₀ t₁} (hq : r < dist q p) :
    spatialSecondFDerivL ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) q = 0 :=
  spatialSecondFDerivL_eq_zero_of_forall_lt_dist (fun q' hq' ↦ by simp [hχ q' hq'.le]) q hq

end Localizations

end TauCeti.ParabolicC2HolderSpace
