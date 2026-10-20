/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Analysis.Normed.Module.Alternating.Bilinear

/-!
# Smooth differential two-forms on manifolds

The generic smooth differential-form carrier already records the alternating map in each tangent
fibre. This module supplies the degree-two view used by the symplectic API: `SmoothTwoForm` is
the scalar degree-two specialization, and its bilinear, evaluation, and constant-form operations
are derived from `SmoothForm`.

The degree-two specialization supplies the bilinear view used by the symplectic modules while
retaining the generic form's alternating-map and smooth-section structure.

The module also provides the identity linear equivalence `legacySmoothTwoFormEquiv` from
`SmoothTwoForm` to `SmoothForm I M ℝ 2`, its forward and inverse simp laws, and its ordered-pair
evaluation law via `SmoothForm.eval₂`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth real differential two-form is the generic smooth scalar form in degree two. -/
abbrev SmoothTwoForm (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  SmoothForm I M ℝ 2

/-- The identity linear equivalence from `SmoothTwoForm I M` to the generic carrier
`SmoothForm I M ℝ 2`. The chartwise closedness description is given by
`legacySmoothTwoFormEquiv_isClosed_iff`. -/
noncomputable def legacySmoothTwoFormEquiv :
    TauCeti.SmoothTwoForm I M ≃ₗ[ℝ] SmoothForm I M ℝ 2 :=
  LinearEquiv.refl ℝ _

/-- Applying the identity equivalence leaves a degree-two smooth form unchanged. -/
@[simp]
theorem legacySmoothTwoFormEquiv_apply_eq
    (φ : TauCeti.SmoothTwoForm I M) :
    legacySmoothTwoFormEquiv φ = φ :=
  by simp only [legacySmoothTwoFormEquiv, LinearEquiv.refl_apply]

/-- Applying the inverse identity equivalence leaves a degree-two smooth form unchanged. -/
@[simp]
theorem legacySmoothTwoFormEquiv_symm_apply
    (φ : SmoothForm I M ℝ 2) :
    legacySmoothTwoFormEquiv.symm φ = φ :=
  by simp only [legacySmoothTwoFormEquiv, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- Evaluating the identity equivalence on an ordered pair gives the two-form evaluation. -/
theorem legacySmoothTwoFormEquiv_apply
    (φ : TauCeti.SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (legacySmoothTwoFormEquiv φ : RoughForm I M ℝ 2) x ![v, w] = φ.eval₂ x v w := by
  rw [legacySmoothTwoFormEquiv_apply_eq]
  exact (SmoothForm.eval₂_apply φ x v w).symm

namespace SmoothTwoForm

variable {form form' : SmoothTwoForm I M}

/-- A continuous bilinear form defines a constant smooth two-form by antisymmetrization:
`const B` evaluates to `(B v w - B w v) / 2`; when `B` is alternating, this agrees with `B`. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    SmoothTwoForm (modelWithCornersSelf ℝ V) V :=
  SmoothForm.const ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B)

/-- The degree-two constructor is the generic constant form in alternating-map coordinates. -/
theorem const_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    const B = SmoothForm.const
      ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B) := by
  rfl

/-- The tangent-space evaluation of a constant smooth two-form. -/
theorem const_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x : V)
    (v w : TangentSpace (modelWithCornersSelf ℝ V) x) :
    SmoothForm.eval₂ (const B) x v w =
      B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
  rw [const_eq, SmoothForm.eval₂_apply, SmoothForm.const_apply]
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [ContinuousAlternatingMap.alternatizeBilinCLM_apply]
  have hAlt : LinearMap.IsAlt B.toBilinForm := fun z ↦ by
    simpa only [ContinuousLinearMap.toBilinForm_apply] using hB z
  have hneg := LinearMap.IsAlt.neg hAlt
    (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w)
  have hneg' : -B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) =
      B (NormedSpace.fromTangentSpace x w) (NormedSpace.fromTangentSpace x v) := by
    simpa only [ContinuousLinearMap.toBilinForm_apply] using hneg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  rw [← hneg']
  ring

/-- The model-space evaluation of a constant smooth two-form. -/
theorem const_model_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x v w : V) :
    SmoothForm.eval₂ (const B) x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w) = B v w := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (const_apply B hB x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w))


end SmoothTwoForm

end TauCeti

end
