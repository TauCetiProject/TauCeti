/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge

/-!
# The paired wedge as a continuous trilinear map

The paired wedge depends continuously and linearly on each of its three inputs: the bilinear
pairing and the two alternating maps. `wedgeWithCLM` bundles this dependence, with the binomial
operator-norm bound. This permits applying the usual calculus of continuous linear maps to
families of forms, including pairings that vary with the base point.

The construction uses `TauCeti.wedgeWith` and its norm bound, together with Mathlib's
`LinearMap.mkContinuous₂`. The normalization follows John M. Lee, *Introduction to Smooth
Manifolds*, second edition, Chapter 14.
-/

public section

noncomputable section

namespace TauCeti

variable {E F₁ F₂ F₃ : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃] {k l : ℕ}

/-- The paired wedge, bundled as a continuous linear map in the pairing with values in
continuous bilinear maps of alternating maps. -/
def wedgeWithCLM : (F₁ →L[ℝ] F₂ →L[ℝ] F₃) →L[ℝ]
    (E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
      E [⋀^Fin (k + l)]→L[ℝ] F₃ := by
  -- Cache the canonical inner operator-space instances to keep typeclass synthesis shallow.
  letI : SeminormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  letI : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  letI : SeminormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  letI : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let B (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
      (E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃ :=
    (LinearMap.mk₂ ℝ (wedgeWith μ)
      (wedgeWith_add_left μ) (wedgeWith_smul_left μ)
      (wedgeWith_add_right μ) (wedgeWith_smul_right μ)).mkContinuous₂
        ((k + l).choose k * ‖μ‖) (norm_wedgeWith_le μ)
  have hB (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
      (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
      B μ φ ψ = wedgeWith μ φ ψ := rfl
  have hnorm (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
      ‖B μ‖ ≤ (k + l).choose k * ‖μ‖ :=
    LinearMap.mkContinuous₂_norm_le _ (by positivity) _
  exact LinearMap.mkContinuous
    { toFun := B
      map_add' := fun μ ν ↦ by
        apply ContinuousLinearMap.ext
        intro φ
        apply ContinuousLinearMap.ext
        intro ψ
        simpa only [hB, add_apply] using
          wedgeWith_add_pairing μ ν φ ψ
      map_smul' := fun c μ ↦ by
        apply ContinuousLinearMap.ext
        intro φ
        apply ContinuousLinearMap.ext
        intro ψ
        simpa only [hB, smul_apply, RingHom.id_apply] using wedgeWith_smul_pairing c μ φ ψ }
    ((k + l).choose k) hnorm

/-- Evaluation of the bundled paired wedge recovers `wedgeWith`. -/
@[simp] theorem wedgeWithCLM_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWithCLM μ φ ψ = wedgeWith μ φ ψ := (rfl)

/-- The operator norm of the bundled paired wedge is bounded by the binomial coefficient. -/
theorem norm_wedgeWithCLM_le :
    @norm _ (by
      let : SeminormedAddCommGroup
          ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
      let : NormedSpace ℝ
          ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
      let : SeminormedAddCommGroup
          ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
            E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
      let : NormedSpace ℝ
          ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
            E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
      let : SeminormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
      let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
      infer_instance)
      (wedgeWithCLM (E := E) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (k := k) (l := l)) ≤
      (k + l).choose k := by
  let : SeminormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : SeminormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : SeminormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro μ
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro φ ψ
  simpa only [wedgeWithCLM_apply] using norm_wedgeWith_le μ φ ψ

end TauCeti
