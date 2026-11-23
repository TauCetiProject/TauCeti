/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Comparison

/-!
# Comparison of manifold path integrals with Mathlib's curve integral

This file relates `TauCeti.pathIntegral` and `TauCeti.continuousPathIntegral` on a real normed
space or an open subset of one to Mathlib's `curveIntegral`:

* `TauCeti.pathIntegral_ofSubsingleton_eq_curveIntegral`: `TauCeti.pathIntegral` agrees with
  Mathlib's `curveIntegral` on a real normed space.
* `TauCeti.continuousPathIntegral_ofSubsingleton_eq_curveIntegral` and
  `TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral`: agreement
  of `TauCeti.continuousPathIntegral` with Mathlib's `curveIntegral` on a normed space or an open
  subset of one.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a real normed space `E`, `TauCeti.pathIntegral` of the `1`-form associated to a covector
field `α : E → E →L[ℝ] F` along a curve `c` matching a path `γ` on `[0, 1]` agrees with Mathlib's
`curveIntegral α γ`. -/
theorem pathIntegral_ofSubsingleton_eq_curveIntegral (α : E → E →L[ℝ] F) {c : ℝ → E}
    {a b : E} {γ : Path a b} (hγ : ∀ t : unitInterval, γ t = c t) :
    pathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) c 0 1 =
      curveIntegral α γ := by
  rw [pathIntegral_def (φ := ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1)
      (α p)) : RoughForm 𝓘(ℝ, E) E F 1)), curveIntegral_eq_intervalIntegral_deriv]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_le zero_le_one] at ht
  have heq : γ.extend =ᶠ[𝓝 t] c := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    rw [Path.extend_apply γ hs', hγ ⟨s, hs'⟩]
  have hv : Manifold.curveVelocity 𝓘(ℝ, E) c t = deriv γ.extend t := by
    rw [Manifold.curveVelocity_eq_deriv, heq.deriv_eq]
  rw [hv, heq.eq_of_nhds]
  exact ContinuousAlternatingMap.ofSubsingleton_apply_apply (f := α (c t)) (i := (0 : Fin 1))
    (x := fun _ : Fin 1 ↦ deriv γ.extend t)

/-- On a real normed space `E`, for a continuous covector field `α : E → E →L[ℝ] F` with local
primitives and complete coefficients, `continuousPathIntegral` along a path following a `C¹` curve
agrees with Mathlib's `curveIntegral α γ`. -/
theorem continuousPathIntegral_ofSubsingleton_eq_curveIntegral [CompleteSpace F]
    {α : E → E →L[ℝ] F} (hα : Continuous α)
    (hφ : ∀ p : E, ∃ (g : E → F) (U : Set E), p ∈ U ∧
      IsPrimitiveOn (I := 𝓘(ℝ, E))
        ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
          RoughForm 𝓘(ℝ, E) E F 1) g U)
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) {a b : E} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) γ =
      curveIntegral α γ := by
  let ψ : RoughForm 𝓘(ℝ, E) E F 1 :=
    fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)
  have hsmooth : IsSmoothForm 𝓘(ℝ, E) 0 ψ :=
    (isSmoothForm_modelSpace_iff (φ := ψ)).mpr <| contDiff_zero.mpr <|
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
        (0 : Fin 1)).continuous.comp hα
  exact (continuousPathIntegral_eq_pathIntegral hφ hsmooth hc.contMDiff hγ).trans
    (pathIntegral_ofSubsingleton_eq_curveIntegral α hγ)

/-- On an open submanifold `U : TopologicalSpace.Opens E` of a real normed space, for a covector
field `α : E → E →L[ℝ] F` continuous on `U` with local primitives on `U` and complete coefficients,
`continuousPathIntegral` along a path `γ` in `U` following a `C¹` curve agrees with Mathlib's
`curveIntegral α (γ.map continuous_subtypeVal)`. -/
theorem continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral
    [CompleteSpace F] {U : TopologicalSpace.Opens E} {α : E → E →L[ℝ] F}
    (hα : ContinuousOn α U)
    (hφ : ∀ p : U, ∃ (g : U → F) (V : Set U), p ∈ V ∧
      IsPrimitiveOn
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
            RoughForm 𝓘(ℝ, E) E F 1)) g V)
    {c : ℝ → U} (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c) {a b : U} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
            RoughForm 𝓘(ℝ, E) E F 1)) γ =
      curveIntegral α (γ.map continuous_subtypeVal) := by
  let ψ : RoughForm 𝓘(ℝ, E) E F 1 :=
    fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)
  have hsmooth : IsSmoothForm 𝓘(ℝ, E) 0 (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) ψ) := by
    rw [isSmoothForm_def]
    intro p
    have hψp : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) 0
        (fun q ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) q (ψ q)) (p : E) := by
      refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
      rw [RoughForm.inChartAt_modelSpace]
      have hcont : ContinuousOn (fun q : E ↦
          ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) (U : Set E) :=
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
          (0 : Fin 1)).continuous.comp_continuousOn hα
      exact (contDiffAt_zero.mpr ⟨U, U.isOpen.mem_nhds p.property, hcont⟩).contDiffWithinAt
    exact hψp.mpullback_form (contMDiff_subtypeVal (n := 1) p) le_rfl
  rw [continuousPathIntegral_eq_pathIntegral hφ hsmooth hc hγ,
    pathIntegral_mpullback ψ (fun _ _ ↦ contMDiff_subtypeVal.mdifferentiable one_ne_zero _)
      (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero),
    pathIntegral_ofSubsingleton_eq_curveIntegral α (c := Subtype.val ∘ c)
      (γ := γ.map continuous_subtypeVal) (fun t ↦ congrArg Subtype.val (hγ t))]

end TauCeti
