/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Comparison of continuous path integrals, smooth path integrals, and curve integrals

This file relates `TauCeti.continuousPathIntegral` (defined for `1`-forms with local primitives
along arbitrary continuous paths) to `TauCeti.pathIntegral` (for `1`-forms along `C¹` curves) and
Mathlib's `curveIntegral` (for covector fields on a real normed space):

* `TauCeti.pathIntegral_ofSubsingleton_eq_curveIntegral`: `TauCeti.pathIntegral` agrees with
  Mathlib's `curveIntegral` on a real normed space.
* `TauCeti.pathIntegral_eq_sub_of_isPrimitiveOn`: local fundamental theorem of calculus for
  `TauCeti.pathIntegral` along differentiable curves inside a primitive domain.
* `TauCeti.continuousPathIntegral_eq_pathIntegral`: when `F` is complete and `φ` is continuous,
  `TauCeti.continuousPathIntegral` along a continuous path following a `C¹` curve agrees with
  `TauCeti.pathIntegral`.
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

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
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

/-- **Local fundamental theorem of calculus for `IsPrimitiveOn`.** If `g` is a primitive of `φ` on
an open set `U` containing the curve `c` on `uIcc a b`, `c` is differentiable at every point of
`uIcc a b`, and the integrand is interval integrable, then
`pathIntegral φ c a b = g (c b) - g (c a)`. No `C¹` regularity of `g` or `c` is needed. -/
theorem pathIntegral_eq_sub_of_isPrimitiveOn [CompleteSpace F]
    {φ : RoughForm I M F 1} {g : M → F} {U : Set M} (hgU : IsPrimitiveOn φ g U)
    {c : ℝ → M} {a b : ℝ} (hc : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hcU : ∀ t ∈ uIcc a b, c t ∈ U)
    (hint : IntervalIntegrable (fun t ↦ φ (c t) fun _ ↦ Manifold.curveVelocity I c t)
      volume a b) :
    pathIntegral φ c a b = g (c b) - g (c a) := by
  rw [pathIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g ∘ c) (fun t ht ↦ ?_) hint
  have hgt := (hgU.mdifferentiableOn (c t) (hcU t ht)).mdifferentiableAt
    (hgU.isOpen.mem_nhds (hcU t ht))
  have hd : HasDerivAt (g ∘ c) (mextDeriv (RoughForm.ofFunction I g) (c t)
      fun _ ↦ Manifold.curveVelocity I c t) t := by
    rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
    exact Manifold.hasDerivAt_comp_curve hgt (Manifold.hasMFDerivAt_curveVelocity (hc t ht))
  rwa [hgU.mextDeriv_eq (c t) (hcU t ht)] at hd

/-- **Comparison with smooth path integrals.** For a continuous `1`-form `φ` with local primitives
and complete coefficients `F`, the continuous path integral along a path `γ` following a `C¹` curve
`c` agrees with `TauCeti.pathIntegral φ c 0 1`. -/
theorem continuousPathIntegral_eq_pathIntegral [IsManifold I 1 M] [CompleteSpace F]
    {φ : RoughForm I M F 1}
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hφ₀ : IsSmoothForm I 0 φ) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    {x y : M} {γ : Path x y} (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral φ γ = pathIntegral φ c 0 1 := by
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU⟩ := hφ (c t₀)
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp (hgU.isOpen.preimage hc.continuous) (t₀ : ℝ) hxU
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Γ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (hgU.add_const (pathIntegral φ c 0 t₀ - g (c t₀)))
      (by simp only [Γ, PrimitiveSpace.proj_graph, hγ]; exact hxU) ?_
    filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (t₀ : ℝ) hδ)] with s hs
    have hsub : uIcc (t₀ : ℝ) s ⊆ c ⁻¹' U := by
      refine (Set.OrdConnected.uIcc_subset ?_ (Metric.mem_ball_self (x := (t₀ : ℝ)) hδ) hs).trans
        hball
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Γ, hγ]
    rw [← pathIntegral_add_adjacent (hint 0 t₀) (hint t₀ s),
      pathIntegral_eq_sub_of_isPrimitiveOn hgU (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero)
        (fun t ht ↦ hsub ht) (hint t₀ s)]
    abel
  rw [continuousPathIntegral_eq_sub_of_lift hφ hΓ (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp [Γ]

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
