/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Comparison

/-!
# Comparison of manifold path integrals with `TauCeti.potentialIntegral` and `curveIntegral`

This file relates `TauCeti.pathIntegral` and `TauCeti.continuousPathIntegral` on a real normed
space or an open subset of one to `TauCeti.potentialIntegral` and Mathlib's `curveIntegral`:

* `TauCeti.pathIntegral_ofSubsingleton_eq_curveIntegral`: `TauCeti.pathIntegral` agrees with
  Mathlib's `curveIntegral` on a real normed space.
* `TauCeti.continuousPathIntegral_ofSubsingleton_eq_potentialIntegral` and
  `TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral`
  (with their `TauCeti.HasLocalPotentials` corollaries): `TauCeti.continuousPathIntegral` agrees
  with `TauCeti.potentialIntegral` on a real normed space or an open subset of one.
* `TauCeti.potentialIntegral_eq_curveIntegral` and
  `TauCeti.HasLocalPotentials.potentialIntegral_eq_curveIntegral`: `TauCeti.potentialIntegral`
  along a path following a `C¹` curve agrees with Mathlib's `curveIntegral`.
* `TauCeti.continuousPathIntegral_ofSubsingleton_eq_curveIntegral` and
  `TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral`: agreement
  of `TauCeti.continuousPathIntegral` with Mathlib's `curveIntegral` on a normed space or an open
  subset of one, derived via `TauCeti.potentialIntegral`.
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

private theorem continuousPathIntegral_eq_potentialIntegral_of_lift
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {θ : RoughForm 𝓘(ℝ, E) M F 1} (hθ : HasLocalPrimitives θ)
    {f : M → E} (hf : Continuous f) {α : E → E →L[ℝ] F} {a b : M} (γ : Path a b)
    (hloc : ∀ {g : M → F} {V : Set M} {x : M}, x ∈ V → IsPrimitiveOn θ g V →
      ∃ (g' : E → F), (∀ᶠ y in 𝓝 (f x), HasFDerivAt g' (α y) y) ∧
        ∀ᶠ y in 𝓝 x, g' (f y) = g y) :
    continuousPathIntegral θ γ = potentialIntegral α (γ.map hf) := by
  have hp := hθ.isCoveringMap_proj
  let Γ := hp.liftPath γ.toContinuousMap (PrimitiveSpace.graph θ 0 a)
    (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph])
  have hΓγ (t : unitInterval) : PrimitiveSpace.proj θ (Γ t) = γ t :=
    congrFun (hp.liftPath_lifts _ _ _) t
  have hprim : IsPrimitiveAlong α (γ.map hf) (fun t ↦ PrimitiveSpace.value θ (Γ t)) := by
    rw [isPrimitiveAlong_iff]
    intro t₀
    rw [isPrimitiveAlongAt_iff]
    obtain ⟨g, V, hxV, hgV, c, hc⟩ :=
      hθ.exists_isPrimitiveOn_eventually_value_eq (Γ.continuous.continuousAt (x := t₀))
    obtain ⟨g', hd', hfg'⟩ := hloc (hΓγ t₀ ▸ hxV) hgV
    refine ⟨g', hd', ?_⟩
    have h0 := hc.self_of_nhds
    have hfg_t : ∀ᶠ s in 𝓝 t₀, g' (f (γ s)) = g (γ s) :=
      (γ.continuous.continuousAt (x := t₀)).eventually hfg'
    have hfg0 := hfg_t.self_of_nhds
    filter_upwards [hc, hfg_t] with s hs hfg_s
    simp only [Path.map_coe, Function.comp_apply]
    rw [hfg_s, hfg0, hs.2, h0.2, hΓγ, hΓγ]
    abel
  rw [continuousPathIntegral_eq_sub_of_lift hθ Γ.continuous hΓγ, hprim.potentialIntegral_eq]

/-- On a real normed space `E`, `continuousPathIntegral` of the `1`-form associated to a covector
field `α : E → E →L[ℝ] F` with local primitives agrees with `TauCeti.potentialIntegral α γ`. -/
theorem continuousPathIntegral_ofSubsingleton_eq_potentialIntegral {α : E → E →L[ℝ] F}
    (hφ : HasLocalPrimitives (I := 𝓘(ℝ, E))
      ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
        RoughForm 𝓘(ℝ, E) E F 1))
    {a b : E} (γ : Path a b) :
    continuousPathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) γ =
      potentialIntegral α γ := by
  have h := continuousPathIntegral_eq_potentialIntegral_of_lift hφ continuous_id γ
    (α := α) fun hxV hgV ↦
      let ⟨hV, hd⟩ := isPrimitiveOn_ofSubsingleton_iff.mp hgV
      ⟨_, eventually_of_mem (hV.mem_nhds hxV) hd, Eventually.of_forall fun _ ↦ rfl⟩
  simpa using h

/-- For a covector field `α : E → E →L[ℝ] F` with `HasLocalPotentials univ α`,
`continuousPathIntegral` agrees with `TauCeti.potentialIntegral α γ`. -/
theorem HasLocalPotentials.continuousPathIntegral_ofSubsingleton_eq_potentialIntegral
    {α : E → E →L[ℝ] F} (hα : HasLocalPotentials univ α) {a b : E} (γ : Path a b) :
    continuousPathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) γ =
      potentialIntegral α γ :=
  TauCeti.continuousPathIntegral_ofSubsingleton_eq_potentialIntegral hα.hasLocalPrimitives γ

/-- On an open submanifold `U : TopologicalSpace.Opens E` of a real normed space,
`continuousPathIntegral` of the restriction of `α : E → E →L[ℝ] F` along a path `γ` in `U`
agrees with `TauCeti.potentialIntegral α (γ.map continuous_subtypeVal)`. -/
theorem continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral
    {U : TopologicalSpace.Opens E} {α : E → E →L[ℝ] F}
    (hφ : HasLocalPrimitives
      (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
        ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
          RoughForm 𝓘(ℝ, E) E F 1)))
    {a b : U} (γ : Path a b) :
    continuousPathIntegral
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
            RoughForm 𝓘(ℝ, E) E F 1)) γ =
      potentialIntegral α (γ.map continuous_subtypeVal) :=
  continuousPathIntegral_eq_potentialIntegral_of_lift hφ continuous_subtypeVal γ fun {g _ x} hxV
      hgV ↦
    let hV_ext := isPrimitiveOn_ofSubsingleton_iff.mp hgV.of_mpullback_subtypeVal
    ⟨Function.extend Subtype.val g 0,
      eventually_of_mem (hV_ext.1.mem_nhds ⟨x, hxV, rfl⟩) hV_ext.2,
      Eventually.of_forall fun y ↦ Subtype.val_injective.extend_apply g 0 y⟩

namespace HasLocalPotentials

/-- On an open submanifold `U : TopologicalSpace.Opens E`, for a covector field `α : E → E →L[ℝ] F`
with `HasLocalPotentials (U : Set E) α`, `continuousPathIntegral` of its restriction along a path
`γ` in `U` agrees with `TauCeti.potentialIntegral α (γ.map continuous_subtypeVal)`. -/
theorem continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral
    {U : TopologicalSpace.Opens E} {α : E → E →L[ℝ] F}
    (hα : HasLocalPotentials (U : Set E) α) {a b : U} (γ : Path a b) :
    continuousPathIntegral
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
            RoughForm 𝓘(ℝ, E) E F 1)) γ =
      potentialIntegral α (γ.map continuous_subtypeVal) :=
  TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral
    ((hasLocalPrimitives_mpullback_subtypeVal_iff (U := U) _).mpr hα.hasLocalPrimitivesOn) γ

end HasLocalPotentials

/-- On an open set `U ⊆ E`, for a covector field `α : E → E →L[ℝ] F` continuous on `U` with local
primitives on `U` and complete coefficients, `TauCeti.potentialIntegral` along a path `γ` following
a `C¹` curve `c` in `U` agrees with Mathlib's `curveIntegral α γ`. -/
theorem potentialIntegral_eq_curveIntegral [CompleteSpace F]
    {U : Set E} (hU : IsOpen U) {α : E → E →L[ℝ] F} (hα : ContinuousOn α U)
    (hφ : HasLocalPrimitivesOn (I := 𝓘(ℝ, E))
      ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
        RoughForm 𝓘(ℝ, E) E F 1) U)
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) (hcU : ∀ t, c t ∈ U)
    {a b : E} {γ : Path a b} (hγ : ∀ t : unitInterval, γ t = c t) :
    potentialIntegral α γ = curveIntegral α γ := by
  let U' : TopologicalSpace.Opens E := ⟨U, hU⟩
  let ψ : RoughForm 𝓘(ℝ, E) E F 1 :=
    fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)
  let cU : ℝ → U' := fun t ↦ ⟨c t, hcU t⟩
  have hcU_mdiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 cU := fun t ↦
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff cU univ t).mp (hc.contMDiff t)
  have hγU (t : unitInterval) : γ t ∈ U := hγ t ▸ hcU t
  let γU : Path (⟨a, by rw [← γ.source, hγ 0]; exact hcU 0⟩ : U')
      ⟨b, by rw [← γ.target, hγ 1]; exact hcU 1⟩ :=
    { toFun := fun t ↦ ⟨γ t, hγU t⟩
      continuous_toFun := γ.continuous.subtype_mk hγU
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have hγU_eq : γU.map continuous_subtypeVal = γ := Path.ext rfl
  have hφ' : HasLocalPrimitives (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U' → E) ψ) :=
    (hasLocalPrimitives_mpullback_subtypeVal_iff (U := U') ψ).mpr hφ
  have hsmooth : IsSmoothForm 𝓘(ℝ, E) 0
      (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U' → E) ψ) := by
    rw [isSmoothForm_def]
    intro p
    have hψp : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) 0
        (fun q ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) q (ψ q)) (p : E) := by
      refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
      rw [RoughForm.inChartAt_modelSpace]
      have hcont : ContinuousOn (fun q : E ↦
          ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) (U' : Set E) :=
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
          (0 : Fin 1)).continuous.comp_continuousOn hα
      exact (contDiffAt_zero.mpr ⟨U', U'.isOpen.mem_nhds p.property, hcont⟩).contDiffWithinAt
    exact hψp.mpullback_form (contMDiff_subtypeVal (n := 1) p) le_rfl
  rw [← hγU_eq,
    ← continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral hφ' γU,
    continuousPathIntegral_eq_pathIntegral hφ' hsmooth hcU_mdiff
      (fun t ↦ Subtype.ext (hγ t)),
    pathIntegral_mpullback ψ (fun _ _ ↦ contMDiff_subtypeVal.mdifferentiable one_ne_zero _)
      (fun t _ ↦ (hcU_mdiff t).mdifferentiableAt one_ne_zero),
    pathIntegral_ofSubsingleton_eq_curveIntegral α (c := Subtype.val ∘ cU)
      (γ := γU.map continuous_subtypeVal) (fun t ↦ hγ t)]

/-- For a covector field `α : E → E →L[ℝ] F` with `HasLocalPotentials U α` and complete
coefficients, `TauCeti.potentialIntegral` along a path `γ` following a `C¹` curve `c` in `U` agrees
with Mathlib's `curveIntegral α γ`. -/
theorem HasLocalPotentials.potentialIntegral_eq_curveIntegral [CompleteSpace F]
    {U : Set E} {α : E → E →L[ℝ] F} (hα : HasLocalPotentials U α)
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) (hcU : ∀ t, c t ∈ U)
    {a b : E} {γ : Path a b} (hγ : ∀ t : unitInterval, γ t = c t) :
    potentialIntegral α γ = curveIntegral α γ :=
  TauCeti.potentialIntegral_eq_curveIntegral hα.isOpen hα.continuousOn
    hα.hasLocalPrimitivesOn hc hcU hγ

/-- On a real normed space `E`, for a continuous covector field `α : E → E →L[ℝ] F` with local
primitives and complete coefficients, `continuousPathIntegral` along a path following a `C¹` curve
agrees with Mathlib's `curveIntegral α γ`. -/
theorem continuousPathIntegral_ofSubsingleton_eq_curveIntegral [CompleteSpace F]
    {α : E → E →L[ℝ] F} (hα : Continuous α)
    (hφ : HasLocalPrimitives (I := 𝓘(ℝ, E))
      ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
        RoughForm 𝓘(ℝ, E) E F 1))
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) {a b : E} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) γ =
      curveIntegral α γ := by
  rw [continuousPathIntegral_ofSubsingleton_eq_potentialIntegral hφ γ]
  exact potentialIntegral_eq_curveIntegral isOpen_univ hα.continuousOn
    (hφ.hasLocalPrimitivesOn univ) hc (fun _ ↦ mem_univ _) hγ

/-- On an open submanifold `U : TopologicalSpace.Opens E` of a real normed space, for a covector
field `α : E → E →L[ℝ] F` continuous on `U` with local primitives on `U` and complete coefficients,
`continuousPathIntegral` along a path `γ` in `U` following a `C¹` curve agrees with Mathlib's
`curveIntegral α (γ.map continuous_subtypeVal)`. -/
theorem continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral
    [CompleteSpace F] {U : TopologicalSpace.Opens E} {α : E → E →L[ℝ] F}
    (hα : ContinuousOn α U)
    (hφ : HasLocalPrimitives
      (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
        ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
          RoughForm 𝓘(ℝ, E) E F 1)))
    {c : ℝ → U} (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c) {a b : U} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
            RoughForm 𝓘(ℝ, E) E F 1)) γ =
      curveIntegral α (γ.map continuous_subtypeVal) := by
  rw [continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_potentialIntegral hφ γ]
  exact potentialIntegral_eq_curveIntegral U.isOpen hα
    ((hasLocalPrimitives_mpullback_subtypeVal_iff (U := U) _).mp hφ)
    (contMDiff_iff_contDiff.mp (contMDiff_subtypeVal.comp hc))
    (fun t ↦ (c t).property) (fun t ↦ congrArg Subtype.val (hγ t))

end TauCeti
