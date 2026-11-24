/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path

/-!
# Comparison of continuous and smooth path integrals

This file relates `TauCeti.continuousPathIntegral` (defined for `1`-forms with local primitives
along arbitrary continuous paths) to `TauCeti.pathIntegral` (for `1`-forms along `C¹` curves):

* `TauCeti.continuousPathIntegral_eq_pathIntegral`: when `F` is complete and `φ` is continuous,
  `TauCeti.continuousPathIntegral` along a continuous path following a `C¹` curve agrees with
  `TauCeti.pathIntegral`.

Comparison with Mathlib's `curveIntegral` on real normed spaces and open subsets lives in
`TauCeti.Geometry.Manifold.DifferentialForm.Integration.CurveIntegral`.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Comparison with smooth path integrals.** For a continuous `1`-form `φ` with local primitives
and complete coefficients `F`, the continuous path integral along a path `γ` following a `C¹` curve
`c` agrees with `TauCeti.pathIntegral φ c 0 1`. -/
theorem continuousPathIntegral_eq_pathIntegral [IsManifold I 1 M] [CompleteSpace F]
    {φ : RoughForm I M F 1} (hφ : HasLocalPrimitives φ)
    (hφ₀ : IsSmoothForm I 0 φ) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    {x y : M} {γ : Path x y} (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral φ γ = pathIntegral φ c 0 1 := by
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ :=
    PrimitiveSpace.continuous_graph_of_forall_exists_isPrimitiveOn_eventuallyEq γ.continuous
      fun t₀ ↦ by
        obtain ⟨g, U, hxU, hgU⟩ := hφ (c t₀)
        obtain ⟨δ, hδ, hball⟩ :=
          Metric.isOpen_iff.mp (hgU.isOpen.preimage hc.continuous) (t₀ : ℝ) hxU
        refine ⟨g, U, by simpa only [hγ] using hxU, hgU, pathIntegral φ c 0 t₀ - g (c t₀), ?_⟩
        filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
          (Metric.ball_mem_nhds (t₀ : ℝ) hδ)] with s hs
        have hsub : uIcc (t₀ : ℝ) s ⊆ c ⁻¹' U := by
          refine (Set.OrdConnected.uIcc_subset ?_ (Metric.mem_ball_self (x := (t₀ : ℝ)) hδ)
            hs).trans hball
          rw [Real.ball_eq_Ioo]
          exact ordConnected_Ioo
        simp only [hγ]
        rw [← pathIntegral_add_adjacent (hint 0 t₀) (hint t₀ s),
          pathIntegral_eq_sub_of_isPrimitiveOn hgU (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero)
            (fun t ht ↦ hsub ht) (hint t₀ s)]
        abel
  rw [continuousPathIntegral_eq_sub_of_lift hφ hΓ (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp [Γ]

end TauCeti
