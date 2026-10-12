/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Regularity of integral curves on parameter sets

An integral curve of a continuously differentiable vector field is twice continuously
differentiable within any parameter set with unique derivatives. This includes nondegenerate
closed intervals: no extension of the curve beyond its endpoints is assumed.

In coordinates the first derivative is the vector field evaluated along the curve. Its
continuity first gives `C¹` regularity, and composition with the `C¹` field then gives `C²`
regularity. Applied to the geodesic spray, this removes the separate regularity assumption
on the projected curve in the spray characterization of geodesics.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [BoundarylessManifold I M] [IsManifold I 2 M]

/-- An integral curve of a `C¹` vector field is `C²` within a parameter set with unique
derivatives, including the endpoints of a nondegenerate closed interval. -/
theorem contMDiffOn_two_of_isMIntegralCurveOn {γ : ℝ → M}
    {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hγ : IsMIntegralCurveOn γ v s)
    (hv : ∀ t ∈ s,
      ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s := by
  intro t₀ ht₀
  rw [contMDiffWithinAt_iff_target]
  refine ⟨(hγ t₀ ht₀).continuousWithinAt, ?_⟩
  -- Read the equation in the chart at the current value and restrict to its source.
  let c : ℝ → E := extChartAt I (γ t₀) ∘ γ
  let w : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀)
      ((extChartAt I (γ t₀)).symm x) (v ((extChartAt I (γ t₀)).symm x))
  have hw : ContDiffAt ℝ 1 w (extChartAt I (γ t₀) (γ t₀)) := by
    have h := hv t₀ ht₀
    rw [contMDiffAt_iff] at h
    exact (h.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨u, hu, hwu⟩ := hw.contDiffOn le_rfl (by simp)
  have hcsrc : ∀ᶠ t in 𝓝[s] t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    (hγ t₀ ht₀).continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I) _)
  have hcu : ∀ᶠ t in 𝓝[s] t₀, c t ∈ u :=
    ((continuousAt_extChartAt (γ t₀)).comp_continuousWithinAt
      (hγ t₀ ht₀).continuousWithinAt).eventually hu
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (hcsrc.and hcu)
  obtain ⟨V, hVU, hVopen, htV⟩ := mem_nhds_iff.mp hU
  let r := s ∩ V
  have hr : UniqueDiffOn ℝ r := hs.inter hVopen
  have hsrc (t : ℝ) (ht : t ∈ r) : γ t ∈ (extChartAt I (γ t₀)).source :=
    (hUs ⟨hVU ht.2, ht.1⟩).1
  have hmaps : MapsTo c r u := fun t ht ↦ (hUs ⟨hVU ht.2, ht.1⟩).2
  have hd (t : ℝ) (ht : t ∈ r) : HasDerivWithinAt c (w (c t)) r t := by
    have h := hasDerivWithinAt_comp_curve (s := r)
      (mdifferentiableAt_extChartAt (I := I) (extChartAt_source I (γ t₀) ▸ hsrc t ht))
      ((hγ t ht.1).mono inter_subset_left)
    convert h using 1
    simp only [w, c, Function.comp_apply, mvfderiv]
    rw [(extChartAt I (γ t₀)).left_inv (hsrc t ht),
      (hasMFDerivAt_extChartAt (I := I)
        (extChartAt_source I (γ t₀) ▸ hsrc t ht)).mfderiv,
      mfderiv_chartAt_eq_tangentCoordChange (extChartAt_source I (γ t₀) ▸ hsrc t ht)]
    rfl
  -- The continuous coordinate field gives C¹ regularity, then composition gives C².
  have hc1 : ContDiffOn ℝ 1 c r := by
    rw [contDiffOn_one_iff_derivWithin hr]
    refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, ?_⟩
    exact (hwu.continuousOn.comp (fun t ht ↦ (hd t ht).continuousWithinAt) hmaps).congr
      fun t ht ↦ (hd t ht).derivWithin (hr t ht)
  have hc2 : ContDiffOn ℝ 2 c r := by
    have htwo : (2 : ℕ∞ω) = 1 + 1 := by norm_num
    rw [htwo, contDiffOn_succ_iff_derivWithin hr]
    exact ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp,
      (hwu.comp hc1 hmaps).congr fun t ht ↦ (hd t ht).derivWithin (hr t ht)⟩
  have hc2t := hc2 t₀ ⟨ht₀, htV⟩
  rw [contDiffWithinAt_inter (hVopen.mem_nhds htV)] at hc2t
  exact hc2t.contMDiffWithinAt

end TauCeti.Manifold
