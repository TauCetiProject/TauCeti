/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The derivative of the flow of an adapted pseudo-gradient in a Morse chart

Let `X` be a pseudo-gradient adapted to `f`, and `φ` a Morse chart at a critical point in which
`X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. While the linear orbit `t ↦ (e^{-wᵢ t} zᵢ)ᵢ` of the
coordinates `z` of a point stays in the chart, the flow of `X` is this linear flow
(`TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc`). This file
differentiates that statement: the derivative of the time-`s` map of the flow, read in the chart
at both ends, is the diagonal map `v ↦ (e^{-wᵢ s} vᵢ)ᵢ` in the coordinates of `φ`
(`TauCeti.IsAdaptedPseudoGradient.coord_mfderiv_toChart_comp_flow`).

Since all weights are `±1`, the diagonal map multiplies every coordinate of negative weight by the
same factor `e^{s}` and every coordinate of positive weight by `e^{-s}`. This is what makes
orientations of the coordinate subspaces of a Morse chart transportable along the flow: a positive
multiple of the identity preserves every orientation.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.coord_mfderiv_toChart_comp_flow`: in a Morse chart in which `X`
  is linear, the derivative of the flow is the linear flow of the coordinates of tangent vectors.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The linear flow of a Morse chart at a fixed time, as a continuous linear map of the model,
read in the coordinates of the chart. -/
private noncomputable def linearFlowCLM (s : ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap ((φ.coord.symm : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E) ∘ₗ
    (LinearMap.pi fun i ↦ Real.exp (-(φ.weight i * s)) • LinearMap.proj i) ∘ₗ
      (φ.coord : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
private theorem linearFlowCLM_apply (s : ℝ) (v : E) :
    φ.linearFlowCLM s v = φ.coord.symm (φ.linearFlow s (φ.coord v)) := by
  simp only [linearFlowCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply]
  congr 1
  funext i
  simp

end MorseChart

namespace IsAdaptedPseudoGradient

/-- **The derivative of the flow in a Morse chart.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and let `z` be a point of the chart whose linear orbit
stays in the chart for all times between `0` and `s`. Then the derivative at `z` of the time-`s`
map of the flow, followed by the chart, sends a tangent vector with coordinates `v` to the vector
with coordinates `(e^{-wᵢ s} vᵢ)ᵢ`. -/
theorem coord_mfderiv_toChart_comp_flow (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : M} (hz : z ∈ φ.toChart.source) {s : ℝ}
    (hs : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart z))) ∈
      φ.toChart.target)
    (v : TangentSpace 𝓘(ℝ, E) z) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow s) z v) =
      φ.linearFlow s (φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v)) := by
  -- The linear orbits of all coordinates near those of `z` stay in the chart up to time `s`.
  have hcont : Continuous fun p : (Fin (Module.finrank ℝ E) → ℝ) × ℝ ↦
      φ.coord.symm (φ.linearFlow p.2 p.1) :=
    (LinearMap.continuous_of_finiteDimensional (φ.coord.symm :
      (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)).comp φ.continuous_linearFlow_uncurry
  have hnear : ∀ᶠ c in 𝓝 (φ.coord (φ.toChart z)), ∀ t ∈ uIcc 0 s,
      φ.coord.symm (φ.linearFlow t c) ∈ φ.toChart.target :=
    isCompact_uIcc.eventually_forall_of_forall_eventually fun t ht ↦
      hcont.continuousAt.preimage_mem_nhds (φ.toChart.open_target.mem_nhds (hs t ht))
  have hcoord : ContinuousAt (fun w ↦ φ.coord (φ.toChart w)) z :=
    φ.continuous_coord.continuousAt.comp (φ.toChart.continuousAt hz)
  -- Near `z`, the chart followed by the flow is the linear flow in coordinates.
  have heq : φ.toChart ∘ hX.flow s =ᶠ[𝓝 z] φ.linearFlowCLM s ∘ φ.toChart := by
    filter_upwards [hcoord.eventually hnear, φ.toChart.open_source.mem_nhds hz] with w hw hws
    have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hw
    rw [φ.toChart_symm_coord_symm_coord hws] at hflow
    rw [comp_apply, comp_apply, hflow, φ.toChart.right_inv (hw s right_mem_uIcc),
      φ.linearFlowCLM_apply]
  have hmf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow s) z v =
      φ.linearFlowCLM s (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v) := by
    rw [heq.mfderiv_eq, mfderiv_comp z (φ.linearFlowCLM s).mdifferentiableAt
      (φ.mdifferentiableAt_toChart hz), (φ.linearFlowCLM s).mfderiv_eq]
    -- `EventuallyEq.mfderiv_eq` composes with `tangentSpaceCast`, the identity map between the
    -- tangent spaces at the two (equal) image points.
    rfl
  rw [hmf]
  exact (congrArg φ.coord (φ.linearFlowCLM_apply s _)).trans (φ.coord.apply_symm_apply _)

end IsAdaptedPseudoGradient

end TauCeti
