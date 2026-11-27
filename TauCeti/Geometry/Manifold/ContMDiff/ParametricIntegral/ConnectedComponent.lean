/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.Topology

/-!
# Integrals over connected components depending on a parameter

Let `M` be a manifold whose connected components are compact, for instance a compact manifold,
with a measure `μ` finite on compact sets, and let `F : M × P → V` be a `C^n` function of a point
of `M` and a parameter in a boundaryless manifold `P`. This file shows that integrating `F` over
the connected component of the point,

`(x, p) ↦ ∫ y in M_x, F (y, p) ∂μ`, where `M_x` is the connected component of `x`,

is again `C^n` (`ContMDiff.setIntegral_connectedComponent`), and so is the average
`(x, p) ↦ ⨍ y in M_x, F (y, p) ∂μ` (`ContMDiff.setAverage_connectedComponent`). In the point the
function is locally constant, since the connected components of a manifold are open; in the
parameter it is an integral over a fixed compact set, which is `C^n` by
`IsCompact.contMDiffAt_parametric_setIntegral`.

Subtracting the componentwise average normalizes a smooth family of functions to have integral
zero over every component, jointly smoothly in the parameter: this is how families of primitives
of exact one-forms, or of Hamiltonians, are normalized to have mean zero.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M}
  {G HP : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ G HP} [IP.Boundaryless] {P : Type*} [TopologicalSpace P]
  [ChartedSpace HP P] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ∞} [IsManifold I n M] [IsManifold IP n P] {F : M × P → V}

/-- **Integrals over a compact connected component depending on a parameter.** If `F` is `C^n`
at every point `(y, p₀)` with `y` in the connected component of `x₀`, and that component is
compact, then `(x, p) ↦ ∫ y in M_x, F (y, p) ∂μ`, the integral over the connected component `M_x`
of `x`, is `C^n` at `(x₀, p₀)`. -/
theorem contMDiffAt_setIntegral_connectedComponent [IsFiniteMeasureOnCompacts μ] {x₀ : M}
    {p₀ : P} (hK : IsCompact (connectedComponent x₀))
    (hF : ∀ y ∈ connectedComponent x₀, ContMDiffAt (I.prod IP) 𝓘(ℝ, V) n F (y, p₀)) :
    ContMDiffAt (I.prod IP) 𝓘(ℝ, V) n
      (fun z : M × P ↦ ∫ y in connectedComponent z.1, F (y, z.2) ∂μ) (x₀, p₀) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  -- In the parameter, an integral over the fixed compact set `M_x₀`.
  have hg : ContMDiffAt IP 𝓘(ℝ, V) n (fun p ↦ ∫ y in connectedComponent x₀, F (y, p) ∂μ) p₀ :=
    hK.contMDiffAt_parametric_setIntegral hK.measure_lt_top.ne fun y hy ↦
      (hF y hy).comp (p₀, y) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  -- Near `x₀` the connected component of the point is `M_x₀`.
  refine (hg.comp (x₀, p₀) contMDiffAt_snd).congr_of_eventuallyEq ?_
  filter_upwards [prod_mem_nhds (isOpen_connectedComponent.mem_nhds mem_connectedComponent)
    univ_mem] with z hz
  rw [Function.comp_apply, connectedComponent_eq hz.1]

/-- **Integrals over connected components depending on a parameter.** On a compact manifold `M`
with a finite measure, if `F : M × P → V` is `C^n`, then so is
`(x, p) ↦ ∫ y in M_x, F (y, p) ∂μ`, the integral over the connected component `M_x` of `x`. -/
theorem _root_.ContMDiff.setIntegral_connectedComponent [CompactSpace M] [IsFiniteMeasure μ]
    (hF : ContMDiff (I.prod IP) 𝓘(ℝ, V) n F) :
    ContMDiff (I.prod IP) 𝓘(ℝ, V) n
      fun z : M × P ↦ ∫ y in connectedComponent z.1, F (y, z.2) ∂μ := fun z ↦
  contMDiffAt_setIntegral_connectedComponent isClosed_connectedComponent.isCompact
    fun y _ ↦ hF (y, z.2)

/-- **Averages over connected components depending on a parameter.** On a compact manifold `M`
with a finite measure, if `F : M × P → V` is `C^n`, then so is
`(x, p) ↦ ⨍ y in M_x, F (y, p) ∂μ`, the average over the connected component `M_x` of `x`. -/
theorem _root_.ContMDiff.setAverage_connectedComponent [CompactSpace M] [IsFiniteMeasure μ]
    (hF : ContMDiff (I.prod IP) 𝓘(ℝ, V) n F) :
    ContMDiff (I.prod IP) 𝓘(ℝ, V) n
      fun z : M × P ↦ ⨍ y in connectedComponent z.1, F (y, z.2) ∂μ := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  -- The normalizing factor `μ(M_x)⁻¹` is locally constant in the point.
  have hl : IsLocallyConstant fun x : M ↦ (μ.real (connectedComponent x))⁻¹ :=
    .of_constant_on_connected_components fun _ _ hy ↦ by rw [connectedComponent_eq hy]
  have hc : ContMDiff (I.prod IP) 𝓘(ℝ) n fun z : M × P ↦ (μ.real (connectedComponent z.1))⁻¹ :=
    hl.contMDiff.comp contMDiff_fst
  simp_rw [setAverage_eq]
  exact hc.smul hF.setIntegral_connectedComponent

end TauCeti
