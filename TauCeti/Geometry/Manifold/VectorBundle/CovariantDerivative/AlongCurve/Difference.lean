/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback

/-!
# Changing the connection in a covariant derivative along a curve

Two covariant derivatives `∇` and `∇'` on the tangent bundle differ by a tensor, their difference
`Δ = CovariantDerivative.difference ∇ ∇'`, with `Δ_x(σ x, v) = ∇_v σ - ∇'_v σ`. This file shows
that their covariant derivatives along a differentiable curve `γ` differ by the same tensor, applied
to the field and the velocity of the curve:

`∇_t V - ∇'_t V = Δ_(γ t)(V t, γ'(t))`.

In particular the two agree at every parameter where `V` vanishes. Read in the chart at `γ t`,
the two moving-chart formulas `v' + Γ(v, u')` differ only in their Christoffel terms, and the
Christoffel maps of two connections differ by the coordinates of their difference tensor
(`TauCeti.Manifold.symmL_christoffelMap_sub_christoffelMap`).

## Main results

* `CovariantDerivative.alongCurveWithin_sub_alongCurveWithin`: the change of connection within
  a parameter set, with `CovariantDerivative.alongCurve_sub_alongCurve` its unrestricted case.
-/

public section

open Bundle
open scoped Manifold

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov cov' : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  {γ : 𝕜 → M} (V : ∀ t, TangentSpace I (γ t))

/-- **Changing the connection along a curve.** Within a parameter set with unique derivatives,
along a curve differentiable there, the covariant derivatives of a field `V` for two connections
differ by their difference tensor applied to `V` and the velocity of the curve. -/
theorem alongCurveWithin_sub_alongCurveWithin {s : Set 𝕜} {t : 𝕜}
    (hs : UniqueDiffWithinAt 𝕜 s t) (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t) :
    alongCurveWithin cov γ V s t - alongCurveWithin cov' γ V s t =
      cov.difference cov' (γ t) (V t) (curveVelocityWithin I γ s t) := by
  set e := trivializationAt E (TangentSpace I) (γ t)
  have hx : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ t)
  rw [alongCurveWithin_apply, alongCurveWithin_apply, ← map_sub, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, add_sub_add_left_eq_sub, sectionCoord_apply,
    derivWithin_extChartAt_comp γ hx hs (hasMFDerivWithinAt_curveVelocityWithin hγ),
    symmL_christoffelMap_sub_christoffelMap _ cov cov' hx, e.symmL_continuousLinearMapAt hx,
    e.symmL_continuousLinearMapAt hx]

/-- **Changing the connection along a curve.** Along a curve differentiable at `t`, the
covariant derivatives of a field `V` for two connections differ by their difference tensor
applied to `V` and the velocity of the curve: `∇_t V - ∇'_t V = Δ(V t, γ'(t))`. -/
theorem alongCurve_sub_alongCurve {t : 𝕜} (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t) :
    alongCurve cov γ V t - alongCurve cov' γ V t =
      cov.difference cov' (γ t) (V t) (curveVelocity I γ t) := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← curveVelocityWithin_univ]
  exact alongCurveWithin_sub_alongCurveWithin cov cov' V uniqueDiffWithinAt_univ
    hγ.mdifferentiableWithinAt

end CovariantDerivative
