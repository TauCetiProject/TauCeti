/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.CoordinateChange

/-!
# The along-curve covariant derivative read in an arbitrary chart

`CovariantDerivative.alongCurveWithin` differentiates a tangent field `V` along a curve `γ` by the
moving-chart formula `v' + Γ (v, u')`, read in the chart centred at the current point `γ t`.  This
file proves that the same formula computed in *any* chart around `γ t`, transported back to
`TangentSpace I (γ t)`, returns the same tangent vector, for an arbitrary field along the curve.
`AlongCurve/Pullback.lean` obtains this only for fields pulled back from an ambient vector field,
where the value is identified with the ambient covariant derivative; the general statement needs
the Christoffel transformation law instead.

Two chart readings of `V` differ by the tangent coordinate change `A z`, so differentiating the
reading in the chart at `x` produces the extra term `(d/dt) (A (γ t)) v`, while the Christoffel
transformation law `TauCeti.Manifold.christoffelMap_coordChange` produces exactly its negative.
The cancellation of these two inhomogeneous terms is the content of the main theorem, and is what
allows a fixed chart to be used in place of the moving one.

## Main results

* `TauCeti.Manifold.sectionCoord_coordChange`: two chart readings of a field along a curve differ
  by the tangent coordinate change, with
  `TauCeti.Manifold.sectionCoord_eventuallyEq_coordChange` its form near a parameter.
* `CovariantDerivative.symmL_alongCurveInChartWithin`: **chart independence** -- the coordinate
  formula read in an arbitrary chart around `γ t` transports back to the moving-chart value.
* `CovariantDerivative.tangentCoordChange_alongCurveInChartWithin`: the resulting transformation
  law for the coordinate formula between two charts around `γ t`.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve": the chart formula.
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (γ : 𝕜 → M) (V : Π t, TangentSpace I (γ t))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The coordinate readings of a tangent field along a curve in the trivializations at two points
whose base sets contain `γ r` differ by the tangent coordinate change between them. -/
theorem sectionCoord_coordChange {x y : M} {r : 𝕜}
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y r =
      tangentCoordChange I x y (γ r) (sectionCoord (F := E) γ V x r) := by
  rw [sectionCoord_apply, sectionCoord_apply, ← continuousLinearMapAt_symmL_coordChange hx hy,
    (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := 𝕜) hx]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Near a parameter whose image lies in two base sets, the coordinate readings of a tangent field
along a curve are related by the tangent coordinate change. -/
theorem sectionCoord_eventuallyEq_coordChange {x y : M} {s : Set 𝕜} {r : 𝕜}
    (hγ : ContinuousWithinAt γ s r)
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y =ᶠ[𝓝[s] r]
      fun q ↦ tangentCoordChange I x y (γ q) (sectionCoord (F := E) γ V x q) := by
  filter_upwards
    [hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx),
    hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) y).open_baseSet.mem_nhds hy)] with q hqx hqy
  exact sectionCoord_coordChange γ V hqx hqy

end TauCeti.Manifold

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
  (γ : 𝕜 → M) (V : Π t, TangentSpace I (γ t))

/-- **Chart independence of the along-curve derivative.**  The coordinate formula computed in the
chart at an arbitrary point `x` whose base set contains `γ t`, transported back to
`TangentSpace I (γ t)`, is the moving-chart value `CovariantDerivative.alongCurveWithin`.  The
field along the curve is arbitrary: only differentiability of its moving-chart reading is
assumed. -/
theorem symmL_alongCurveInChartWithin {x : M} {s : Set 𝕜} {t : 𝕜}
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t) :
    (trivializationAt E (TangentSpace I) x).symmL 𝕜 (γ t)
        (alongCurveInChartWithin cov γ V s x t) =
      alongCurveWithin cov γ V s t := by
  -- The proof compares the two readings of `V` term by term: `hderivx` differentiates the reading
  -- in the chart at `x` by the product rule, producing an inhomogeneous term, and `hchris`
  -- rewrites its Christoffel term, producing the opposite one.  `key` records the resulting
  -- cancellation, and the two transports are then inverse to each other.
  have hγ' : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (curveVelocityWithin I γ s t)) :=
    hasMFDerivWithinAt_curveVelocityWithin hγ
  have hc0 : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hxsrc : γ t ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hAmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I (γ t) x) (γ t) := by
    have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
    exact (contMDiffAt_tangentCoordChange (I := I) (n := 1) (x := γ t) (y := x)
      hxsrc).mdifferentiableAt one_ne_zero
  have hAderiv : HasDerivWithinAt (fun r ↦ tangentCoordChange I (γ t) x (γ r))
      (mvfderiv I (tangentCoordChange I (γ t) x) (γ t) (curveVelocityWithin I γ s t)) s t :=
    hasDerivWithinAt_comp_curve hAmd hγ'
  -- Reading a tangent vector at `γ t` in the chart at `x` applies the coordinate change.
  have hread : ∀ u : E,
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t) u
        = tangentCoordChange I (γ t) x (γ t) u := fun u => by
    rw [← continuousLinearMapAt_symmL_coordChange (I := I) (x := γ t) (x₀ := x) hc0 hx u,
      symmL_trivializationAt_self]
  have hpointx : sectionCoord (F := E) γ V x t
      = tangentCoordChange I (γ t) x (γ t) (sectionCoord (F := E) γ V (γ t) t) :=
    sectionCoord_coordChange γ V hc0 hx
  -- The product rule for the reading in the chart at `x`.
  have hderivx : derivWithin (sectionCoord (F := E) γ V x) s t
      = mvfderiv I (tangentCoordChange I (γ t) x) (γ t) (curveVelocityWithin I γ s t)
            (sectionCoord (F := E) γ V (γ t) t)
        + tangentCoordChange I (γ t) x (γ t)
            (derivWithin (sectionCoord (F := E) γ V (γ t)) s t) :=
    ((hAderiv.clm_apply hV.hasDerivWithinAt).congr_of_eventuallyEq
      (sectionCoord_eventuallyEq_coordChange γ V hγ.continuousWithinAt hc0 hx)
      hpointx).derivWithin hu
  -- Its inhomogeneous term is the one appearing in the Christoffel transformation law.
  have hDapply : mvfderiv I (tangentCoordChange I (γ t) x) (γ t)
        (curveVelocityWithin I γ s t) (sectionCoord (F := E) γ V (γ t) t)
      = mvfderiv I (fun z ↦ tangentCoordChange I (γ t) x z
          (sectionCoord (F := E) γ V (γ t) t)) (γ t) (curveVelocityWithin I γ s t) := by
    have h₁ : HasDerivWithinAt (fun r ↦ tangentCoordChange I (γ t) x (γ r)
          (sectionCoord (F := E) γ V (γ t) t))
        (mvfderiv I (tangentCoordChange I (γ t) x) (γ t) (curveVelocityWithin I γ s t)
          (sectionCoord (F := E) γ V (γ t) t)) s t := by
      simpa using hAderiv.clm_apply
        (hasDerivWithinAt_const t s (sectionCoord (F := E) γ V (γ t) t))
    have h₂ : HasDerivWithinAt (fun r ↦ tangentCoordChange I (γ t) x (γ r)
          (sectionCoord (F := E) γ V (γ t) t))
        (mvfderiv I (fun z ↦ tangentCoordChange I (γ t) x z
          (sectionCoord (F := E) γ V (γ t) t)) (γ t) (curveVelocityWithin I γ s t)) s t :=
      hasDerivWithinAt_comp_curve (MDifferentiableAt.clm_apply hAmd mdifferentiableAt_const) hγ'
    rw [← h₁.derivWithin hu, ← h₂.derivWithin hu]
  -- The velocity of the curve, read in the two charts.
  have hvel : derivWithin (extChartAt I x ∘ γ) s t
      = tangentCoordChange I (γ t) x (γ t) (curveVelocityWithin I γ s t) := by
    rw [derivWithin_extChartAt_comp γ hx hu hγ']
    exact hread _
  have hvel₀ : derivWithin (extChartAt I (γ t) ∘ γ) s t = curveVelocityWithin I γ s t := by
    rw [derivWithin_extChartAt_comp γ hc0 hu hγ', continuousLinearMapAt_trivializationAt_self]
  have hchris := christoffelMap_coordChange (I := I) (M := M) (finBasis 𝕜 E) (x := γ t) (x₀ := x)
    hxsrc (curveVelocityWithin I γ s t) (sectionCoord (F := E) γ V (γ t) t)
    (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
    (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet))
  -- The two inhomogeneous terms cancel.
  have key : alongCurveInChartWithin cov γ V s x t
      = tangentCoordChange I (γ t) x (γ t) (alongCurveInChartWithin cov γ V s (γ t) t) := by
    rw [alongCurveInChartWithin_apply, alongCurveInChartWithin_apply, hderivx, hpointx, hvel,
      hchris, hDapply, hvel₀, map_add]
    abel
  rw [alongCurveWithin_apply, symmL_trivializationAt_self, key, ← hread]
  exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := 𝕜) hx _

/-- **The transformation law for the along-curve coordinate formula.**  Between the trivializations
at two points whose base sets contain `γ t`, the coordinate formula transforms by the tangent
coordinate change. -/
theorem tangentCoordChange_alongCurveInChartWithin {x y : M} {s : Set 𝕜} {t : 𝕜}
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ t ∈ (trivializationAt E (TangentSpace I) y).baseSet)
    (hu : UniqueDiffWithinAt 𝕜 s t) (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t) :
    alongCurveInChartWithin cov γ V s y t =
      tangentCoordChange I x y (γ t) (alongCurveInChartWithin cov γ V s x t) := by
  rw [← continuousLinearMapAt_symmL_coordChange hx hy,
    symmL_alongCurveInChartWithin cov γ V hx hu hγ hV,
    ← symmL_alongCurveInChartWithin cov γ V hy hu hγ hV,
    (trivializationAt E (TangentSpace I) y).continuousLinearMapAt_symmL (R := 𝕜) hy]

end CovariantDerivative
