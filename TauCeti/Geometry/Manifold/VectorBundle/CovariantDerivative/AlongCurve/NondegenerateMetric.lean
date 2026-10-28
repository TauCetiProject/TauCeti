/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic

/-!
# Compatibility with a nondegenerate metric along a curve

Let `g` be a smooth symmetric nondegenerate metric on `M`, of any signature, and let `∇` be a
covariant derivative on `TM` compatible with `g`. This file proves the product rule

`(d/dt) g(V, W) = g(D V / dt, W) + g(V, D W / dt)`

for tangent fields `V`, `W` along a curve, and its two standard consequences:

* along a curve, the pairing `g(V, W)` of two parallel fields is constant, so parallel transport
  preserves `g`;
* the pairing `g(γ', γ')` of the velocity of a geodesic of `∇` with itself is constant. For a
  Lorentzian metric this says that a geodesic is timelike, null or spacelike throughout.

These are stated for any connection compatible with `g`; in particular they hold for every
Levi-Civita connection of `g`, through
`TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection.isMetricCompatible`. The
product rule is the specialization of `CovariantDerivative.hasDerivWithinAt_apply_alongCurveWithin`
to the pairing `g`.

## Main results

All results live in the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`.

* `IsMetricCompatible.hasDerivWithinAt_apply_alongCurveWithin` and
  `IsMetricCompatible.hasDerivAt_apply_alongCurve`: the product rule within a parameter set and
  with unrestricted derivatives, with the differentiability and `derivWithin`/`deriv` forms
  `IsMetricCompatible.differentiableWithinAt_apply`,
  `IsMetricCompatible.derivWithin_apply_alongCurveWithin`,
  `IsMetricCompatible.differentiableAt_apply` and `IsMetricCompatible.deriv_apply_alongCurve`.
* `IsMetricCompatible.apply_eq_of_alongCurveWithin_eq_zero`: parallel fields along a curve have
  constant pairing on a preconnected parameter set.
* `IsMetricCompatible.apply_curveVelocityWithin_self_eq_of_accelerationWithin_eq_zero`: a curve
  with vanishing covariant acceleration has constant `g(γ', γ')` on a preconnected parameter set.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3: covariant differentiation along curves, parallel translation and geodesics.
* `TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed`: the positive-definite argument
  for constant speed, followed here with `g` in place of the inner product.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {V W : ∀ r, TangentSpace I (γ r)}

/-- **The product rule along a curve** for a covariant derivative compatible with a nondegenerate
metric: for two tangent fields along a differentiable real curve whose coordinate readings are
differentiable within `s` at `t`, `(d/dt) g(V, W) = g(D V / dt, W) + g(V, D W / dt)` within `s`
at `t`. -/
theorem IsMetricCompatible.hasDerivWithinAt_apply_alongCurveWithin (h : g.IsMetricCompatible cov)
    (hu : UniqueDiffWithinAt ℝ s t) (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ g (γ r) (V r) (W r))
      (g (γ t) (alongCurveWithin cov γ V s t) (W t) +
        g (γ t) (V t) (alongCurveWithin cov γ W s t)) s t :=
  CovariantDerivative.hasDerivWithinAt_apply_alongCurveWithin
    (fun _ _ hY hZ ↦ g.mdifferentiableAt_apply hY hZ) (fun _ _ hY hZ v ↦ h.mvfderiv_eq hY hZ v)
    hu hγ hV hW

/-- The pairing `g(V, W)` of two tangent fields along a differentiable real curve, whose coordinate
readings are differentiable within `s` at `t`, is differentiable within `s` at `t`. -/
theorem IsMetricCompatible.differentiableWithinAt_apply (h : g.IsMetricCompatible cov)
    (hu : UniqueDiffWithinAt ℝ s t) (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (fun r ↦ g (γ r) (V r) (W r)) s t :=
  (h.hasDerivWithinAt_apply_alongCurveWithin hu hγ hV hW).differentiableWithinAt

/-- The product rule along a curve for a covariant derivative compatible with a nondegenerate
metric, as an identity for `derivWithin`. -/
theorem IsMetricCompatible.derivWithin_apply_alongCurveWithin (h : g.IsMetricCompatible cov)
    (hu : UniqueDiffWithinAt ℝ s t) (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    derivWithin (fun r ↦ g (γ r) (V r) (W r)) s t =
      g (γ t) (alongCurveWithin cov γ V s t) (W t) +
        g (γ t) (V t) (alongCurveWithin cov γ W s t) :=
  (h.hasDerivWithinAt_apply_alongCurveWithin hu hγ hV hW).derivWithin hu

/-- The product rule along a curve for a covariant derivative compatible with a nondegenerate
metric, with unrestricted derivatives: `(d/dt) g(V, W) = g(D V / dt, W) + g(V, D W / dt)`. -/
theorem IsMetricCompatible.hasDerivAt_apply_alongCurve (h : g.IsMetricCompatible cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    HasDerivAt (fun r ↦ g (γ r) (V r) (W r))
      (g (γ t) (alongCurve cov γ V t) (W t) + g (γ t) (V t) (alongCurve cov γ W t)) t := by
  apply hasDerivWithinAt_univ.mp
  simpa only [alongCurveWithin_univ] using
    h.hasDerivWithinAt_apply_alongCurveWithin uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt hV.differentiableWithinAt hW.differentiableWithinAt

/-- The pairing `g(V, W)` of two tangent fields along a differentiable real curve, whose coordinate
readings are differentiable at `t`, is differentiable at `t`. -/
theorem IsMetricCompatible.differentiableAt_apply (h : g.IsMetricCompatible cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    DifferentiableAt ℝ (fun r ↦ g (γ r) (V r) (W r)) t :=
  (h.hasDerivAt_apply_alongCurve hγ hV hW).differentiableAt

/-- The product rule along a curve for a covariant derivative compatible with a nondegenerate
metric, as an identity for `deriv`. -/
theorem IsMetricCompatible.deriv_apply_alongCurve (h : g.IsMetricCompatible cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    deriv (fun r ↦ g (γ r) (V r) (W r)) t =
      g (γ t) (alongCurve cov γ V t) (W t) + g (γ t) (V t) (alongCurve cov γ W t) :=
  (h.hasDerivAt_apply_alongCurve hγ hV hW).deriv

/-- **Parallel transport preserves a compatible nondegenerate metric.** On a preconnected
parameter set `s` with unique derivatives, two tangent fields along a differentiable curve that
have differentiable coordinate readings and are parallel, `D V / dt = D W / dt = 0` on `s`, have
the same pairing `g(V, W)` at every two parameters of `s`. -/
theorem IsMetricCompatible.apply_eq_of_alongCurveWithin_eq_zero (h : g.IsMetricCompatible cov)
    (hs : UniqueDiffOn ℝ s) (hconn : IsPreconnected s) (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s)
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hV₀ : ∀ t ∈ s, alongCurveWithin cov γ V s t = 0)
    (hW₀ : ∀ t ∈ s, alongCurveWithin cov γ W s t = 0) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    g (γ a) (V a) (W a) = g (γ b) (V b) (W b) := by
  have hderiv (t : ℝ) (ht : t ∈ s) :
      HasDerivWithinAt (fun r ↦ g (γ r) (V r) (W r)) 0 s t := by
    simpa only [hV₀ t ht, hW₀ t ht, map_zero, zero_apply, add_zero] using
      h.hasDerivWithinAt_apply_alongCurveWithin (hs t ht) (hγ t ht) (hV t ht) (hW t ht)
  refine hconn.ordConnected.convex.is_const_of_fderivWithin_eq_zero
    (𝕜 := ℝ) (f := fun r ↦ g (γ r) (V r) (W r))
    (fun t ht ↦ (hderiv t ht).differentiableWithinAt) (fun t ht ↦ ?_) ha hb
  simpa using (hderiv t ht).hasFDerivWithinAt.fderivWithin (hs t ht)

/-- **Geodesics of a compatible connection have constant `g(γ', γ')`.** On a preconnected
parameter set `s` with unique derivatives, a `C²` curve whose covariant acceleration vanishes on
`s` pairs its within-set velocity with itself to the same value at every two parameters of `s`.
For a Lorentzian metric this says that a geodesic keeps its causal character. -/
theorem IsMetricCompatible.apply_curveVelocityWithin_self_eq_of_accelerationWithin_eq_zero
    (h : g.IsMetricCompatible cov) (hs : UniqueDiffOn ℝ s) (hconn : IsPreconnected s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (hacc : ∀ t ∈ s, accelerationWithin cov γ s t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    g (γ a) (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) =
      g (γ b) (curveVelocityWithin I γ s b) (curveVelocityWithin I γ s b) := by
  have hcoord (t : ℝ) (ht : t ∈ s) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t)) s t :=
    differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hpar (t : ℝ) (ht : t ∈ s) :
      alongCurveWithin cov γ (curveVelocityWithin I γ s) s t = 0 := by
    rw [← accelerationWithin_def, hacc t ht]
  exact h.apply_eq_of_alongCurveWithin_eq_zero hs hconn
    (hγ.mdifferentiableOn (by norm_num)) hcoord hcoord hpar hpar ha hb

end TauCeti.Manifold.ContMDiffNondegenerateMetric
