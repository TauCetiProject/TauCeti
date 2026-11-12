/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.Jacobian
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Geometry.Manifold.Riemannian.ArcLength

/-!
# Geodesic circles in polar coordinates

Let `p` be a point of a Riemannian manifold and let `b : ℂ →ₗᵢ[ℝ] T_p M` be a linear isometry, that
is, an orthonormal frame `(b 1, b Complex.I)` of a plane in `T_p M`; on a surface it is an
orthonormal frame of the tangent plane. The unit circle of that plane is
`e(θ) = b (circleMap 0 1 θ)`, parametrized by angular arclength with velocity
`e′(θ) = b (circleMap 0 1 θ * Complex.I)`, and geodesic polar coordinates are
`F(r, θ) = exp_p (r • e(θ))`.

This file studies the curves `θ ↦ F(r, θ)` of constant radius, the geodesic circles
`TauCeti.Manifold.geodesicCircle b r`. Their speed is the polar Jacobian
`j(r, θ) = ‖d(exp_p)_(r e(θ)) (r e′(θ))‖`, so the length of an arc of a geodesic circle is the
integral of `j(r, θ) dθ` over the angular interval. A geodesic circle is `2π`-periodic, and inside a
normal domain a geodesic circle of nonzero radius is injective on each period.

## Main definitions and results

* `TauCeti.Manifold.geodesicCircle`: the geodesic circle `θ ↦ exp_p (r • b (circleMap 0 1 θ))`.
* `TauCeti.Manifold.norm_curveVelocity_geodesicCircle`: the speed of a geodesic circle is the polar
  Jacobian.
* `TauCeti.Manifold.pathELength_geodesicCircle`: the length of an arc of a geodesic circle is the
  integral of the polar Jacobian over the angular interval.
* `TauCeti.Manifold.periodic_polarJacobian_circleMap` and
  `TauCeti.Manifold.pathELength_geodesicCircle_add_two_pi`: the polar Jacobian is `2π`-periodic in
  the angle, and the length of a full turn is `∫ θ in 0..2π, j(r, θ)`, whatever the initial angle.
* `TauCeti.Manifold.periodic_geodesicCircle` and
  `TauCeti.Manifold.IsNormalDomain.injOn_geodesicCircle`: a geodesic circle is `2π`-periodic, and
  inside a normal domain it is injective on each half-open angular interval of length `2π`.

All domains of the exponential map remain explicit.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 6 and 10.
* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, §4-6.
-/

public noncomputable section

open Bundle Function Set
open scoped ContDiff Manifold Real

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} (b : ℂ →ₗᵢ[ℝ] TangentSpace I p) {r θ : ℝ}

/-- The geodesic circle of radius `r` about `p` in the tangent plane framed by the linear isometry
`b : ℂ →ₗᵢ[ℝ] T_p M`, parametrized by the angle: the curve `θ ↦ exp_p (r • b (circleMap 0 1 θ))`.
As a function of `(r, θ)` it is the geodesic polar coordinate map. At a vector outside the domain
of the exponential map it takes the junk value of `riemannianExp`. -/
def geodesicCircle (r θ : ℝ) : M := riemannianExp I M p (r • b (circleMap 0 1 θ))

/-- A geodesic circle is the exponential image of the scaled unit circle of the framed tangent
plane. -/
theorem geodesicCircle_def (r θ : ℝ) :
    geodesicCircle b r θ = riemannianExp I M p (r • b (circleMap 0 1 θ)) := by rfl

/-- The geodesic circle of radius zero is constant at the centre. -/
@[simp] theorem geodesicCircle_zero [I.Boundaryless] [T2Space M] (θ : ℝ) :
    geodesicCircle b 0 θ = p := by
  rw [geodesicCircle_def, zero_smul, riemannianExp_zero]

/-- A geodesic circle is `2π`-periodic in the angle. -/
theorem periodic_geodesicCircle (r : ℝ) : Periodic (geodesicCircle b r) (2 * π) := fun θ ↦ by
  rw [geodesicCircle_def, geodesicCircle_def, periodic_circleMap 0 1 θ]

/-- A geodesic circle is smooth on any set of angles at which it stays in the domain of the
exponential map. -/
theorem contMDiffOn_geodesicCircle [I.Boundaryless] [T2Space M] {s : Set ℝ}
    (hmem : ∀ θ ∈ s, r • b (circleMap 0 1 θ) ∈ expDomain I M p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (geodesicCircle b r) s :=
  (contMDiffOn_riemannianExp p).comp
    (contDiff_const.smul (b.toContinuousLinearMap.contDiff.comp
      (contDiff_circleMap 0 1))).contMDiff.contMDiffOn hmem

/-- The speed of a geodesic circle is the polar Jacobian `j(r, θ) = ‖d(exp_p)_(r e(θ)) (r e′(θ))‖`
in the radial direction `e(θ) = b (circleMap 0 1 θ)` with angular vector
`e′(θ) = b (circleMap 0 1 θ * Complex.I)`. -/
theorem norm_curveVelocity_geodesicCircle [I.Boundaryless] [T2Space M]
    (hmem : r • b (circleMap 0 1 θ) ∈ expDomain I M p) :
    ‖curveVelocity I (geodesicCircle b r) θ‖ =
      polarJacobian p (b (circleMap 0 1 θ)) (b (circleMap 0 1 θ * Complex.I)) r := by
  have he : HasDerivAt (fun θ ↦ b (circleMap 0 1 θ)) (b (circleMap 0 1 θ * Complex.I)) θ :=
    b.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rw [funext (geodesicCircle_def b r)]
  exact norm_curveVelocity_riemannianExp_const_smul he hmem

/-- The length of an arc of a geodesic circle is the integral of the polar Jacobian over the
angular interval: `j(r, θ) dθ` is arclength on the circle of radius `r`. -/
theorem pathELength_geodesicCircle [I.Boundaryless] [T2Space M] {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁)
    (hmem : ∀ θ ∈ Icc θ₀ θ₁, r • b (circleMap 0 1 θ) ∈ expDomain I M p) :
    Manifold.pathELength I (geodesicCircle b r) θ₀ θ₁ = ENNReal.ofReal
      (∫ θ in θ₀..θ₁,
        polarJacobian p (b (circleMap 0 1 θ)) (b (circleMap 0 1 θ * Complex.I)) r) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  let s : Set ℝ := {θ | r • b (circleMap 0 1 θ) ∈ expDomain I M p}
  have hs : IsOpen s := (isOpen_expDomain p).preimage
    (continuous_const.smul (b.continuous.comp (continuous_circleMap 0 1)))
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (geodesicCircle b r) s :=
    (contMDiffOn_geodesicCircle b fun _ hθ ↦ hθ).of_le (by simp)
  rw [hγ.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hmem]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ' ↦ ?_
  have hθs : θ ∈ s := hmem θ (by rwa [uIcc_of_le hθ] at hθ')
  rw [curveVelocityWithin_of_mem_nhds (hs.mem_nhds hθs), norm_curveVelocity_geodesicCircle b hθs]

/-- The polar Jacobian `j(r, θ)` along the unit circle of the framed tangent plane is
`2π`-periodic in the angle. -/
theorem periodic_polarJacobian_circleMap (r : ℝ) :
    Periodic (fun θ ↦
      polarJacobian p (b (circleMap 0 1 θ)) (b (circleMap 0 1 θ * Complex.I)) r) (2 * π) :=
  fun θ ↦ by simp only [periodic_circleMap 0 1 θ]

/-- The length of a full turn of a geodesic circle is `∫ θ in 0..2π, j(r, θ)`, whatever the angle
at which the turn starts. -/
theorem pathELength_geodesicCircle_add_two_pi [I.Boundaryless] [T2Space M]
    {θ₀ : ℝ} (hmem : ∀ θ ∈ Icc θ₀ (θ₀ + 2 * π), r • b (circleMap 0 1 θ) ∈ expDomain I M p) :
    Manifold.pathELength I (geodesicCircle b r) θ₀ (θ₀ + 2 * π) = ENNReal.ofReal
      (∫ θ in 0..2 * π,
        polarJacobian p (b (circleMap 0 1 θ)) (b (circleMap 0 1 θ * Complex.I)) r) := by
  rw [pathELength_geodesicCircle b (le_add_of_nonneg_right Real.two_pi_pos.le) hmem,
    (periodic_polarJacobian_circleMap b r).intervalIntegral_add_eq θ₀ 0, zero_add]

/-- Inside a normal domain, a geodesic circle of nonzero radius is injective on each half-open
angular interval of length `2π`. -/
theorem IsNormalDomain.injOn_geodesicCircle {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) (hr : r ≠ 0) (θ₀ : ℝ)
    (hmem : ∀ θ ∈ Ico θ₀ (θ₀ + 2 * π), r • b (circleMap 0 1 θ) ∈ U) :
    InjOn (geodesicCircle b r) (Ico θ₀ (θ₀ + 2 * π)) := by
  intro θ hθ φ hφ heq
  rw [geodesicCircle_def, geodesicCircle_def] at heq
  exact injOn_circleMap_of_abs_sub_le' one_ne_zero (by linarith) hθ hφ
    (b.injective (smul_right_injective _ hr (h.injOn (hmem θ hθ) (hmem φ hφ) heq)))

end TauCeti.Manifold
