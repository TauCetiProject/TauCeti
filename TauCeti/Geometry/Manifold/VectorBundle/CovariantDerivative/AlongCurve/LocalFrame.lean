/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Metric connection coefficients along a curve

The connection coefficients of a local frame orthonormal along a curve are skew-symmetric
(`IsLocalFrameOn.coeff_covariantDerivative_curveVelocity_add_eq_zero`). This curvewise version
of `IsLocalFrameOn.coeff_covariantDerivative_add_eq_zero` only needs differentiability of the
curve at the parameter and of the two frame sections at its image, with orthonormality along
the curve near that parameter. It supplies the coefficient identities used when differentiating
moving-frame coordinates.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018,
  Chapter 9 (geodesic curvature and Gauss–Bonnet).
-/

public noncomputable section

open Bundle CovariantDerivative Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {n : ℕ∞ω} {u : Set M} {γ : ℝ → M} {t : ℝ}

/-- **Curvewise skewness of the connection matrix.** For a metric connection, the coefficient of
`∇_{γ'} sⱼ` along `sᵢ` at `γ t` is minus the coefficient of `∇_{γ'} sᵢ` along `sⱼ`, when the
local frame is orthonormal along `γ` near `t`. Only `γ` differentiable at `t` and the two frame
sections differentiable at `γ t` are needed. -/
theorem coeff_covariantDerivative_curveVelocity_add_eq_zero {ι : Type*} [Finite ι]
    {s : ι → Π x : M, TangentSpace I x} (hs : IsLocalFrameOn I E n s u) (hu : γ t ∈ u)
    (ho : ∀ᶠ r in 𝓝 t, Orthonormal ℝ (fun i ↦ s i (γ r)))
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) {i j : ι}
    (hsi : MDiffAt (T% (s i)) (γ t)) (hsj : MDiffAt (T% (s j)) (γ t)) :
    hs.coeff i (γ t) (cov (s j) (γ t) (curveVelocity I γ t)) +
      hs.coeff j (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) = 0 := by
  classical
  have hc : (fun r ↦ inner ℝ (s i (γ r)) (s j (γ r))) =ᶠ[𝓝 t]
      fun _ ↦ if i = j then (1 : ℝ) else 0 :=
    ho.mono fun r hr ↦ (orthonormal_iff_ite.mp hr) i j
  have hm := hcov.inner_alongCurve_add_inner_alongCurve_eq_zero_of_eventuallyEq_const hγ
    (differentiableAt_sectionCoord γ (fun r ↦ s i (γ r)) (hsi.comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    (differentiableAt_sectionCoord γ (fun r ↦ s j (γ r)) (hsj.comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))) hc
  rw [alongCurve_pullback cov γ (s i) (hasMFDerivAt_curveVelocity hγ) hsi,
    alongCurve_pullback cov γ (s j) (hasMFDerivAt_curveVelocity hγ) hsj] at hm
  rw [hs.coeff_eq_inner hu ho.self_of_nhds, hs.coeff_eq_inner hu ho.self_of_nhds]
  linarith [real_inner_comm (cov (s i) (γ t) (curveVelocity I γ t)) (s j (γ t))]

end IsLocalFrameOn
