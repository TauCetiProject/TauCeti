/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.FrameCoordinates.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Differentiating frame coordinates with a metric connection

Let `z = ⟪e₀, γ'⟫ + i ⟪e₁, γ'⟫` be the velocity coordinates of a curve in an orthonormal local
frame of a surface, and let `ω(X) = ⟪e₁, ∇_X e₀⟫` be the connection one-form of a metric
connection `∇`. Differentiating the coordinates gives
`z' = (∇_t γ')₀ + i (∇_t γ')₁ - i ω(γ') z`
(`IsLocalFrameOn.hasDerivAt_frameVelocityCoordinates`). The curve only needs to be differentiable
at `t`, with its velocity differentiable in the tangent-bundle trivialization centered at `γ t`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018,
  Chapter 9 (geodesic curvature and Gauss–Bonnet).
-/

public noncomputable section

open Bundle CovariantDerivative Filter TauCeti.Manifold
open scoped Manifold Topology

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {γ : ℝ → M} {t : ℝ}

/-- The derivative of the complex velocity coordinates in an orthonormal local frame is the
coordinate covariant acceleration minus `i ω(γ') z`. This holds for any metric connection, and
only needs `γ` differentiable at `t`, with its velocity differentiable in the tangent-bundle
trivialization centered at `γ t`. Orthonormality is only required along `γ` near `t`. -/
theorem hasDerivAt_frameVelocityCoordinates (hs : IsLocalFrameOn I E 1 s u)
    (hu : u ∈ 𝓝 (γ t)) (ho : ∀ᶠ r in 𝓝 t, Orthonormal ℝ (fun i ↦ s i (γ r)))
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hv : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ (curveVelocity I γ) (γ t)) t) :
    HasDerivAt (frameVelocityCoordinates s γ)
      ((inner ℝ (s 0 (γ t)) (alongCurve cov γ (curveVelocity I γ) t) : ℂ) +
        (inner ℝ (s 1 (γ t)) (alongCurve cov γ (curveVelocity I γ) t) : ℂ) * Complex.I -
          Complex.I * (hs.connectionForm cov 0 1 (γ t) ![curveVelocity I γ t] : ℂ) *
            frameVelocityCoordinates s γ t) t := by
  have ht := mem_of_mem_nhds hu
  have hframe (i : Fin 2) := ((hs.contMDiffOn i).contMDiffAt hu).mdifferentiableAt one_ne_zero
  have hcoord (i : Fin 2) := differentiableAt_sectionCoord γ (fun r ↦ s i (γ r))
    ((hframe i).comp t hγ) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hskew (i j : Fin 2) :
      hs.coeff i (γ t) (cov (s j) (γ t) (curveVelocity I γ t)) +
        hs.coeff j (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) = 0 := by
    have hc : (fun r ↦ inner ℝ (s i (γ r)) (s j (γ r))) =ᶠ[𝓝 t]
        fun _ ↦ if i = j then (1 : ℝ) else 0 :=
      ho.mono fun r hr ↦ (orthonormal_iff_ite.mp hr) i j
    have hm := hcov.inner_alongCurve_add_inner_alongCurve_eq_zero_of_eventuallyEq_const
      hγ (hcoord i) (hcoord j) hc
    rw [alongCurve_pullback cov γ (s i) (hasMFDerivAt_curveVelocity hγ) (hframe i),
      alongCurve_pullback cov γ (s j) (hasMFDerivAt_curveVelocity hγ) (hframe j)] at hm
    rw [hs.coeff_eq_inner ht ho.self_of_nhds, hs.coeff_eq_inner ht ho.self_of_nhds]
    linarith [real_inner_comm (cov (s i) (γ t) (curveVelocity I γ t)) (s j (γ t))]
  have hdiag (i : Fin 2) : hs.coeff i (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) = 0 := by
    linarith [hskew i i]
  have hswap := eq_neg_of_add_eq_zero_left (hskew 0 1)
  have hd (i : Fin 2) := hcov.hasDerivAt_inner_alongCurve hγ (hcoord i) hv
  have hinner (i : Fin 2) :
      inner ℝ (alongCurve cov γ (fun r ↦ s i (γ r)) t) (curveVelocity I γ t) =
        (frameVelocityCoordinates s γ t).re *
          hs.coeff 0 (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) +
        (frameVelocityCoordinates s γ t).im *
          hs.coeff 1 (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) := by
    rw [alongCurve_pullback cov γ (s i) (hasMFDerivAt_curveVelocity hγ) (hframe i),
      real_inner_comm,
      curveVelocity_eq_frameVelocityCoordinates ho.self_of_nhds
        (hs.generating ht Submodule.mem_top)]
    simp [inner_add_left, real_inner_smul_left, ← hs.coeff_eq_inner ht ho.self_of_nhds]
  have h0 := hd 0
  have h1 := hd 1
  rw [hinner] at h0 h1
  simp only [hdiag, mul_zero, add_zero, zero_add] at h0 h1
  rw [hswap] at h1
  convert h0.ofReal_comp.add (h1.ofReal_comp.mul_const Complex.I) using 1
  · funext r
    simpa only [Pi.add_apply, frameVelocityCoordinates_re, frameVelocityCoordinates_im] using
      (Complex.re_add_im (frameVelocityCoordinates s γ r)).symm
  · simp only [connectionForm_apply, Matrix.cons_val_zero]
    apply Complex.ext <;> simp <;> ring

end IsLocalFrameOn
