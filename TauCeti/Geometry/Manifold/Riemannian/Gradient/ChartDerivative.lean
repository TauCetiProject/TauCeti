/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import TauCeti.Geometry.Manifold.VectorField.Chart.Riemannian

/-!
# The chart derivative of a gradient at a critical point

Let `f` be a function on a boundaryless manifold `M` with a continuous Riemannian metric `g`, and
let `x` be a critical point of `f` at which `f` is `C²` and its gradient is differentiable, as
holds for a `C²` function and a `C¹` metric (`TauCeti.Manifold.contMDiffAt_mgradient`). The
gradient `grad f` vanishes at `x`, so its chart derivative
`D = TauCeti.vectorFieldChartDerivative I (grad f) x` is the derivative of a vector field at a
zero. When `D` is invertible, the zero is nondegenerate and the sign of the determinant of `D` is
its local index in the Poincaré–Hopf theorem; at a degenerate zero the determinant vanishes and
does not determine the index (for `f t = t ^ 4` on `ℝ`, `D = 0` at `0` while the index is `1`).
This file identifies `D` with the critical Hessian raised by the metric at `x`:
`g_x (w, D v) = Hess f x (v, w)` (`TauCeti.inner_vectorFieldChartDerivative_mgradient`).
Consequently `D` is `g_x`-symmetric (`TauCeti.inner_vectorFieldChartDerivative_mgradient_comm`),
it is invertible exactly at a nondegenerate critical point, and there the sign of its determinant
is `(-1)` to the Morse index of `f` at `x`
(`TauCeti.sign_det_vectorFieldChartDerivative_mgradient`). In particular, at a nondegenerate
critical point the index of the zero of the gradient field does not depend on the metric.

The identification rests on the product rule at a zero
`MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero`: applied to `σ = grad f` and a field
`τ` with `τ x = w`, the function `g(grad f, τ) = df(τ)` has derivative `g_x (w, D ·)`, while by
definition of the critical Hessian it has derivative `Hess f x (·, w)` at the critical point `x`.

## Main results

* `TauCeti.inner_vectorFieldChartDerivative_mgradient`: at a critical point, the chart derivative
  of the gradient is the critical Hessian raised by the metric.
* `TauCeti.inner_vectorFieldChartDerivative_mgradient_comm`: it is symmetric for the metric.
* `TauCeti.vectorFieldChartDerivative_mgradient_apply_eq_zero_iff`: its kernel is the kernel of
  the critical Hessian.
* `TauCeti.det_vectorFieldChartDerivative_mgradient_ne_zero_iff`: its determinant is nonzero
  exactly at a nondegenerate critical point.
* `TauCeti.sign_det_vectorFieldChartDerivative_mgradient`: at a nondegenerate critical point the
  sign of its determinant is `(-1) ^ manifoldMorseIndex I f x`.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the index of a gradient field at a nondegenerate critical point).
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open Bundle Filter Set VectorField
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

section Gradient

variable [IsManifold I 2 M] {f : M → ℝ} {x : M}

/-- **The chart derivative of the gradient at a critical point is the Hessian.** At a critical
point `x` of a function `f` which is `C²` at `x`, if the gradient of `f` is differentiable at `x`,
its chart derivative `D` satisfies `g_x (w, D v) = Hess f x (v, w)`: it is the critical Hessian
raised by the metric at `x`. -/
theorem inner_vectorFieldChartDerivative_mgradient
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    inner ℝ w (vectorFieldChartDerivative I (Manifold.mgradient I f) x v : TangentSpace I x) =
      criticalHessian I f x v w := by
  -- Extend `w` to a vector field `Y`; then `Hess f x (v, w)` differentiates `df(Y) = g(grad f, Y)`.
  let Y := FiberBundle.extend E w
  have hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E w
  have hH := criticalHessian_apply_eq_mvfderiv hf hcrit hY v
  have hpair : (fun y ↦ mvfderiv I f y (Y y)) = fun y ↦ inner ℝ (Manifold.mgradient I f y) (Y y) :=
    funext fun y ↦ (Manifold.inner_mgradient _).symm
  rw [hpair, hgrad.mvfderiv_inner_bundle_apply_of_eq_zero
    (Manifold.mgradient_eq_zero_iff.mpr hcrit) hY.continuousAt v] at hH
  simpa only [Y, FiberBundle.extend_apply_self] using hH.symm

/-- At a critical point of a `C²` function with differentiable gradient, the chart derivative `D`
of the gradient is symmetric for the metric at the critical point: `g_x (w, D v) = g_x (v, D w)`. -/
theorem inner_vectorFieldChartDerivative_mgradient_comm
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    inner ℝ w (vectorFieldChartDerivative I (Manifold.mgradient I f) x v : TangentSpace I x) =
      inner ℝ v (vectorFieldChartDerivative I (Manifold.mgradient I f) x w : TangentSpace I x) := by
  rw [inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit,
    inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit, criticalHessian_apply_swap hf]

/-- At a critical point of a `C²` function with differentiable gradient, a tangent vector is in
the kernel of the chart derivative of the gradient exactly when it is in the kernel of the critical
Hessian. -/
theorem vectorFieldChartDerivative_mgradient_apply_eq_zero_iff
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v : TangentSpace I x) :
    vectorFieldChartDerivative I (Manifold.mgradient I f) x v = 0 ↔
      criticalHessian I f x v = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_, fun h ↦ ?_⟩
  · rw [← inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit, h]
    exact inner_zero_right _
  · have h' := inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit v
      (vectorFieldChartDerivative I (Manifold.mgradient I f) x v)
    rw [h] at h'
    exact (inner_self_eq_zero (𝕜 := ℝ) (E := TangentSpace I x)).mp h'

/-- **The index of a gradient at a nondegenerate critical point.** At a nondegenerate critical
point `x` of a function whose gradient is differentiable at `x`, the sign of the determinant of the
chart derivative of the gradient is `(-1)` to the Morse index of the function at `x`. In
particular it does not depend on the metric. -/
theorem sign_det_vectorFieldChartDerivative_mgradient
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    SignType.sign (LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x)) =
      (-1) ^ manifoldMorseIndex I f x := by
  obtain ⟨hf, hcrit, hinv⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let D := vectorFieldChartDerivative I (Manifold.mgradient I f) x
  -- Read `D` as an endomorphism of the tangent space at `x`, which carries the metric at `x`.
  let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x := D
  have hH (v w : TangentSpace I x) : inner ℝ w (T v) = criticalHessian I f x v w :=
    inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit v w
  have hT : T.IsSymmetric := fun v w ↦ by
    rw [real_inner_comm]
    exact inner_vectorFieldChartDerivative_mgradient_comm hgrad hf hcrit v w
  have hker : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ hinv.injective ?_
    rw [map_zero]
    exact (vectorFieldChartDerivative_mgradient_apply_eq_zero_iff hgrad hf hcrit v).mp hv
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  refine hT.sign_det_eq_neg_one_pow_sigNeg hker fun v ↦ ?_
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    real_inner_comm, hH]

/-- **Nondegeneracy from the chart derivative of the gradient.** At a critical point of a `C²`
function with differentiable gradient, the chart derivative of the gradient has nonzero
determinant exactly when the critical point is nondegenerate. -/
theorem det_vectorFieldChartDerivative_mgradient_ne_zero_iff
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) :
    LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x) ≠ 0 ↔
      IsManifoldNondegenerateCriticalPoint I f x := by
  refine ⟨fun hdet ↦ ?_, fun h hdet ↦ ?_⟩
  · -- A nonzero determinant makes `D` injective, hence the critical Hessian injective.
    have hD := LinearMap.ker_eq_bot.mp <| (LinearMap.isUnit_iff_ker_eq_bot _).mp <|
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    refine isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mpr ⟨hf, hcrit,
      criticalHessian_isInvertible_of_injective <| (injective_iff_map_eq_zero _).mpr
        fun v hv ↦ (injective_iff_map_eq_zero _).mp hD v ?_⟩
    exact (vectorFieldChartDerivative_mgradient_apply_eq_zero_iff hgrad hf hcrit v).mpr hv
  · have hs := sign_det_vectorFieldChartDerivative_mgradient hgrad h
    rw [hdet, sign_zero] at hs
    rcases neg_one_pow_eq_or SignType (manifoldMorseIndex I f x) with h1 | h1 <;>
      rw [h1] at hs <;> exact absurd hs (by decide)

end Gradient

end TauCeti
