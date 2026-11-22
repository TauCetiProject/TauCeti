/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Riemannian and intrinsic Hessians

For a metric-compatible connection `∇` and a function `f` which is `C²` at a point `x`, the
covariant derivative of the gradient of `f`, paired with the metric, is the critical Hessian of
`f` at `x`, the second derivative of `f` in the preferred chart at `x`, corrected by a first-order
term:

`⟪∇_v grad f, w⟫ = criticalHessian f x v w - df_x(∇_v W)`,

where `W = FiberBundle.extend E w` is the vector field with constant coordinates `w` in the
preferred chart at `x`. The correction `∇_v W` is the Christoffel map of `∇` in that chart
(`TauCeti.Manifold.covariantDerivative_extend_eq_christoffelMap`), so away from critical points
the connection, and for the Levi–Civita connection the metric, enters the Hessian through the term
`df_x(Γ(w, v))`. Away from critical points both terms on the right depend on the preferred chart;
only their difference is coordinate-free. No torsion assumption is needed.

At a critical point `df_x = 0` and the correction vanishes: the pairing is the critical Hessian
for every metric-compatible connection. In particular the Riemannian Hessian defined using the
Levi–Civita connection is the critical Hessian there, so its value at a critical point is
independent of the chosen metric and connection, and the intrinsic Morse index can be read from it.

The comparison requires only `C²` regularity of the function at the point and a `C¹` metric.

## Main results

* `TauCeti.inner_covariantDerivative_mgradient_eq_criticalHessian_sub`: the Hessian of `f` for a
  metric-compatible connection is the critical Hessian minus `df_x(∇_v W)`.
* `TauCeti.Manifold.hessian_eq_criticalHessian_sub`: the same for the Riemannian Hessian.
* `TauCeti.criticalHessian_apply_eq_inner_covariantDerivative` and
  `TauCeti.Manifold.hessian_eq_criticalHessian`: at a critical point, these Hessians are the
  critical Hessian.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Chapter 4, for the
  Hessian and the Christoffel symbols of a connection in a chart.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- **The Hessian of a metric-compatible connection in the preferred chart.** For any
metric-compatible connection `∇` and any point `x` at which `f` is `C²`, pairing `∇_v grad f`
with `w` gives the critical Hessian of `f` at `x`, minus `df_x(∇_v W)` for the vector field `W`
with constant coordinates `w` in the preferred chart at `x`. That correction is `df_x` of the
Christoffel map of `∇` in this chart, and vanishes at critical points. No torsion condition is
needed. -/
theorem inner_covariantDerivative_mgradient_eq_criticalHessian_sub
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : CovariantDerivative.IsMetricCompatible
      (I := I) (V := fun y : M ↦ TangentSpace I y) cov)
    (v w : TangentSpace I x) :
    inner ℝ (cov (Manifold.mgradient I f) x v) w =
      criticalHessian I f x v w - mvfderiv I f x (cov (FiberBundle.extend E w) x v) := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x :=
    (Manifold.contMDiffAt_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt one_ne_zero
  -- Metric compatibility differentiates `⟪grad f, W⟫ = df(W)`, whose derivative along `v` is the
  -- critical Hessian.
  have hmetric := hcov.mvfderiv_inner_eq (FiberBundle.extend E v) hgrad
    (FiberBundle.mdifferentiableAt_extend I E w)
  simp only [Manifold.inner_mgradient, FiberBundle.extend_apply_self] at hmetric
  rw [← mvfderiv_mvfderiv_extend_eq_criticalHessian hf, hmetric, add_sub_cancel_right]

/-- For any metric-compatible connection, the derivative of the gradient at a critical point,
paired with the metric, equals the intrinsic critical Hessian. No torsion condition is needed. -/
theorem criticalHessian_apply_eq_inner_covariantDerivative
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : CovariantDerivative.IsMetricCompatible
      (I := I) (V := fun y : M ↦ TangentSpace I y) cov)
    (v w : TangentSpace I x) :
    criticalHessian I f x v w = inner ℝ (cov (Manifold.mgradient I f) x v) w := by
  rw [inner_covariantDerivative_mgradient_eq_criticalHessian_sub hf hcov, hcrit,
    zero_apply, sub_zero]

namespace Manifold

/-- **The Riemannian Hessian in the preferred chart.** At any point `x` at which `f` is `C²`, the
Riemannian Hessian for a `C¹` metric is the critical Hessian, the second derivative of `f` in the
preferred chart at `x`, minus `df_x(∇_v W)` for the Levi–Civita connection `∇` and the vector
field `W` with constant coordinates `w` in that chart. -/
theorem hessian_eq_criticalHessian_sub (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    hessian I f x v w = criticalHessian I f x v w -
      mvfderiv I f x
        (CovariantDerivative.leviCivitaConnection I M (FiberBundle.extend E w) x v) := by
  rw [hessian_def]
  exact inner_covariantDerivative_mgradient_eq_criticalHessian_sub hf
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) v w

/-- At a critical point, the Riemannian Hessian for any `C¹` metric is the intrinsic Hessian.
Only `C²` regularity of the function at this point is required. -/
theorem hessian_eq_criticalHessian (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    hessian I f x v w = criticalHessian I f x v w := by
  rw [hessian_eq_criticalHessian_sub hf, hcrit, zero_apply, sub_zero]

end Manifold

end TauCeti
