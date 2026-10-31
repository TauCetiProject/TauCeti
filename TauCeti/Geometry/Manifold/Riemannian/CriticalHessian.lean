/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Riemannian and intrinsic Hessians at critical points

At a critical point of a `C²` function, its intrinsic critical Hessian agrees with the covariant
derivative of its gradient paired with the metric. This holds for every metric-compatible
connection, without a torsion assumption. In particular, the Riemannian Hessian defined using the
Levi–Civita connection is the critical Hessian. Thus its value at a critical point is independent
of the chosen metric and connection, and the intrinsic Morse index can be read from it.

The comparison requires only `C²` regularity of the function at the critical point and a `C¹`
metric. Metric and connection independence are asserted only at critical points.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 1.
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

/-- For any metric-compatible connection, the derivative of the gradient at a critical point,
paired with the metric, equals the intrinsic critical Hessian. No torsion condition is needed. -/
theorem criticalHessian_apply_eq_inner_covariantDerivative
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : CovariantDerivative.IsMetricCompatible
      (I := I) (V := fun y : M ↦ TangentSpace I y) cov)
    (v w : TangentSpace I x) :
    criticalHessian I f x v w = inner ℝ (cov (Manifold.mgradient I f) x v) w := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hY := FiberBundle.mdifferentiableAt_extend I E w
  have hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x := by
    have h := Manifold.contMDiffAt_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)
    exact h.mdifferentiableAt one_ne_zero
  have hzero : Manifold.mgradient I f x = 0 := Manifold.mgradient_eq_zero_iff.mpr hcrit
  have hmetric := hcov.mvfderiv_inner_eq (FiberBundle.extend E v) hgrad hY
  simp only [Manifold.inner_mgradient, FiberBundle.extend_apply_self, hzero, inner_zero_left,
    add_zero] at hmetric
  have hH := criticalHessian_apply_eq_mvfderiv hf hcrit hY v
  simpa only [FiberBundle.extend_apply_self] using hH.trans hmetric

namespace Manifold

/-- At a critical point, the Riemannian Hessian for any `C¹` metric is the intrinsic Hessian.
Only `C²` regularity of the function at this point is required. -/
theorem hessian_eq_criticalHessian (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    hessian I f x v w = criticalHessian I f x v w := by
  rw [hessian_def]
  exact (criticalHessian_apply_eq_inner_covariantDerivative hf hcrit
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) v w).symm

end Manifold

end TauCeti
