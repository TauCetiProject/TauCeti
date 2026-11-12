/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic

/-!
# The critical Hessian of the height function on the sphere

Let `v` be a unit vector of a real inner product space `E` of dimension `n + 1`, and let
`h_v(x) = ⟪x, v⟫` be the height function on the unit sphere (`TauCeti.sphereHeight`). Its
critical points are the poles `±v`, and there its critical Hessian is

`Hess_x h_v (a, b) = -h_v(x) ⟪a, b⟫`,

where the tangent vectors `a`, `b` are read in `E` through the differential of the inclusion of
the sphere (`TauCeti.criticalHessian_sphereHeight`): minus the inner product at the north pole `v`,
where `h_v = 1`, and the inner product at the south pole `-v`, where `h_v = -1`. This is the second
fundamental form of the unit sphere paired with the normal `x`, as for any linear function
restricted to a hypersurface at a critical point.

The computation takes place in the preferred chart at the north pole, stereographic projection
from the south pole. There the height is `TauCeti.stereographicHeight`, whose second derivative at
the origin is minus the inner product (`TauCeti.fderiv_fderiv_stereographicHeight_zero`), and the
differential of the inclusion of the sphere is isometric at the centre of the chart
(`TauCeti.inner_mvfderiv_coe_sphere`).

## Main results

* `TauCeti.criticalHessian_sphereHeight_self`: the critical Hessian at the north pole.
* `TauCeti.criticalHessian_sphereHeight_neg`: the critical Hessian at the south pole.
* `TauCeti.criticalHessian_sphereHeight`: the critical Hessian at a critical point `x` is
  `-h_v(x)` times the inner product.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the second fundamental form of a hypersurface).
-/

public section

open Metric Module
open scoped Manifold InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The Hessian of the height at the north pole.** At the north pole `v` the critical Hessian of
the height `x ↦ ⟪x, v⟫` is minus the inner product of tangent vectors read in `E`. -/
theorem criticalHessian_sphereHeight_self (v : sphere (0 : E) 1) (a b : TangentSpace (𝓡 n) v) :
    criticalHessian (𝓡 n) (sphereHeight v) v a b =
      -⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v a,
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v b⟫_ℝ := by
  rw [criticalHessian_apply_eq_fderiv_fderiv, sphereHeight_comp_extChartAt_symm,
    extChartAt_sphere_apply_self, fderiv_fderiv_stereographicHeight_zero,
    inner_mvfderiv_coe_sphere v a b]
  -- `tangentSpaceCastModel` reads a tangent vector as its chart coordinate, by definition.
  rfl

/-- **The Hessian of the height at the south pole.** At the south pole `-v` the critical Hessian
of the height `x ↦ ⟪x, v⟫` is the inner product of tangent vectors read in `E`. -/
theorem criticalHessian_sphereHeight_neg (v : sphere (0 : E) 1)
    (a b : TangentSpace (𝓡 n) (-v)) :
    criticalHessian (𝓡 n) (sphereHeight v) (-v) a b =
      ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (-v) a,
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (-v) b⟫_ℝ := by
  have h := criticalHessian_sphereHeight_self (n := n) (-v) a b
  rw [sphereHeight_neg, criticalHessian_neg, neg_apply, neg_apply] at h
  exact neg_injective h

/-- **The Hessian of the height at its critical points.** At a critical point `x` of the height
`h_v(x) = ⟪x, v⟫`, one of the poles `±v`, the critical Hessian is `-h_v(x)` times the inner product
of tangent vectors read in `E`: the second fundamental form of the unit sphere paired with its
normal `x`. -/
theorem criticalHessian_sphereHeight {v x : sphere (0 : E) 1}
    (hx : x ∈ criticalPoints (𝓡 n) (sphereHeight v)) (a b : TangentSpace (𝓡 n) x) :
    criticalHessian (𝓡 n) (sphereHeight v) x a b =
      -(sphereHeight v x * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x a,
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x b⟫_ℝ) := by
  rw [criticalPoints_sphereHeight, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [criticalHessian_sphereHeight_self, sphereHeight_self, one_mul]
  · rw [criticalHessian_sphereHeight_neg, sphereHeight_neg_self, neg_one_mul, neg_neg]

end TauCeti
