/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Basic

/-!
# Injectivity radius of real inner-product spaces

Every finite-dimensional real inner-product space has `inj(p) = ⊤` at every point `p` and
`inj(F) = ⊤`, because the exponential map is translation by `p` and `Set.univ` is a normal domain.

## Main results

* `TauCeti.Manifold.injectivityRadiusAt_model_space`: `inj(p) = ⊤` on real inner-product spaces.
* `TauCeti.Manifold.injectivityRadius_model_space`: `inj(F) = ⊤` on real inner-product spaces.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10.
-/

public section

open Set
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every point of a finite-dimensional real inner-product space has infinite injectivity radius. -/
@[simp] theorem injectivityRadiusAt_model_space (p : F) : injectivityRadiusAt 𝓘(ℝ, F) F p = ⊤ :=
  injectivityRadiusAt_eq_top_iff_isNormalDomain_univ.2
    (isNormalDomain_model_space p isOpen_univ (mem_univ 0) (starConvex_univ 0))

/-- A finite-dimensional real inner-product space has infinite global injectivity radius. -/
@[simp] theorem injectivityRadius_model_space : injectivityRadius 𝓘(ℝ, F) F = ⊤ := by
  simp [injectivityRadius_def]

end TauCeti.Manifold

end
