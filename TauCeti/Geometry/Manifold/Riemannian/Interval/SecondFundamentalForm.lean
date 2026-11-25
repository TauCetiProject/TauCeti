/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Interval.Basic

/-!
# The second fundamental form of the boundary of a closed interval

On the closed interval `[a, b]`, `a < b`, with its Euclidean metric
(`TauCeti.iccEuclideanMetric`), the tangent space of the boundary at each endpoint is zero, so the
second fundamental form of the boundary is the zero form
(`TauCeti.boundarySecondFundamentalForm_Icc`), as on every Riemannian manifold of dimension one
(`TauCeti.boundarySecondFundamentalForm_eq_zero_of_dim_one`).
-/

public section

open Set
open scoped Manifold

namespace TauCeti

open scoped IccZeroAddOne

variable {a b : ℝ} [Fact (a < b)]

/-- The second fundamental form of the boundary of `[a, b]` is the zero form on the zero tangent
space of the boundary. -/
theorem boundarySecondFundamentalForm_Icc (q : (𝓡∂ (0 + 1)).boundary (Icc a b)) :
    boundarySecondFundamentalForm q = 0 :=
  boundarySecondFundamentalForm_eq_zero_of_dim_one q

end TauCeti
