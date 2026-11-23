/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Operator.LinearPMap.GraphSpace

/-!
# The graph inner product

Let `f : E →ₗ.[𝕜] F` be a partial linear map between inner product spaces. Its graph space
`f.graphSpace` (`TauCeti.Analysis.Normed.Operator.LinearPMap.GraphSpace`) is a subspace of the
Hilbert direct sum `WithLp 2 (E × F)`, so it carries the *graph inner product*

`⟪(x, f x), (y, f y)⟫ = ⟪x, y⟫ + ⟪f x, f y⟫`

(`LinearPMap.inner_toGraphSpace`), whose norm is the graph norm `LinearPMap.norm_toGraphSpace_sq`.
When `f` is closed and `E`, `F` are Hilbert spaces, the graph space is a Hilbert space
(`LinearPMap.IsClosed.completeSpace_graphSpace`).

## Main declarations

* `LinearPMap.inner_toGraphSpace`: the graph inner product.
* `LinearPMap.inner_graphSpace`: the inner product of the graph space in coordinates.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), §1.1 (the graph scalar product of a closed operator).
-/

public section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (f : E →ₗ.[𝕜] F)

/-- **The graph inner product.** -/
theorem inner_toGraphSpace (x y : f.domain) :
    ⟪f.toGraphSpace x, f.toGraphSpace y⟫_𝕜 = ⟪(x : E), (y : E)⟫_𝕜 + ⟪f x, f y⟫_𝕜 := by
  simp [Submodule.coe_inner, WithLp.prod_inner_apply]

/-- The inner product of two vectors of the graph space is the sum of the inner products of their
coordinates. -/
theorem inner_graphSpace (z w : f.graphSpace) :
    ⟪z, w⟫_𝕜 = ⟪(z : WithLp 2 (E × F)).fst, (w : WithLp 2 (E × F)).fst⟫_𝕜 +
      ⟪(z : WithLp 2 (E × F)).snd, (w : WithLp 2 (E × F)).snd⟫_𝕜 := by
  simp [Submodule.coe_inner, WithLp.prod_inner_apply]

end LinearPMap
