/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Adjoints of isometric isomorphisms and of `L²` coordinate projections

Two families of adjoints of linear maps between finite-dimensional inner product spaces:

* the adjoint of an isometric isomorphism `e : E ≃ₗᵢ[𝕜] F`, viewed as a linear map, is its
  inverse (`LinearIsometryEquiv.adjoint_coe_eq_symm`). This is Mathlib's
  `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm`, stated for the coercion
  `(e : E →ₗ[𝕜] F)` in which compositions with isometric isomorphisms are usually written;
* on the `L²` product `WithLp 2 (E × F)`, the coordinate projections `WithLp.fstₗ` and
  `WithLp.sndₗ` are adjoint to the inclusions `x ↦ (x, 0)` and `y ↦ (0, y)` of the two factors.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

namespace LinearIsometryEquiv

/-- The adjoint of an isometric isomorphism, viewed as a linear map, is its inverse.

Mathlib's `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm` states this for `e.toLinearMap`. The
coercion `(e : E →ₗ[𝕜] F)` instead factors through `e.toContinuousLinearEquiv`, so neither `rw`
nor `simp` can apply that lemma to it. -/
@[simp]
theorem adjoint_coe_eq_symm (e : E ≃ₗᵢ[𝕜] F) :
    LinearMap.adjoint (e : E →ₗ[𝕜] F) = (e.symm : F →ₗ[𝕜] E) :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ by simpa using e.symm.inner_map_map x (e y)).symm

end LinearIsometryEquiv

namespace WithLp

/-- The adjoint of the first coordinate projection of an `L²` product is the inclusion
`x ↦ (x, 0)` of the first factor. -/
theorem adjoint_fstₗ :
    LinearMap.adjoint (WithLp.fstₗ 2 𝕜 E F) =
      (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E F := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply]

/-- The adjoint of the second coordinate projection of an `L²` product is the inclusion
`y ↦ (0, y)` of the second factor. -/
theorem adjoint_sndₗ :
    LinearMap.adjoint (WithLp.sndₗ 2 𝕜 E F) =
      (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E F := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply]

end WithLp
