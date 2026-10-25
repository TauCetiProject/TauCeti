/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Adjoints of linear maps

For bounded operators between complete inner product spaces, the adjoint takes values in the
orthogonal complement of the kernel (`ContinuousLinearMap.adjoint_apply_mem_orthogonal_ker`).
For a continuous linear equivalence between complete inner product spaces, the adjoint is
bijective (`ContinuousLinearEquiv.adjoint_bijective`).
For a finite-dimensional linear isometry, the adjoint returns its image vectors to their
preimages (`LinearIsometry.adjoint_apply_apply`).

Two families of adjoints of linear maps between finite-dimensional inner product spaces:

* the adjoint of an isometric isomorphism `e : E ≃ₗᵢ[𝕜] F`, viewed as a linear map, is its
  inverse (`LinearIsometryEquiv.adjoint_coe_eq_symm`). This is Mathlib's
  `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm`, stated for the coercion
  `(e : E →ₗ[𝕜] F)` in which compositions with isometric isomorphisms are usually written;
* on the `L²` product `WithLp 2 (E × F)`, the coordinate projections `WithLp.fstₗ` and
  `WithLp.sndₗ` are adjoint to the inclusions `x ↦ (x, 0)` and `y ↦ (0, y)` of the two factors.

Finally, a pointwise bound `‖C x‖ ≤ c * ‖x‖` passes to the adjoint
(`LinearMap.norm_adjoint_apply_le`). This is the operator-norm bound `‖C†‖ ≤ ‖C‖` in pointwise
form for algebraic linear maps, deduced from Mathlib's isometry `ContinuousLinearMap.adjoint`.
If a linear map vanishes on `Tᗮ`, its adjoint takes values in `T`
(`LinearMap.adjoint_apply_mem_of_forall_mem_orthogonal`). The determinant of the adjoint of an
endomorphism is the conjugate of its determinant (`LinearMap.det_adjoint`). For a surjective
linear map, the orthogonal complement of its kernel has the dimension of the codomain
(`LinearMap.finrank_orthogonal_ker_of_surjective`).

Passing a finite-dimensional operator to continuous linear maps preserves its adjoint
(`TauCeti.toContinuousLinearMap_star`) and its normality
(the instance `TauCeti.isStarNormal_toContinuousLinearMap`).

-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

open scoped InnerProduct

/-- The adjoint of a bounded operator takes values in the orthogonal complement of its kernel. -/
theorem adjoint_apply_mem_orthogonal_ker [CompleteSpace E] [CompleteSpace F]
    (u : E →L[𝕜] F) (y : F) : (u†) y ∈ u.kerᗮ := by
  rw [orthogonal_ker]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ y)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open scoped InnerProduct

/-- The adjoint of a continuous linear equivalence between Hilbert spaces is bijective. -/
@[simp]
theorem adjoint_bijective [CompleteSpace E] [CompleteSpace F] (e : E ≃L[𝕜] F) :
    Function.Bijective ((e : E →L[𝕜] F)†) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨((e.symm : F →L[𝕜] E)†), ?_, ?_⟩
  · intro x
    simp only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      e.coe_comp_coe_symm, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  · intro x
    simp only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      e.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

end ContinuousLinearEquiv

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

namespace LinearIsometry

/-- The adjoint of a linear isometry sends each image vector back to its preimage. -/
@[simp]
theorem adjoint_apply_apply (f : E →ₗᵢ[𝕜] F) (x : E) :
    LinearMap.adjoint f.toLinearMap (f x) = x :=
  LinearMap.congr_fun (adjoint_comp_self' f) x

end LinearIsometry

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

namespace LinearMap

/-- The orthogonal complement of the kernel of a surjective linear map has the dimension of the
codomain. -/
theorem finrank_orthogonal_ker_of_surjective (f : E →ₗ[𝕜] F) (hf : Function.Surjective f) :
    Module.finrank 𝕜 (ker f)ᗮ = Module.finrank 𝕜 F := by
  rw [orthogonal_ker, finrank_range_adjoint, range_eq_top.mpr hf, finrank_top]

/-- The determinant of the adjoint of an endomorphism is the conjugate of its determinant. -/
@[simp]
theorem det_adjoint (f : E →ₗ[𝕜] E) : (adjoint f).det = star f.det := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [← det_toMatrix b.toBasis, ← det_toMatrix b.toBasis, toMatrix_adjoint b b,
    Matrix.det_conjTranspose]

/-- If `‖C x‖ ≤ c * ‖x‖` for every `x` and `0 ≤ c`, then also `‖C† y‖ ≤ c * ‖y‖` for every `y`. -/
theorem norm_adjoint_apply_le {C : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ x, ‖C x‖ ≤ c * ‖x‖) (y : F) : ‖adjoint C y‖ ≤ c * ‖y‖ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  -- The continuous adjoint is an isometry for the operator norm.
  calc ‖adjoint C y‖ = ‖ContinuousLinearMap.adjoint C.toContinuousLinearMap y‖ := by
        rw [← adjoint_toContinuousLinearMap, coe_toContinuousLinearMap']
    _ ≤ c * ‖y‖ := ContinuousLinearMap.le_of_opNorm_le _ (by
        rw [LinearIsometryEquiv.norm_map]
        exact C.toContinuousLinearMap.opNorm_le_bound hc hC) y

/-- If a linear map `A` vanishes on `Tᗮ`, then the adjoint of `A` takes values in `T`. -/
theorem adjoint_apply_mem_of_forall_mem_orthogonal {A : E →ₗ[𝕜] F} {T : Submodule 𝕜 E}
    (hA : ∀ x ∈ Tᗮ, A x = 0) (y : F) : adjoint A y ∈ T :=
  T.orthogonal_orthogonal ▸ Submodule.orthogonal_le (fun x hx ↦ hA x hx)
    (A.orthogonal_ker ▸ mem_range_self _ y)

end LinearMap

namespace TauCeti

/-- Passing a finite-dimensional operator to continuous linear maps preserves its adjoint. -/
theorem toContinuousLinearMap_star {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (T : E →ₗ[𝕜] E) :
    (star T).toContinuousLinearMap = star T.toContinuousLinearMap := by
  rw [LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]

/-- A finite-dimensional linear operator remains normal when regarded as continuous. -/
instance isStarNormal_toContinuousLinearMap {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (T : E →ₗ[𝕜] E) [IsStarNormal T] :
    IsStarNormal T.toContinuousLinearMap where
  star_comm_self := by
    rw [← toContinuousLinearMap_star]
    ext x
    exact congrArg (fun f : E →ₗ[𝕜] E => f x) (star_comm_self (x := T)).eq

end TauCeti
