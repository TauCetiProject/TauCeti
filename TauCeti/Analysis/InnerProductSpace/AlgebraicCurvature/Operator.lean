/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Further properties of `TauCeti.FourTensor.ofExteriorEnd`

This file supplements `TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare` with
injectivity, identity and scalar-contraction evaluations, characterization of
`curvatureEndomorphism r`, and `O(V)`-equivariance for `TauCeti.FourTensor.ofExteriorEnd`.

## Main statements

* `TauCeti.FourTensor.ofExteriorEnd_injective`: an endomorphism of `⋀[ℝ]^2 V` is determined by its
  four-tensor.
* `TauCeti.FourTensor.ofExteriorEnd_one`: the identity on `⋀[ℝ]^2 V` corresponds to
  `constantCurvature V`.
* `TauCeti.FourTensor.scalar_ofExteriorEnd`: `scalar (ofExteriorEnd T) = 2 * trace T`.
* `LinearIsometryEquiv.ofExteriorEnd_compContinuousLinearMap`: equivariance under linear isometric
  equivalences.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. 167 (2008), 1079–1097, Section 2.
-/

public section

open exteriorPower
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- An endomorphism of `⋀[ℝ]^2 V` is uniquely determined by its four-tensor. -/
theorem ofExteriorEnd_injective : Function.Injective (ofExteriorEnd (V := V)) :=
  Function.LeftInverse.injective curvatureEndomorphism_ofExteriorEnd

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` vanishes iff the endomorphism does. -/
@[simp]
theorem ofExteriorEnd_eq_zero_iff {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    ofExteriorEnd T = 0 ↔ T = 0 :=
  map_eq_zero_iff ofExteriorEnd ofExteriorEnd_injective

/-- The identity endomorphism of `⋀[ℝ]^2 V` maps to `constantCurvature V`. -/
@[simp]
theorem ofExteriorEnd_one :
    ofExteriorEnd (1 : Module.End ℝ (⋀[ℝ]^2 V)) = constantCurvature V := by
  simpa only [curvatureEndomorphism_constantCurvature, Module.End.one_eq_id] using
    (isAlgebraicCurvature_constantCurvature (V := V)).ofExteriorEnd_curvatureEndomorphism

/-- The scalar contraction of `ofExteriorEnd T` is twice the trace of `T` on `⋀[ℝ]^2 V`. -/
@[simp]
theorem scalar_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    scalar (ofExteriorEnd T) = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) T := by
  rw [scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm
    (ofExteriorEnd_antisymm_first T) (ofExteriorEnd_antisymm_last T),
    curvatureEndomorphism_ofExteriorEnd]

/-- Characterization of `curvatureEndomorphism r` on pure bivectors for a pair-antisymmetric
four-tensor `r`. -/
theorem curvatureEndomorphism_eq_iff_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism r = T ↔
      ∀ u v z w, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  ⟨by rintro rfl u v z w; exact inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂ u v z w,
   fun h ↦ exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
     rw [inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂, h]⟩

/-- Characterization of `curvatureEndomorphism r` on pure bivectors for an algebraic curvature
tensor `r`. -/
theorem IsAlgebraicCurvature.curvatureEndomorphism_eq_iff {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism r = T ↔
      ∀ u v z w, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  curvatureEndomorphism_eq_iff_of_antisymm hr.antisymm_first hr.antisymm_last T

end TauCeti.FourTensor

namespace LinearIsometryEquiv

open exteriorPower TauCeti.FourTensor

/-- Pulling back `ofExteriorEnd T` along a linear isometric equivalence conjugates `T` by the
induced exterior-square isometry. -/
theorem ofExteriorEnd_compContinuousLinearMap {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (ofExteriorEnd T).compContinuousLinearMap (fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      ofExteriorEnd
        ((exteriorPower.map 2 e.symm.toLinearMap) ∘ₗ T ∘ₗ
          (exteriorPower.map 2 e.toLinearMap)) := by
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec, ofExteriorEnd_apply, ofExteriorEnd_apply,
    e.inner_conj_exteriorPowerMap]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    map_apply_ιMulti_two, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

end LinearIsometryEquiv
