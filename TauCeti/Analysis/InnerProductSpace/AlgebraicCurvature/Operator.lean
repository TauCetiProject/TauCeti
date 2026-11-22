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
`curvatureEndomorphism r`, the rank-one operator characterization of `planeCurvature u v`, and
pullback / `O(V)`-equivariance for `TauCeti.FourTensor.ofExteriorEnd`.

## Main statements

* `TauCeti.FourTensor.ofExteriorEnd_injective`: an endomorphism of `⋀[ℝ]^2 V` is determined by its
  four-tensor.
* `TauCeti.FourTensor.ofExteriorEnd_one`: the identity on `⋀[ℝ]^2 V` corresponds to
  `constantCurvature V`.
* `TauCeti.FourTensor.scalar_ofExteriorEnd`: `scalar (ofExteriorEnd T) = 2 * trace T`.
* `TauCeti.FourTensor.curvatureEndomorphism_eq_iff_of_antisymm`: characterization of
  `curvatureEndomorphism r` on pure bivectors.
* `TauCeti.FourTensor.planeCurvature_eq_ofExteriorEnd` and
  `TauCeti.FourTensor.curvatureEndomorphism_planeCurvature`: the bivector rank-one operator
  characterization of `planeCurvature u v`.
* `ContinuousLinearMap.ofExteriorEnd_compContinuousLinearMap` and
  `LinearIsometryEquiv.ofExteriorEnd_compContinuousLinearMap`: pullback of `ofExteriorEnd` along
  continuous linear maps and equivariance under linear isometric equivalences.

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

/-- The rank-one plane curvature tensor `planeCurvature u v` is the four-tensor associated to
the rank-one operator `(u ∧ v) ⊗ (u ∧ v)` on `⋀[ℝ]^2 V`. -/
theorem planeCurvature_eq_ofExteriorEnd (u v : V) :
    planeCurvature u v =
      ofExteriorEnd
        (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![u, v])
          (ιMulti ℝ 2 ![u, v])).toLinearMap := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, ofExteriorEnd_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, inner_ιMulti_two, inner_ιMulti_two]

/-- The bivector endomorphism of `planeCurvature u v` is the rank-one operator
`ξ ↦ ⟪u ∧ v, ξ⟫ • (u ∧ v)`. -/
@[simp]
theorem curvatureEndomorphism_planeCurvature (u v : V) :
    curvatureEndomorphism (planeCurvature u v) =
      (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![u, v])
        (ιMulti ℝ 2 ![u, v])).toLinearMap := by
  rw [planeCurvature_eq_ofExteriorEnd, curvatureEndomorphism_ofExteriorEnd]

end TauCeti.FourTensor

namespace ContinuousLinearMap

open exteriorPower TauCeti.FourTensor

/-- Pulling back `ofExteriorEnd T` along a continuous linear map `f : W →L[ℝ] V` conjugates `T`
by `exteriorPower.map 2 f.toLinearMap` and its adjoint. -/
theorem ofExteriorEnd_compContinuousLinearMap {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (f : W →L[ℝ] V) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (ofExteriorEnd T).compContinuousLinearMap (fun _ ↦ f) =
      ofExteriorEnd
        (LinearMap.adjoint (exteriorPower.map 2 f.toLinearMap) ∘ₗ T ∘ₗ
          exteriorPower.map 2 f.toLinearMap) := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [compContinuousLinearMap_apply_vec, ofExteriorEnd_apply, LinearMap.comp_apply,
    LinearMap.adjoint_inner_left, map_apply_ιMulti_two, ContinuousLinearMap.coe_coe]

end ContinuousLinearMap

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
  rw [ContinuousLinearMap.ofExteriorEnd_compContinuousLinearMap,
    LinearIsometry.toLinearMap_toContinuousLinearMap, e.toLinearIsometry_toLinearMap,
    e.adjoint_exteriorPower_map]

end LinearIsometryEquiv
