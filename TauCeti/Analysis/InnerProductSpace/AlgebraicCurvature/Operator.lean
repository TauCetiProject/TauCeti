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
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Four-tensors induced by endomorphisms of the exterior square

On a finite-dimensional real inner product space `V`, every endomorphism `T` of the second exterior
power `⋀[ℝ]^2 V` determines a four-tensor `TauCeti.FourTensor.ofExteriorEnd T` by

`ofExteriorEnd T ![u, v, z, w] = ⟪T (u ∧ v), z ∧ w⟫`.

This map is injective, lands in the four-tensors antisymmetric in their first and last pairs,
carries the identity endomorphism to `TauCeti.FourTensor.constantCurvature V`, and sends symmetric
endomorphisms to pair-interchange-symmetric four-tensors; the algebraic curvature tensors correspond
precisely to the self-adjoint endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi identity.
Its scalar contraction is twice the trace of `T` on `⋀[ℝ]^2 V`.

It is a right inverse to `TauCeti.FourTensor.curvatureEndomorphism` (defined in
`TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare`), and on four-tensors
already antisymmetric in both pairs — in particular on `algebraicCurvatureSubmodule V` — the two
maps are two-sided inverses.

## Main definitions

* `TauCeti.FourTensor.ofExteriorEnd`: the four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` of an
  endomorphism `T` of `⋀[ℝ]^2 V`.

## Main statements

* `TauCeti.FourTensor.ofExteriorEnd_injective`: an endomorphism of `⋀[ℝ]^2 V` is determined by its
  four-tensor.
* `TauCeti.FourTensor.ofExteriorEnd_one`: the identity on `⋀[ℝ]^2 V` corresponds to
  `constantCurvature V`.
* `TauCeti.FourTensor.ofExteriorEnd_swap_pairs_iff`: pair interchange of `ofExteriorEnd T` is
  equivalent to symmetry of `T`.
* `TauCeti.FourTensor.isAlgebraicCurvature_ofExteriorEnd_iff`: `ofExteriorEnd T` is an algebraic
  curvature tensor iff `IsAlgebraicCurvatureEndomorphism T`.
* `TauCeti.FourTensor.curvatureEndomorphism_ofExteriorEnd` and
  `TauCeti.FourTensor.ofExteriorEnd_curvatureEndomorphism_of_antisymm`: inverse relations on
  pair-antisymmetric four-tensors.
* `LinearIsometryEquiv.ofExteriorEnd_compContinuousLinearMap`: equivariance under linear isometric
  equivalences.
* `TauCeti.FourTensor.scalar_ofExteriorEnd`: `scalar (ofExteriorEnd T) = 2 * trace T`.

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

/-- The four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` associated to an endomorphism `T` of the
exterior square `⋀[ℝ]^2 V`. With this convention the identity on `⋀[ℝ]^2 V` maps to
`constantCurvature V`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V :=
  fourTensorOfExteriorBilin.comp TauCeti.bilinFormToEnd.symm.toLinearMap

/-- Evaluation of the four-tensor associated to an endomorphism of `⋀[ℝ]^2 V`. -/
@[simp]
theorem ofExteriorEnd_apply (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofExteriorEnd]

/-- An endomorphism of `⋀[ℝ]^2 V` is uniquely determined by its four-tensor. -/
theorem ofExteriorEnd_injective : Function.Injective (ofExteriorEnd (V := V)) := by
  intro S T h
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  simpa only [ofExteriorEnd_apply] using DFunLike.congr_fun h ![u, v, z, w]

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` vanishes iff the endomorphism does. -/
@[simp]
theorem ofExteriorEnd_eq_zero_iff {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    ofExteriorEnd T = 0 ↔ T = 0 :=
  map_eq_zero_iff ofExteriorEnd ofExteriorEnd_injective

/-- The identity endomorphism of `⋀[ℝ]^2 V` maps to `constantCurvature V`. -/
@[simp]
theorem ofExteriorEnd_one :
    ofExteriorEnd (1 : Module.End ℝ (⋀[ℝ]^2 V)) = constantCurvature V := by
  refine ext_vec fun u v z w ↦ ?_
  rw [ofExteriorEnd_apply, constantCurvature_apply]
  simpa using inner_ιMulti_two u v z w

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its first pair. -/
theorem ofExteriorEnd_antisymm_first (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![v, u, z, w] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, ιMulti_two_swap v u, map_neg, inner_neg_left]

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its last pair. -/
theorem ofExteriorEnd_antisymm_last (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![u, v, w, z] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, ιMulti_two_swap w z, inner_neg_right]

/-- Pair-interchange symmetry of `ofExteriorEnd T` is equivalent to symmetry of `T` on
`⋀[ℝ]^2 V`. -/
theorem ofExteriorEnd_swap_pairs_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (∀ u v z w, ofExteriorEnd T ![u, v, z, w] = ofExteriorEnd T ![z, w, u, v]) ↔
      T.IsSymmetric := by
  refine ⟨fun h a b ↦ ?_, fun h u v z w ↦ by
    simp only [ofExteriorEnd_apply]; rw [h, real_inner_comm]⟩
  have hbil : (innerₗ (⋀[ℝ]^2 V)).compl₁₂ T LinearMap.id = (innerₗ (⋀[ℝ]^2 V)).compl₂ T :=
    exteriorPower.linearMap_ext_ιMulti_two fun u v ↦
      exteriorPower.linearMap_ext_ιMulti_two fun z w ↦ by
        simp only [LinearMap.compl₁₂_apply, LinearMap.compl₂_apply, LinearMap.id_apply,
          innerₗ_apply_apply]
        rw [real_inner_comm (T (ιMulti ℝ 2 ![z, w]))]
        simpa only [ofExteriorEnd_apply] using h u v z w
  simpa using LinearMap.congr_fun₂ hbil a b

/-- `ofExteriorEnd T` is an algebraic curvature tensor iff `IsAlgebraicCurvatureEndomorphism T`. -/
theorem isAlgebraicCurvature_ofExteriorEnd_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    IsAlgebraicCurvature (ofExteriorEnd T) ↔ IsAlgebraicCurvatureEndomorphism T :=
  ⟨fun h ↦ ⟨(ofExteriorEnd_swap_pairs_iff T).mp h.swap_pairs, fun u v z w ↦ by
      simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w⟩,
   fun h ↦ ⟨ofExteriorEnd_antisymm_first T, ofExteriorEnd_antisymm_last T,
     (ofExteriorEnd_swap_pairs_iff T).mpr h.isSymmetric, fun u v z w ↦ by
       simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w⟩⟩

/-- `curvatureEndomorphism` is a left inverse to `ofExteriorEnd`. -/
@[simp]
theorem curvatureEndomorphism_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism (ofExteriorEnd T) = T :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    rw [inner_curvatureEndomorphism_ιMulti_of_antisymm (ofExteriorEnd_antisymm_first T)
      (ofExteriorEnd_antisymm_last T), ofExteriorEnd_apply]

/-- The scalar contraction of `ofExteriorEnd T` is twice the trace of `T` on `⋀[ℝ]^2 V`. -/
theorem scalar_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    scalar (ofExteriorEnd T) = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) T := by
  rw [scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm
    (ofExteriorEnd_antisymm_first T) (ofExteriorEnd_antisymm_last T),
    curvatureEndomorphism_ofExteriorEnd]

/-- On pair-antisymmetric four-tensors, `ofExteriorEnd` and `curvatureEndomorphism` are inverses. -/
theorem ofExteriorEnd_curvatureEndomorphism_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ofExteriorEnd (curvatureEndomorphism r) = r := by
  refine ext_vec fun u v z w ↦ ?_
  rw [ofExteriorEnd_apply, inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂]

/-- On bivector-symmetric four-tensors, `ofExteriorEnd (curvatureEndomorphism r) = r`. -/
@[simp]
theorem IsBivectorSymmetric.ofExteriorEnd_curvatureEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    ofExteriorEnd (curvatureEndomorphism r) = r :=
  ofExteriorEnd_curvatureEndomorphism_of_antisymm hr.antisymm_first hr.antisymm_last

/-- On algebraic curvature tensors, `ofExteriorEnd (curvatureEndomorphism r) = r`. -/
@[simp]
theorem IsAlgebraicCurvature.ofExteriorEnd_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ofExteriorEnd (curvatureEndomorphism r) = r :=
  hr.isBivectorSymmetric.ofExteriorEnd_curvatureEndomorphism

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
    e.inner_conj_map]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    map_apply_ιMulti_two, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

end LinearIsometryEquiv
