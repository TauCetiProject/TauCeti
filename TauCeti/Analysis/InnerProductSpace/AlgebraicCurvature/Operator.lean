/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Algebraic curvature tensors and endomorphisms of the exterior square

On a finite-dimensional real inner product space `V`, every endomorphism `T` of the second exterior
power `⋀[ℝ]^2 V` determines a four-tensor `TauCeti.FourTensor.ofExteriorEnd T` by

`ofExteriorEnd T ![u, v, z, w] = ⟪T (u ∧ v), z ∧ w⟫`.

This map is injective, lands in the four-tensors antisymmetric in their first and last pairs,
carries the identity endomorphism to `TauCeti.FourTensor.constantCurvature V`, and sends symmetric
endomorphisms to pair-interchange-symmetric four-tensors; the algebraic curvature tensors correspond
precisely to the self-adjoint endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi identity.
Its scalar contraction is twice the trace of `T` on `⋀[ℝ]^2 V`, reflecting the factor of `2`
between ordered and unordered orthonormal bivector sums.

In the reverse direction, `TauCeti.FourTensor.toExteriorEnd` antisymmetrizes any four-tensor in its
first and last pairs and descends the resulting pair-alternating form to an endomorphism of
`⋀[ℝ]^2 V`. It is a linear retraction of `ofExteriorEnd`, and on four-tensors already antisymmetric
in both pairs — in particular on `algebraicCurvatureSubmodule V` — the two maps are inverses,
equivariant under linear isometric equivalences.

## Main definitions

* `TauCeti.FourTensor.ofExteriorEnd`: the four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` of an
  endomorphism `T` of `⋀[ℝ]^2 V`.
* `TauCeti.FourTensor.toExteriorEnd`: the endomorphism of `⋀[ℝ]^2 V` obtained by
  pair-antisymmetrizing a four-tensor and descending via `LinearMap.exteriorSquareBilinear`.

## Main statements

* `TauCeti.FourTensor.ofExteriorEnd_injective`: an endomorphism of `⋀[ℝ]^2 V` is determined by its
  four-tensor.
* `TauCeti.FourTensor.ofExteriorEnd_one` and `TauCeti.FourTensor.toExteriorEnd_constantCurvature`:
  the identity on `⋀[ℝ]^2 V` corresponds to `constantCurvature V`.
* `TauCeti.FourTensor.ofExteriorEnd_swap_pairs_iff`: pair interchange of `ofExteriorEnd T` is
  equivalent to symmetry of `T`.
* `TauCeti.FourTensor.isAlgebraicCurvature_ofExteriorEnd_iff`: `ofExteriorEnd T` is an algebraic
  curvature tensor iff `T` is symmetric and satisfies the first Bianchi identity on pure wedges.
* `TauCeti.FourTensor.toExteriorEnd_ofExteriorEnd` and
  `TauCeti.FourTensor.ofExteriorEnd_toExteriorEnd_of_antisymm`: inverse relations on
  pair-antisymmetric four-tensors.
* `TauCeti.FourTensor.ofExteriorEnd_compContinuousLinearMap_linearIsometryEquiv` and
  `TauCeti.FourTensor.toExteriorEnd_compContinuousLinearMap_linearIsometryEquiv`: equivariance under
  linear isometric equivalences.
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

section PairAntisymm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pair-antisymmetrization of a four-tensor `r`:
`(u, v, z, w) ↦ (1 / 4) (r(u, v, z, w) - r(v, u, z, w) - r(u, v, w, z) + r(v, u, w, z))`,
as a curried four-linear map. -/
private def pairAntisymm (r : FourTensor V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ (1 / 4 : ℝ) *
        (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]))
      (fun _ _ _ ↦ by simp only [apply_add_third, apply_add_fourth]; ring)
      (fun _ _ _ ↦ by simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring)
      (fun _ _ _ ↦ by simp only [apply_add_third, apply_add_fourth]; ring)
      (fun _ _ _ ↦ by simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring))
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first,
      apply_add_second]; ring)
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
      apply_smul_first, apply_smul_second]; ring)
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first,
      apply_add_second]; ring)
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
      apply_smul_first, apply_smul_second]; ring)

private theorem pairAntisymm_apply (r : FourTensor V) (u v z w : V) :
    pairAntisymm r u v z w =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) :=
  (rfl)

private def exteriorSquareForm (r : FourTensor V) :
    LinearMap.BilinForm ℝ (⋀[ℝ]^2 V) :=
  (pairAntisymm r).exteriorSquareBilinear
    (fun _ _ _ ↦ by simp only [pairAntisymm_apply]; ring)
    -- Ascribe `IsAlt` explicitly so `exteriorSquareBilinear_ιMulti_ιMulti` matches.
    (fun u v ↦ show (pairAntisymm r u v).IsAlt from fun _ ↦ by simp only [pairAntisymm_apply]; ring)

private theorem exteriorSquareForm_ιMulti (r : FourTensor V) (u v z w : V) :
    exteriorSquareForm r (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w]) =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) := by
  rw [exteriorSquareForm, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  rfl

end PairAntisymm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The curried four-linear map `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` associated to an endomorphism
`T` of `⋀[ℝ]^2 V`. -/
private def ofExteriorEndLinear (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫)
      (fun _ _ _ ↦ by rw [ιMulti_two_add_left, inner_add_right])
      (fun _ _ _ ↦ by rw [ιMulti_two_smul_left, real_inner_smul_right, smul_eq_mul])
      (fun _ _ _ ↦ by rw [ιMulti_two_add_right, inner_add_right])
      (fun _ _ _ ↦ by rw [ιMulti_two_smul_right, real_inner_smul_right, smul_eq_mul]))
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
      ιMulti_two_add_left, map_add, inner_add_left])
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
      ιMulti_two_smul_left, map_smul, real_inner_smul_left])
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
      ιMulti_two_add_right, map_add, inner_add_left])
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
      ιMulti_two_smul_right, map_smul, real_inner_smul_left])

/-- The four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` associated to an endomorphism `T` of the
exterior square `⋀[ℝ]^2 V`. With this convention the identity on `⋀[ℝ]^2 V` maps to
`constantCurvature V`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun T := ofLinearMap₄ (ofExteriorEndLinear T)
  map_add' _ _ := by ext _; simp [ofExteriorEndLinear, inner_add_left]
  map_smul' _ _ := by ext _; simp [ofExteriorEndLinear, real_inner_smul_left]

/-- Evaluation of the four-tensor associated to an endomorphism of `⋀[ℝ]^2 V`. -/
@[simp]
theorem ofExteriorEnd_apply (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofExteriorEnd, ofExteriorEndLinear]

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
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, ofExteriorEnd_apply, constantCurvature_apply]
  simpa using inner_ιMulti_two (m 0) (m 1) (m 2) (m 3)

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its first pair. -/
theorem ofExteriorEnd_antisymm_first (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![v, u, z, w] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, ιMulti_two_swap u v, map_neg, inner_neg_left]

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its last pair. -/
theorem ofExteriorEnd_antisymm_last (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![u, v, w, z] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, ιMulti_two_swap z w, inner_neg_right]

/-- Pair-interchange symmetry of `ofExteriorEnd T` is equivalent to symmetry of `T` on
`⋀[ℝ]^2 V`. -/
theorem ofExteriorEnd_swap_pairs_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (∀ u v z w, ofExteriorEnd T ![u, v, z, w] = ofExteriorEnd T ![z, w, u, v]) ↔
      T.IsSymmetric := by
  refine ⟨fun h a b ↦ ?_, fun h u v z w ↦ by
    simp only [ofExteriorEnd_apply]; rw [h, real_inner_comm]⟩
  have hbil : (innerₗ (⋀[ℝ]^2 V)).compl₁₂ T LinearMap.id = (innerₗ (⋀[ℝ]^2 V)).compl₂ T :=
    exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦
      exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
        have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
        have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
        simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
          LinearMap.compl₂_apply, LinearMap.id_apply, innerₗ_apply_apply]
        rw [hu, hv, real_inner_comm (T (ιMulti ℝ 2 ![v 0, v 1]))]
        simpa only [ofExteriorEnd_apply] using h (u 0) (u 1) (v 0) (v 1)))
  simpa using LinearMap.congr_fun₂ hbil a b

/-- `ofExteriorEnd T` is an algebraic curvature tensor iff `T` is symmetric and satisfies the first
Bianchi identity on pure bivectors. -/
theorem isAlgebraicCurvature_ofExteriorEnd_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    IsAlgebraicCurvature (ofExteriorEnd T) ↔
      T.IsSymmetric ∧
        ∀ u v z w,
          ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ +
          ⟪T (ιMulti ℝ 2 ![v, z]), ιMulti ℝ 2 ![u, w]⟫ +
          ⟪T (ιMulti ℝ 2 ![z, u]), ιMulti ℝ 2 ![v, w]⟫ = 0 := by
  refine ⟨fun h ↦ ⟨(ofExteriorEnd_swap_pairs_iff T).mp h.swap_pairs, fun u v z w ↦ by
      simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w⟩,
    fun ⟨hsym, hcyc⟩ ↦ ⟨ofExteriorEnd_antisymm_first T, ofExteriorEnd_antisymm_last T,
      (ofExteriorEnd_swap_pairs_iff T).mpr hsym, fun u v z w ↦ by
        simpa only [ofExteriorEnd_apply] using hcyc u v z w⟩⟩

private theorem inner_conj_exteriorPower_map {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (T : Module.End ℝ (⋀[ℝ]^2 V)) (x y : ⋀[ℝ]^2 W) :
    ⟪(exteriorPower.map 2 e.symm.toLinearMap ∘ₗ T ∘ₗ exteriorPower.map 2 e.toLinearMap) x, y⟫ =
      ⟪T (exteriorPower.map 2 e.toLinearMap x), exteriorPower.map 2 e.toLinearMap y⟫ := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← exteriorPower.inner_map_map e.toLinearIsometry]
  have hcomp : exteriorPower.map 2 e.toLinearMap ∘ₗ exteriorPower.map 2 e.symm.toLinearMap =
      LinearMap.id := by
    rw [← exteriorPower.map_comp,
      show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id by ext v; simp,
      exteriorPower.map_id]
  exact congrArg (⟪·, _⟫) (LinearMap.congr_fun hcomp _)

/-- Pulling back `ofExteriorEnd T` along a linear isometric equivalence conjugates `T` by the
induced exterior-square isometry. -/
theorem ofExteriorEnd_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (ofExteriorEnd T).compContinuousLinearMap (fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      ofExteriorEnd
        ((exteriorPower.map 2 e.symm.toLinearMap) ∘ₗ T ∘ₗ
          (exteriorPower.map 2 e.toLinearMap)) := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec, ofExteriorEnd_apply, ofExteriorEnd_apply,
    inner_conj_exteriorPower_map]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    map_apply_ιMulti_two, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

/-- The scalar contraction of `ofExteriorEnd T` is twice the trace of `T` on `⋀[ℝ]^2 V`. -/
theorem scalar_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    scalar (ofExteriorEnd T) = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) T := by
  let b := stdOrthonormalBasis ℝ V
  rw [scalar_apply_orthonormalBasis b, ← b.sum_inner_ιMulti_two_eq_two_mul_trace T,
    Finset.sum_comm]
  simp only [ofExteriorEnd_apply]

/-- The endomorphism of `⋀[ℝ]^2 V` associated to a four-tensor `r`, obtained by
pair-antisymmetrizing `r` and descending to `⋀[ℝ]^2 V`. On any four-tensor antisymmetric in both
pairs (in particular on every algebraic curvature tensor),
`⟪toExteriorEnd r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`, so `ofExteriorEnd` and `toExteriorEnd` are
inverses there. -/
def toExteriorEnd : FourTensor V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun r :=
    (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 V)).symm.toLinearEquiv.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ exteriorSquareForm r)
  map_add' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      LinearMap.add_apply, inner_add_left, exteriorSquareForm_ιMulti, add_apply]; ring
  map_smul' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      LinearMap.smul_apply, RingHom.id_apply, real_inner_smul_left, exteriorSquareForm_ιMulti,
      smul_apply, smul_eq_mul]; ring

/-- On pure bivectors, `toExteriorEnd r` evaluates the pair-antisymmetrization of `r`. -/
theorem inner_toExteriorEnd_ιMulti (r : FourTensor V) (u v z w : V) :
    ⟪toExteriorEnd r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) := by
  simp only [toExteriorEnd, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
    exteriorSquareForm_ιMulti]

/-- For a four-tensor antisymmetric in both pairs, `toExteriorEnd r` pairs on pure bivectors as
`r`. -/
theorem inner_toExteriorEnd_ιMulti_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    ⟪toExteriorEnd r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  rw [inner_toExteriorEnd_ιMulti, h₁ v u z w, h₂ u v w z, h₁ v u w z, h₂ u v w z]
  ring

/-- For an algebraic curvature tensor `r`, `⟪toExteriorEnd r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
@[simp]
theorem IsAlgebraicCurvature.inner_toExteriorEnd_ιMulti {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪toExteriorEnd r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  inner_toExteriorEnd_ιMulti_of_antisymm hr.antisymm_first hr.antisymm_last u v z w

/-- `toExteriorEnd` is a left inverse to `ofExteriorEnd`. -/
@[simp]
theorem toExteriorEnd_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    toExteriorEnd (ofExteriorEnd T) = T :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    rw [inner_toExteriorEnd_ιMulti_of_antisymm (ofExteriorEnd_antisymm_first T)
      (ofExteriorEnd_antisymm_last T), ofExteriorEnd_apply]

/-- On pair-antisymmetric four-tensors, `ofExteriorEnd` and `toExteriorEnd` are inverses. -/
theorem ofExteriorEnd_toExteriorEnd_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ofExteriorEnd (toExteriorEnd r) = r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, ofExteriorEnd_apply, inner_toExteriorEnd_ιMulti_of_antisymm h₁ h₂]

/-- On algebraic curvature tensors, `ofExteriorEnd (toExteriorEnd r) = r`. -/
@[simp]
theorem IsAlgebraicCurvature.ofExteriorEnd_toExteriorEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ofExteriorEnd (toExteriorEnd r) = r :=
  ofExteriorEnd_toExteriorEnd_of_antisymm hr.antisymm_first hr.antisymm_last

/-- `toExteriorEnd` sends `constantCurvature V` to the identity on `⋀[ℝ]^2 V`. -/
@[simp]
theorem toExteriorEnd_constantCurvature :
    toExteriorEnd (constantCurvature V) = 1 := by
  rw [← ofExteriorEnd_one, toExteriorEnd_ofExteriorEnd]

/-- Pair-interchange symmetry of `r` makes `toExteriorEnd r` a symmetric endomorphism of
`⋀[ℝ]^2 V`. -/
theorem isSymmetric_toExteriorEnd {r : FourTensor V}
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    (toExteriorEnd r).IsSymmetric := by
  rw [← ofExteriorEnd_swap_pairs_iff]
  intro u v z w
  simp only [ofExteriorEnd_apply, inner_toExteriorEnd_ιMulti]
  rw [hswap u v z w, hswap v u z w, hswap u v w z, hswap v u w z]
  ring

/-- The curvature endomorphism of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymmetric_toExteriorEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (toExteriorEnd r).IsSymmetric :=
  FourTensor.isSymmetric_toExteriorEnd hr.swap_pairs

/-- Characterization of `toExteriorEnd r` on pure bivectors for a pair-antisymmetric four-tensor
`r`. -/
theorem toExteriorEnd_eq_iff_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    toExteriorEnd r = T ↔
      ∀ u v z w, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  ⟨by rintro rfl u v z w; exact inner_toExteriorEnd_ιMulti_of_antisymm h₁ h₂ u v z w,
   fun h ↦ exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
     rw [inner_toExteriorEnd_ιMulti_of_antisymm h₁ h₂, h]⟩

/-- Characterization of `toExteriorEnd r` on pure bivectors for an algebraic curvature tensor
`r`. -/
theorem IsAlgebraicCurvature.toExteriorEnd_eq_iff {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    toExteriorEnd r = T ↔
      ∀ u v z w, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  toExteriorEnd_eq_iff_of_antisymm hr.antisymm_first hr.antisymm_last T

/-- `toExteriorEnd` is equivariant under linear isometric equivalences. -/
theorem toExteriorEnd_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    toExteriorEnd
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (exteriorPower.map 2 e.symm.toLinearMap) ∘ₗ toExteriorEnd r ∘ₗ
        (exteriorPower.map 2 e.toLinearMap) :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    rw [inner_toExteriorEnd_ιMulti, inner_conj_exteriorPower_map]
    simp only [compContinuousLinearMap_apply_vec, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, map_apply_ιMulti_two, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, inner_toExteriorEnd_ιMulti]

/-- For a four-tensor antisymmetric in its first pair, its scalar contraction is twice the trace of
its exterior-square endomorphism. -/
theorem scalar_eq_two_mul_trace_toExteriorEnd_of_antisymm_first {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (toExteriorEnd r) := by
  let b := stdOrthonormalBasis ℝ V
  rw [scalar_apply_orthonormalBasis b, ← b.sum_inner_ιMulti_two_eq_two_mul_trace (toExteriorEnd r)]
  simp only [inner_toExteriorEnd_ιMulti]
  have hterm (i j) :
      r ![b i, b j, b i, b j] - r ![b j, b i, b i, b j] -
        r ![b i, b j, b j, b i] + r ![b j, b i, b j, b i] =
      2 * r ![b i, b j, b i, b j] + 2 * r ![b j, b i, b j, b i] := by
    rw [h₁ (b j) (b i) (b i) (b j), h₁ (b i) (b j) (b j) (b i)]; ring
  simp_rw [hterm]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, r ![b j, b i, b j, b i]) = ∑ i, ∑ j, r ![b i, b j, b i, b j] from
    Finset.sum_comm, Finset.sum_comm]
  ring

/-- The scalar contraction of an algebraic curvature tensor is twice the trace of its curvature
endomorphism. -/
theorem IsAlgebraicCurvature.scalar_eq_two_mul_trace_toExteriorEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (toExteriorEnd r) :=
  scalar_eq_two_mul_trace_toExteriorEnd_of_antisymm_first hr.antisymm_first

end TauCeti.FourTensor
