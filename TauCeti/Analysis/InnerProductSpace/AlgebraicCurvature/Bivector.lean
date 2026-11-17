/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.KulkarniNomizu
public import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.Topology.Algebra.Module.SymmetricBilinear.Dimension
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.Analysis.InnerProductSpace.Dual

/-!
# Algebraic curvature tensors as symmetric bivector operators

On a finite-dimensional real inner product space `V`, every pair-antisymmetric four-tensor
`r : FourTensor V` descends to a bilinear form on the exterior square `⋀[ℝ]^2 V`, and via the
bivector Gram inner product to a linear endomorphism
`TauCeti.FourTensor.curvatureOperator r : Module.End ℝ (⋀[ℝ]^2 V)` characterized by

`⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`.

Conversely, `TauCeti.FourTensor.ofBivectorEnd` associates to every endomorphism of `⋀[ℝ]^2 V` a
pair-antisymmetric four-tensor. Under this correspondence:

* pair-interchange symmetry of `r` is self-adjointness (`LinearMap.IsSymmetric`) of the bivector
  operator;
* the constant-curvature tensor `TauCeti.FourTensor.constantCurvature V` corresponds to the
  identity `LinearMap.id : Module.End ℝ (⋀[ℝ]^2 V)`;
* the Kulkarni–Nomizu product `h ⊙ k` of two bilinear forms represented by endomorphisms `A, B`
  corresponds to `2 • exteriorPower.wedgeEnd A B`;
* the scalar contraction `TauCeti.FourTensor.scalar r` is twice the trace of `curvatureOperator r`
  on `⋀[ℝ]^2 V`;
* the algebraic curvature tensors `TauCeti.FourTensor.algebraicCurvatureSubmodule V` correspond
  isomorphically both to `TauCeti.FourTensor.bivectorCurvatureSubmodule V` and to the kernel of the
  surjective Bianchi map `Sym²(⋀² V) → ⋀⁴ V*`, giving the dimension formula
  `dim Curv(V) = n² (n² - 1) / 12` for `n = dim V`.

## Main definitions

* `TauCeti.FourTensor.curvatureOperator`: linear map `FourTensor V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V)`.
* `TauCeti.FourTensor.ofBivectorEnd`: linear map `Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V`.
* `TauCeti.FourTensor.IsBivectorCurvatureOperator` and
  `TauCeti.FourTensor.bivectorCurvatureSubmodule`: symmetric bivector operators in the kernel of
  the Bianchi sum.
* `TauCeti.FourTensor.algebraicCurvatureEquivBivector`: linear isomorphism between
  `algebraicCurvatureSubmodule V` and `bivectorCurvatureSubmodule V`.
* `TauCeti.FourTensor.bianchiMap` and `TauCeti.FourTensor.algebraicCurvatureEquivKerBianchi`:
  the Bianchi map `symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ →ₗ[ℝ] (V [⋀^Fin 4]→ₗ[ℝ] ℝ)` and the
  linear isomorphism of `algebraicCurvatureSubmodule V` with its kernel.

## Main results

* `TauCeti.FourTensor.IsAlgebraicCurvature.inner_curvatureOperator_ιMulti` and
  `TauCeti.FourTensor.curvatureOperator_ofBivectorEnd`.
* `TauCeti.FourTensor.curvatureOperator_constantCurvature`:
  `curvatureOperator (constantCurvature V) = LinearMap.id`.
* `TauCeti.FourTensor.curvatureOperator_kulkarniNomizu_of_inner`:
  `curvatureOperator (kulkarniNomizu h k) = (2 : ℝ) • exteriorPower.wedgeEnd A B`.
* `TauCeti.FourTensor.scalar_eq_two_mul_trace_curvatureOperator` and
  `TauCeti.FourTensor.two_mul_trace_curvatureOperator_comp_wedgeEnd_id`.
* `TauCeti.FourTensor.surjective_bianchiMap` and
  `TauCeti.FourTensor.finrank_algebraicCurvatureSubmodule`:
  `Module.finrank ℝ (algebraicCurvatureSubmodule W) = n ^ 2 * (n ^ 2 - 1) / 12`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 1.H.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

open LinearMap (BilinForm)
open exteriorPower
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Pair-antisymmetrization of a four-tensor as a curried four-linear map, used to extend
`curvatureOperator` linearly to all of `FourTensor V`. On pair-antisymmetric tensors it agrees
with evaluation of `r`. -/
private def pairAltLinear₄ (r : FourTensor V) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) / 4)
      (fun z₁ z₂ w ↦ by
        simp only [apply_add_third, apply_add_fourth]
        ring)
      (fun c z w ↦ by
        simp only [apply_smul_third, apply_smul_fourth]
        ring)
      (fun z w₁ w₂ ↦ by
        simp only [apply_add_third, apply_add_fourth]
        ring)
      (fun c z w ↦ by
        simp only [apply_smul_third, apply_smul_fourth]
        ring))
    (fun u₁ u₂ v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first, apply_add_second]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, apply_smul_first, apply_smul_second]
      ring)
    (fun u v₁ v₂ ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first, apply_add_second]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, apply_smul_first, apply_smul_second]
      ring)

omit [FiniteDimensional ℝ V] in
private theorem pairAltLinear₄_apply (r : FourTensor V) (u v z w : V) :
    pairAltLinear₄ r u v z w =
      (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) / 4 :=
  (rfl)

omit [FiniteDimensional ℝ V] in
private theorem pairAltLinear₄_self_first (r : FourTensor V) (u z w : V) :
    pairAltLinear₄ r u u z w = 0 := by
  rw [pairAltLinear₄_apply]
  ring

omit [FiniteDimensional ℝ V] in
private theorem pairAltLinear₄_isAlt_last (r : FourTensor V) (u v : V) :
    (pairAltLinear₄ r u v).IsAlt := fun z ↦ by
  rw [pairAltLinear₄_apply]
  ring

/-- The bilinear form on `⋀[ℝ]^2 V` descended from the pair-antisymmetrization of `r`. -/
private def exteriorBilinForm (r : FourTensor V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  (pairAltLinear₄ r).exteriorSquareBilinear (pairAltLinear₄_self_first r)
    (pairAltLinear₄_isAlt_last r)

/-- The bivector curvature operator associated to a four-tensor `r : FourTensor V`. For a
pair-antisymmetric tensor (and in particular for every algebraic curvature tensor), it is uniquely
characterized by `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
def curvatureOperator : FourTensor V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun r :=
    (InnerProductSpace.continuousLinearMapOfBilin
      (exteriorBilinForm r).toContinuousBilinearMap).toLinearMap
  map_add' r q := by
    refine linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
    have h (s : FourTensor V) :
        ⟪(InnerProductSpace.continuousLinearMapOfBilin
            (exteriorBilinForm s).toContinuousBilinearMap) (ιMulti ℝ 2 ![u, v]),
          ιMulti ℝ 2 ![z, w]⟫ =
          exteriorBilinForm s (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w]) :=
      InnerProductSpace.continuousLinearMapOfBilin_apply
        (exteriorBilinForm s).toContinuousBilinearMap (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w])
    simp only [LinearMap.add_apply, ContinuousLinearMap.coe_coe, inner_add_left, h]
    simp only [exteriorBilinForm, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti,
      pairAltLinear₄_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_apply]
    ring
  map_smul' c r := by
    refine linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
    have h (s : FourTensor V) :
        ⟪(InnerProductSpace.continuousLinearMapOfBilin
            (exteriorBilinForm s).toContinuousBilinearMap) (ιMulti ℝ 2 ![u, v]),
          ιMulti ℝ 2 ![z, w]⟫ =
          exteriorBilinForm s (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w]) :=
      InnerProductSpace.continuousLinearMapOfBilin_apply
        (exteriorBilinForm s).toContinuousBilinearMap (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w])
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, RingHom.id_apply,
      real_inner_smul_left, h]
    simp only [exteriorBilinForm, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti,
      pairAltLinear₄_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_apply, smul_eq_mul]
    ring

/-- Pairing `curvatureOperator r (u ∧ v)` with `z ∧ w` recovers the pair-antisymmetrization of
`r`. -/
theorem inner_curvatureOperator_ιMulti (r : FourTensor V) (u v z w : V) :
    ⟪curvatureOperator r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) / 4 := by
  calc
    ⟪curvatureOperator r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫
      = exteriorBilinForm r (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w]) :=
        InnerProductSpace.continuousLinearMapOfBilin_apply
          (exteriorBilinForm r).toContinuousBilinearMap (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w])
    _ = _ := by simp [exteriorBilinForm, pairAltLinear₄_apply]

/-- For a four-tensor antisymmetric in both its first and last pairs of arguments, the bivector
operator satisfies `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
theorem inner_curvatureOperator_ιMulti_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    ⟪curvatureOperator r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  rw [inner_curvatureOperator_ιMulti, h₁ v u z w, h₂ u v w z, h₁ v u w z, h₂ u v w z]
  ring

/-- For an algebraic curvature tensor `r`, `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`.
-/
theorem IsAlgebraicCurvature.inner_curvatureOperator_ιMulti {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪curvatureOperator r (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  inner_curvatureOperator_ιMulti_of_antisymm hr.antisymm_first hr.antisymm_last u v z w

/-- For a pair-antisymmetric four-tensor `r`, `curvatureOperator r` is uniquely determined by its
inner products on decomposable wedges. -/
theorem curvatureOperator_eq_iff_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z])
    (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureOperator r = T ↔
      ∀ u v z w : V, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  refine ⟨fun h u v z w ↦ h ▸ inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂ u v z w, fun h ↦ ?_⟩
  refine linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  rw [inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂, h]

/-- The bilinear map `(u, v) ↦ u ∧ v` into `⋀[ℝ]^2 V`. -/
private def wedgeTwoBilinear : V →ₗ[ℝ] V →ₗ[ℝ] ⋀[ℝ]^2 V :=
  LinearMap.mk₂ ℝ (fun u v ↦ ιMulti ℝ 2 ![u, v])
    ιMulti_two_add_left (fun c u v ↦ ιMulti_two_smul_left u v c)
    ιMulti_two_add_right (fun c u v ↦ ιMulti_two_smul_right u v c)

/-- The pair-antisymmetric four-tensor associated to an endomorphism `T` of `⋀[ℝ]^2 V`, defined by
`ofBivectorEnd T ![u, v, z, w] = ⟪T (u ∧ v), z ∧ w⟫`. -/
def ofBivectorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun T := ofLinearMap₄ <|
    LinearMap.mk₂ ℝ
      (fun u v ↦ LinearMap.mk₂ ℝ
        (fun z w ↦ ⟪T (wedgeTwoBilinear u v), wedgeTwoBilinear z w⟫)
        (fun z₁ z₂ w ↦ by simp only [map_add, LinearMap.add_apply, inner_add_right])
        (fun c z w ↦ by simp only [map_smul, LinearMap.smul_apply, real_inner_smul_right,
          smul_eq_mul])
        (fun z w₁ w₂ ↦ by simp only [map_add, inner_add_right])
        (fun c z w ↦ by simp only [map_smul, real_inner_smul_right, smul_eq_mul]))
      (fun u₁ u₂ v ↦ by
        ext z w
        simp only [LinearMap.mk₂_apply, map_add, LinearMap.add_apply, inner_add_left])
      (fun c u v ↦ by
        ext z w
        simp only [LinearMap.mk₂_apply, map_smul, LinearMap.smul_apply, real_inner_smul_left,
          smul_eq_mul])
      (fun u v₁ v₂ ↦ by
        ext z w
        simp only [LinearMap.mk₂_apply, map_add, LinearMap.add_apply, inner_add_left])
      (fun c u v ↦ by
        ext z w
        simp only [LinearMap.mk₂_apply, map_smul, LinearMap.smul_apply, real_inner_smul_left,
          smul_eq_mul])
  map_add' T S := by
    ext m
    simp only [add_apply, ofLinearMap₄_apply, LinearMap.mk₂_apply, LinearMap.add_apply,
      inner_add_left]
  map_smul' c T := by
    ext m
    simp only [smul_apply, ofLinearMap₄_apply, LinearMap.mk₂_apply, LinearMap.smul_apply,
      real_inner_smul_left, RingHom.id_apply, smul_eq_mul]

/-- Evaluation of `ofBivectorEnd T` on `(u, v, z, w)`. -/
@[simp]
theorem ofBivectorEnd_apply (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] = ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofBivectorEnd, wedgeTwoBilinear]

/-- Every four-tensor in the image of `ofBivectorEnd` is antisymmetric in its first pair. -/
theorem ofBivectorEnd_antisymm_first (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] = -ofBivectorEnd T ![v, u, z, w] := by
  have hswap : ![v, u] = ![u, v] ∘ Equiv.swap 0 1 := by funext i; fin_cases i <;> rfl
  simp only [ofBivectorEnd_apply]
  rw [hswap, (ιMulti ℝ 2).map_swap _ (by decide), map_neg, inner_neg_left, neg_neg]

/-- Every four-tensor in the image of `ofBivectorEnd` is antisymmetric in its last pair. -/
theorem ofBivectorEnd_antisymm_last (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] = -ofBivectorEnd T ![u, v, w, z] := by
  have hswap : ![w, z] = ![z, w] ∘ Equiv.swap 0 1 := by funext i; fin_cases i <;> rfl
  simp only [ofBivectorEnd_apply]
  rw [hswap, (ιMulti ℝ 2).map_swap _ (by decide), inner_neg_right, neg_neg]

/-- `curvatureOperator` is a left inverse to `ofBivectorEnd`. -/
@[simp]
theorem curvatureOperator_ofBivectorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureOperator (ofBivectorEnd T) = T := by
  rw [curvatureOperator_eq_iff_of_antisymm (ofBivectorEnd_antisymm_first T)
    (ofBivectorEnd_antisymm_last T)]
  intro u v z w
  rw [ofBivectorEnd_apply]

/-- `ofBivectorEnd` is injective. -/
theorem ofBivectorEnd_injective : Function.Injective (ofBivectorEnd (V := V)) :=
  Function.LeftInverse.injective curvatureOperator_ofBivectorEnd

/-- On pair-antisymmetric four-tensors, `ofBivectorEnd ∘ curvatureOperator` is the identity. -/
theorem ofBivectorEnd_curvatureOperator_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ofBivectorEnd (curvatureOperator r) = r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, ofBivectorEnd_apply, inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂]

/-- On algebraic curvature tensors, `ofBivectorEnd (curvatureOperator r) = r`. -/
theorem IsAlgebraicCurvature.ofBivectorEnd_curvatureOperator {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ofBivectorEnd (curvatureOperator r) = r :=
  ofBivectorEnd_curvatureOperator_of_antisymm hr.antisymm_first hr.antisymm_last

/-- The conditions for an endomorphism `T` of `⋀[ℝ]^2 V` to arise from an algebraic curvature
tensor: symmetry with respect to the bivector inner product and the first Bianchi identity. -/
structure IsBivectorCurvatureOperator (T : Module.End ℝ (⋀[ℝ]^2 V)) : Prop where
  /-- Symmetry with respect to the Gram inner product on `⋀[ℝ]^2 V`. -/
  isSymmetric : T.IsSymmetric
  /-- The first Bianchi identity on decomposable wedges. -/
  bianchi : ∀ u v z w : V,
    ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ +
      ⟪T (ιMulti ℝ 2 ![v, z]), ιMulti ℝ 2 ![u, w]⟫ +
      ⟪T (ιMulti ℝ 2 ![z, u]), ιMulti ℝ 2 ![v, w]⟫ = 0

variable (V) in
/-- The submodule of symmetric endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi
identity. -/
def bivectorCurvatureSubmodule : Submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) where
  carrier := {T | IsBivectorCurvatureOperator T}
  zero_mem' := ⟨LinearMap.IsSymmetric.zero, by simp⟩
  add_mem' {T S} hT hS :=
    ⟨hT.isSymmetric.add hS.isSymmetric, fun u v z w ↦ by
      simp only [LinearMap.add_apply, inner_add_left]
      linear_combination hT.bianchi u v z w + hS.bianchi u v z w⟩
  smul_mem' c T hT :=
    ⟨hT.isSymmetric.smul (by simp), fun u v z w ↦ by
      simp only [LinearMap.smul_apply, real_inner_smul_left]
      linear_combination c * hT.bianchi u v z w⟩

/-- Membership in `bivectorCurvatureSubmodule V` is `IsBivectorCurvatureOperator`. -/
@[simp]
theorem mem_bivectorCurvatureSubmodule {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    T ∈ bivectorCurvatureSubmodule V ↔ IsBivectorCurvatureOperator T :=
  Iff.rfl

/-- `ofBivectorEnd T` is an algebraic curvature tensor if and only if `T` is a bivector curvature
operator. -/
@[simp]
theorem isAlgebraicCurvature_ofBivectorEnd_iff {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    IsAlgebraicCurvature (ofBivectorEnd T) ↔ IsBivectorCurvatureOperator T := by
  refine ⟨fun h ↦ ⟨?_, fun u v z w ↦ by
      simpa only [ofBivectorEnd_apply] using h.cyclic_eq_zero u v z w⟩,
    fun h ↦ ⟨ofBivectorEnd_antisymm_first T, ofBivectorEnd_antisymm_last T, fun u v z w ↦ ?_,
      fun u v z w ↦ by
        simpa only [ofBivectorEnd_apply] using h.bianchi u v z w⟩⟩
  · have hadj : T.adjoint = T := linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
      rw [LinearMap.adjoint_inner_left, real_inner_comm]
      simpa only [ofBivectorEnd_apply] using (h.swap_pairs u v z w).symm
    intro x y
    rw [← LinearMap.adjoint_inner_right T x y, hadj]
  · simpa only [ofBivectorEnd_apply, real_inner_comm (ιMulti ℝ 2 ![u, v])] using
      h.isSymmetric (ιMulti ℝ 2 ![u, v]) (ιMulti ℝ 2 ![z, w])

/-- The bivector operator of an algebraic curvature tensor is a bivector curvature operator. -/
theorem IsAlgebraicCurvature.isBivectorCurvatureOperator {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    IsBivectorCurvatureOperator (curvatureOperator r) := by
  rwa [← isAlgebraicCurvature_ofBivectorEnd_iff, hr.ofBivectorEnd_curvatureOperator]

variable (V) in
/-- The canonical linear isomorphism between algebraic curvature tensors on `V` and symmetric
bivector curvature operators on `⋀[ℝ]^2 V`. -/
def algebraicCurvatureEquivBivector :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] bivectorCurvatureSubmodule V where
  toFun r := ⟨curvatureOperator r.1,
    (mem_algebraicCurvatureSubmodule.mp r.2).isBivectorCurvatureOperator⟩
  invFun T := ⟨ofBivectorEnd T.1,
    mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_ofBivectorEnd_iff.mpr T.2)⟩
  left_inv r := Subtype.ext (mem_algebraicCurvatureSubmodule.mp r.2).ofBivectorEnd_curvatureOperator
  right_inv T := Subtype.ext (curvatureOperator_ofBivectorEnd T.1)
  map_add' r q := Subtype.ext (map_add curvatureOperator r.1 q.1)
  map_smul' c r := Subtype.ext (map_smul curvatureOperator c r.1)

/-- Forgetting the submodule predicate on `algebraicCurvatureEquivBivector V r` yields
`curvatureOperator r.1`. -/
@[simp]
theorem coe_algebraicCurvatureEquivBivector (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureEquivBivector V r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureOperator r.1 :=
  (rfl)

/-- Forgetting the submodule predicate on `(algebraicCurvatureEquivBivector V).symm T` yields
`ofBivectorEnd T.1`. -/
@[simp]
theorem coe_algebraicCurvatureEquivBivector_symm (T : bivectorCurvatureSubmodule V) :
    ((algebraicCurvatureEquivBivector V).symm T : FourTensor V) = ofBivectorEnd T.1 :=
  (rfl)

/-! ### Contractions, Kulkarni–Nomizu operators, and isometric equivariance -/

/-- The constant-curvature four-tensor corresponds to the identity endomorphism of `⋀[ℝ]^2 V`. -/
@[simp]
theorem curvatureOperator_constantCurvature :
    curvatureOperator (constantCurvature V) = LinearMap.id := by
  rw [curvatureOperator_eq_iff_of_antisymm
    isAlgebraicCurvature_constantCurvature.antisymm_first
    isAlgebraicCurvature_constantCurvature.antisymm_last]
  intro u v z w
  rw [LinearMap.id_apply, inner_ιMulti_two, constantCurvature_apply]

/-- If bilinear forms `h, k : BilinForm ℝ V` are represented through the inner product by linear
endomorphisms `A, B : Module.End ℝ V`, then the bivector operator of `kulkarniNomizu h k` is
`2 • exteriorPower.wedgeEnd A B`. -/
theorem curvatureOperator_kulkarniNomizu_of_inner {h k : BilinForm ℝ V} {A B : Module.End ℝ V}
    (hh : ∀ u v, h u v = ⟪A u, v⟫) (hk : ∀ u v, k u v = ⟪B u, v⟫) :
    curvatureOperator (kulkarniNomizu h k) = (2 : ℝ) • wedgeEnd A B := by
  have h₁ : ∀ u v z w, kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![v, u, z, w] :=
    fun u v z w ↦ by
      simp only [kulkarniNomizu_apply_eq]
      exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first h k u v w z
  have h₂ : ∀ u v z w, kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![u, v, w, z] :=
    fun u v z w ↦ by
      simp only [kulkarniNomizu_apply_eq]
      exact LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k u v w z
  rw [curvatureOperator_eq_iff_of_antisymm h₁ h₂]
  intro u v z w
  rw [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti_two, kulkarniNomizu_apply]
  simp only [hh, hk]
  ring

/-- Pulling back a four-tensor along a linear isometric equivalence `e : W ≃ₗᵢ[ℝ] V` conjugates its
bivector curvature operator by `⋀² e`. -/
theorem curvatureOperator_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    curvatureOperator (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (exteriorPower.map 2 e.symm.toLinearIsometry.toLinearMap).comp
        ((curvatureOperator r).comp (exteriorPower.map 2 e.toLinearIsometry.toLinearMap)) := by
  refine linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  rw [inner_curvatureOperator_ιMulti, LinearMap.comp_apply, LinearMap.comp_apply]
  have he (a b : W) :
      exteriorPower.map 2 e.toLinearIsometry.toLinearMap (ιMulti ℝ 2 ![a, b]) =
        ιMulti ℝ 2 ![e a, e b] := by
    rw [map_apply_ιMulti]
    congr 1; funext i; fin_cases i <;> rfl
  have hsymm (x : ⋀[ℝ]^2 V) (y : ⋀[ℝ]^2 W) :
      ⟪exteriorPower.map 2 e.symm.toLinearIsometry.toLinearMap x, y⟫ =
        ⟪x, exteriorPower.map 2 e.toLinearIsometry.toLinearMap y⟫ := by
    rw [← inner_map_map e.toLinearIsometry, ← LinearMap.comp_apply, ← map_comp]
    have hid : e.toLinearIsometry.toLinearMap.comp e.symm.toLinearIsometry.toLinearMap =
        LinearMap.id := by
      ext a; exact e.apply_symm_apply a
    rw [hid, map_id, LinearMap.id_apply]
  rw [hsymm, he, he, inner_curvatureOperator_ιMulti]
  simp only [compContinuousLinearMap_apply_vec, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]

/-- In an orthonormal basis, the Ricci contraction of a pair-antisymmetric four-tensor is the trace
of `curvatureOperator r` over two-planes spanned by the basis vectors. -/
theorem ricci_eq_sum_inner_curvatureOperator {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v : V) :
    ricci r u v = ∑ i, ⟪curvatureOperator r (ιMulti ℝ 2 ![b i, u]), ιMulti ℝ 2 ![b i, v]⟫ := by
  rw [ricci_apply_orthonormalBasis b]
  exact Finset.sum_congr rfl fun i _ ↦
    (inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂ (b i) u (b i) v).symm

/-- The scalar contraction of a pair-antisymmetric four-tensor is twice the trace of its bivector
operator on `⋀[ℝ]^2 V`. -/
theorem scalar_eq_two_mul_trace_curvatureOperator {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureOperator r) := by
  let b := stdOrthonormalBasis ℝ V
  rw [scalar_apply_orthonormalBasis b, ← b.sum_inner_ιMulti_two_eq_two_mul_trace, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    (inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂ (b i) (b j) (b i) (b j)).symm

/-- For an algebraic curvature tensor `r`, `scalar r = 2 * trace (curvatureOperator r)`. -/
theorem IsAlgebraicCurvature.scalar_eq_two_mul_trace_curvatureOperator {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureOperator r) :=
  FourTensor.scalar_eq_two_mul_trace_curvatureOperator hr.antisymm_first hr.antisymm_last

/-- Twice the trace pairing `tr(curvatureOperator r ∘ (A ∧ id))` equals the contraction
of `ricci r` against `A` in any orthonormal basis. -/
theorem two_mul_trace_curvatureOperator_comp_wedgeEnd_id {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (A : Module.End ℝ V) :
    2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureOperator r ∘ₗ wedgeEnd A LinearMap.id) =
      ∑ i, ricci r (A (b i)) (b i) := by
  rw [← b.sum_inner_ιMulti_two_eq_two_mul_trace]
  simp only [LinearMap.comp_apply, wedgeEnd_apply_ιMulti_two, LinearMap.id_apply, map_smul,
    map_add, real_inner_smul_left, inner_add_left,
    inner_curvatureOperator_ιMulti_of_antisymm h₁ h₂]
  have hswap (i j : ι) : r ![A (b i), b j, b i, b j] = r ![b j, A (b i), b j, b i] := by
    rw [h₁ (A (b i)) (b j), h₂ (b j) (A (b i)), neg_neg]
  simp_rw [hswap, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ (2 : ℝ)⁻¹ * r ![b i, A (b j), b i, b j])]
  simp_rw [← Finset.mul_sum, ← ricci_apply_orthonormalBasis b]
  linarith

/-! ### The Bianchi map and the dimension of `algebraicCurvatureSubmodule` -/

/-- The multilinear Bianchi sum `(u, v, z, w) ↦ B(u ∧ v, z ∧ w) + B(v ∧ z, u ∧ w) + B(z ∧ u, v ∧ w)`
of a symmetric bilinear form `B` on `⋀[ℝ]^2 V`. -/
private def bianchiMultilinear (B : symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
  MultilinearMap.mk'
    (fun m ↦
      B.1 (wedgeTwoBilinear (m 0) (m 1)) (wedgeTwoBilinear (m 2) (m 3)) +
        B.1 (wedgeTwoBilinear (m 1) (m 2)) (wedgeTwoBilinear (m 0) (m 3)) +
        B.1 (wedgeTwoBilinear (m 2) (m 0)) (wedgeTwoBilinear (m 1) (m 3)))
    (fun m i x y ↦ by
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Function.update_self,
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
          map_add, LinearMap.add_apply, add_apply] <;>
        ring)
    (fun m i c x ↦ by
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Function.update_self,
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
          map_smul, LinearMap.smul_apply, smul_apply, RingHom.id_apply, smul_eq_mul] <;>
        ring)

omit [FiniteDimensional ℝ V] in
private theorem wedgeTwoBilinear_self (u : V) : wedgeTwoBilinear u u = 0 :=
  (ιMulti ℝ 2).map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl (by decide)

omit [FiniteDimensional ℝ V] in
private theorem wedgeTwoBilinear_swap (u v : V) :
    wedgeTwoBilinear v u = -wedgeTwoBilinear u v := by
  have hswap : ![v, u] = ![u, v] ∘ Equiv.swap 0 1 := by funext i; fin_cases i <;> rfl
  change ιMulti ℝ 2 ![v, u] = -ιMulti ℝ 2 ![u, v]
  rw [hswap, (ιMulti ℝ 2).map_swap _ (by decide)]

private theorem cyclic_bilin_eq_zero_of_lt {U E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (w : U → U → E) (hw_self : ∀ u, w u u = 0) (hw_swap : ∀ u v, w v u = -w u v)
    (m : Fin 4 → U) {i j : Fin 4} (hm : m i = m j) (hij : i < j) :
    B (w (m 0) (m 1)) (w (m 2) (m 3)) +
      B (w (m 1) (m 2)) (w (m 0) (m 3)) +
      B (w (m 2) (m 0)) (w (m 1) (m 3)) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hm hij
  · omega
  · rw [← hm, hw_self, hw_swap (m 2) (m 0)]; simp
  · rw [← hm, hw_self, hw_swap (m 1) (m 0)]; simp
  · rw [← hm, hw_self, hsymm (w (m 2) (m 0)), hw_swap (m 1) (m 0)]; simp
  · omega
  · omega
  · rw [← hm, hw_self, hw_swap (m 1) (m 0)]; simp
  · rw [← hm, hw_self, hsymm (w (m 1) (m 2)), hw_swap (m 2) (m 1)]; simp
  · omega
  · omega
  · omega
  · rw [← hm, hw_self, hsymm (w (m 2) (m 0)), hw_swap (m 2) (m 0)]; simp
  · omega
  · omega
  · omega
  · omega

private theorem cyclic_bilin_eq_zero_of_eq {U E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (w : U → U → E) (hw_self : ∀ u, w u u = 0) (hw_swap : ∀ u v, w v u = -w u v)
    (m : Fin 4 → U) {i j : Fin 4} (hm : m i = m j) (hij : i ≠ j) :
    B (w (m 0) (m 1)) (w (m 2) (m 3)) +
      B (w (m 1) (m 2)) (w (m 0) (m 3)) +
      B (w (m 2) (m 0)) (w (m 1) (m 3)) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact cyclic_bilin_eq_zero_of_lt B hsymm w hw_self hw_swap m hm hlt
  · exact cyclic_bilin_eq_zero_of_lt B hsymm w hw_self hw_swap m hm.symm hgt

variable (V) in
/-- The linear Bianchi map `Sym²(⋀² V) → ⋀⁴ V*` sending a symmetric bilinear form `B` on
`⋀[ℝ]^2 V` to the alternating four-form
`(u, v, z, w) ↦ B(u ∧ v, z ∧ w) + B(v ∧ z, u ∧ w) + B(z ∧ u, v ∧ w)`. -/
def bianchiMap : symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ →ₗ[ℝ] (V [⋀^Fin 4]→ₗ[ℝ] ℝ) where
  toFun B :=
    { toMultilinearMap := bianchiMultilinear B
      map_eq_zero_of_eq' m i j hm hij :=
        cyclic_bilin_eq_zero_of_eq B.1
          ((mem_symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ B.1).mp B.2)
          (fun u v ↦ wedgeTwoBilinear u v) wedgeTwoBilinear_self wedgeTwoBilinear_swap m hm hij }
  map_add' B C := by
    ext m
    simp only [AlternatingMap.coe_mk, bianchiMultilinear, MultilinearMap.mk'_apply,
      Submodule.coe_add, add_apply]
    ring
  map_smul' c B := by
    ext m
    simp only [AlternatingMap.coe_mk, bianchiMultilinear, MultilinearMap.mk'_apply,
      Submodule.coe_smul_of_tower, smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Pointwise evaluation of the Bianchi map `Sym²(⋀² V) → ⋀⁴ V*` on four vectors. -/
@[simp]
theorem bianchiMap_apply (B : symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ) (m : Fin 4 → V) :
    bianchiMap V B m =
      B.1 (ιMulti ℝ 2 ![m 0, m 1]) (ιMulti ℝ 2 ![m 2, m 3]) +
        B.1 (ιMulti ℝ 2 ![m 1, m 2]) (ιMulti ℝ 2 ![m 0, m 3]) +
        B.1 (ιMulti ℝ 2 ![m 2, m 0]) (ιMulti ℝ 2 ![m 1, m 3]) := by
  simp [bianchiMap, bianchiMultilinear, wedgeTwoBilinear]

/-- **The Bianchi map `Sym²(⋀² V) → ⋀⁴ V*` is surjective**: one-third of the exterior-algebra
wedge product `(x, y) ↦ ω(x ∧ y)` is a right inverse. -/
theorem surjective_bianchiMap : Function.Surjective (bianchiMap V) := by
  intro ω
  let B₀ : BilinForm ℝ (⋀[ℝ]^2 V) :=
    (3 : ℝ)⁻¹ • ((exteriorPower.wedge ℝ V 2 2).compr₂ (alternatingMapLinearEquiv ω))
  have hB₀_apply (a b c d : V) :
      B₀ (ιMulti ℝ 2 ![a, b]) (ιMulti ℝ 2 ![c, d]) = (3 : ℝ)⁻¹ * ω ![a, b, c, d] := by
    simp only [B₀, LinearMap.smul_apply, LinearMap.compr₂_apply, wedge_ιMulti, smul_eq_mul]
    have happ : Fin.append ![a, b] ![c, d] = ![a, b, c, d] := by
      funext i; fin_cases i <;> rfl
    rw [happ, alternatingMapLinearEquiv_apply_ιMulti]
  have hB₀_symm : B₀.flip = B₀ := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦
      exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_))
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.BilinForm.flip_apply]
    have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    rw [hu, hv, hB₀_apply, hB₀_apply]
    congr 1
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
    have hperm : ![v 0, v 1, u 0, u 1] = ![u 0, u 1, v 0, v 1] ∘ σ := by
      funext i; fin_cases i <;> rfl
    have hsign : Equiv.Perm.sign σ = 1 := by decide
    rw [hperm, ω.map_perm, hsign, one_smul]
  refine ⟨⟨B₀.toContinuousBilinearMap,
    (mem_symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ _).mpr fun x y ↦ by
      simpa using LinearMap.congr_fun₂ hB₀_symm.symm x y⟩, ?_⟩
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [bianchiMap_apply]
  simp only [LinearMap.toContinuousBilinearMap_apply, hB₀_apply]
  let τ₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let τ₂ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 2
  have hp₁ : ![m 1, m 2, m 0, m 3] = ![m 0, m 1, m 2, m 3] ∘ τ₁ := by
    funext i; fin_cases i <;> rfl
  have hp₂ : ![m 2, m 0, m 1, m 3] = ![m 0, m 1, m 2, m 3] ∘ τ₂ := by
    funext i; fin_cases i <;> rfl
  have hs₁ : Equiv.Perm.sign τ₁ = 1 := by decide
  have hs₂ : Equiv.Perm.sign τ₂ = 1 := by decide
  rw [hp₁, hp₂, ω.map_perm, ω.map_perm, hs₁, hs₂, one_smul, ← hm]
  ring

private def bilinOfEnd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Module.End ℝ E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((innerₗ E).compl₁₂ T LinearMap.id).toContinuousBilinearMap

private theorem bilinOfEnd_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Module.End ℝ E) (x y : E) :
    bilinOfEnd T x y = ⟪T x, y⟫ :=
  (rfl)

variable (V) in
/-- The linear isomorphism identifying `algebraicCurvatureSubmodule V` with the kernel of the
Bianchi map `Sym²(⋀² V) → ⋀⁴ V*`. -/
def algebraicCurvatureEquivKerBianchi :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] LinearMap.ker (bianchiMap V) where
  toFun r :=
    ⟨⟨bilinOfEnd (curvatureOperator r.1),
      (mem_symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ _).mpr fun x y ↦ by
        rw [bilinOfEnd_apply, bilinOfEnd_apply,
          (mem_algebraicCurvatureSubmodule.mp r.2).isBivectorCurvatureOperator.isSymmetric x y,
          real_inner_comm]⟩,
      LinearMap.mem_ker.mpr <| AlternatingMap.ext fun m ↦ by
        simp only [bianchiMap_apply, bilinOfEnd_apply, zero_apply]
        exact (mem_algebraicCurvatureSubmodule.mp r.2).isBivectorCurvatureOperator.bianchi
          (m 0) (m 1) (m 2) (m 3)⟩
  invFun B :=
    ⟨ofBivectorEnd (InnerProductSpace.continuousLinearMapOfBilin B.1.1).toLinearMap,
      mem_algebraicCurvatureSubmodule.mpr <| isAlgebraicCurvature_ofBivectorEnd_iff.mpr
        ⟨InnerProductSpace.isSymmetric_continuousLinearMapOfBilin
          ((mem_symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ B.1.1).mp B.1.2),
        fun u v z w ↦ by
          have hker := AlternatingMap.congr_fun (LinearMap.mem_ker.mp B.2) ![u, v, z, w]
          simpa only [ContinuousLinearMap.coe_coe,
            InnerProductSpace.continuousLinearMapOfBilin_apply, bianchiMap_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_apply] using hker⟩⟩
  left_inv r := by
    apply Subtype.ext
    change ofBivectorEnd
      (InnerProductSpace.continuousLinearMapOfBilin
        (bilinOfEnd (curvatureOperator r.1))).toLinearMap = r.1
    have h : (InnerProductSpace.continuousLinearMapOfBilin
        (bilinOfEnd (curvatureOperator r.1))).toLinearMap = curvatureOperator r.1 :=
      LinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦
        InnerProductSpace.continuousLinearMapOfBilin_apply (bilinOfEnd (curvatureOperator r.1)) x y
    rw [h, (mem_algebraicCurvatureSubmodule.mp r.2).ofBivectorEnd_curvatureOperator]
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    change bilinOfEnd (curvatureOperator (ofBivectorEnd
      (InnerProductSpace.continuousLinearMapOfBilin B.1.1).toLinearMap)) = B.1.1
    rw [curvatureOperator_ofBivectorEnd]
    exact ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦
      InnerProductSpace.continuousLinearMapOfBilin_apply B.1.1 x y
  map_add' r q := Subtype.ext <| Subtype.ext <|
    ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦ by
      simp [bilinOfEnd_apply, inner_add_left]
  map_smul' c r := Subtype.ext <| Subtype.ext <|
    ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦ by
      simp [bilinOfEnd_apply, real_inner_smul_left]

private theorem choose_four_cast_rat (n : ℕ) :
    (n.choose 4 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num [Nat.choose]
  · have hdesc : n.descFactorial 4 = n * (n - 1) * (n - 2) * (n - 3) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
      ring
    have hdvd : 24 ∣ n.descFactorial 4 := by
      simpa only [show Nat.factorial 4 = 24 by decide] using Nat.factorial_dvd_descFactorial n 4
    rw [Nat.choose_eq_descFactorial_div_factorial, show Nat.factorial 4 = 24 by decide,
      Nat.cast_div hdvd (by norm_num), hdesc]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    rfl

private theorem choose_four_add_eq_choose_two (n k : ℕ)
    (hrn : n.choose 4 + k = n.choose 2 * (n.choose 2 + 1) / 2) :
    k = n ^ 2 * (n ^ 2 - 1) / 12 := by
  set m := n.choose 2
  have hm_even : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have hrat : (12 : ℚ) * (k : ℚ) = ((n ^ 2 * (n ^ 2 - 1) : ℕ) : ℚ) := by
    have hhrn : (n.choose 4 : ℚ) + (k : ℚ) = (m : ℚ) * ((m : ℚ) + 1) / 2 := by
      have := congrArg (Nat.cast (R := ℚ)) hrn
      rw [Nat.cast_add, Nat.cast_div hm_even (by norm_num)] at this
      push_cast at this
      exact this
    have hm_val : (m : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := Nat.cast_choose_two ℚ n
    have hc4 := choose_four_cast_rat n
    have hrhs : ((n ^ 2 * (n ^ 2 - 1) : ℕ) : ℚ) = (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) := by
      rcases n with _ | n
      · norm_num
      · have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
        push_cast [h1]
        rfl
    rw [hrhs]
    rw [hm_val, hc4] at hhrn
    linarith
  have h12 : n ^ 2 * (n ^ 2 - 1) = 12 * k := by
    exact_mod_cast hrat.symm
  rw [h12, Nat.mul_div_right _ (by positivity)]

private theorem finrank_alternatingMap_four (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] :
    Module.finrank ℝ (E [⋀^Fin 4]→ₗ[ℝ] ℝ) = (Module.finrank ℝ E).choose 4 := by
  rw [(alternatingMapLinearEquiv (R := ℝ) (M := E) (N := ℝ) (n := 4)).finrank_eq,
    ((Module.finBasis ℝ (⋀[ℝ]^4 E)).constr ℝ).symm.finrank_eq,
    Module.finrank_fin_fun, exteriorPower.finrank_eq]

private theorem finiteDimensional_symmetricBilinearMaps_normed (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (symmetricBilinearMaps ℝ E ℝ) :=
  ((Module.finBasis ℝ E).symmetricBilinearCoordinates (G := ℝ)).symm.finiteDimensional

private theorem finrank_symmetricBilinearMaps_normed (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Module.finrank ℝ (symmetricBilinearMaps ℝ E ℝ) =
      Module.finrank ℝ E * (Module.finrank ℝ E + 1) / 2 :=
  TauCeti.finrank_symmetricBilinearMaps_self ℝ E

private theorem finrank_ker_of_surjective {M N : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] [AddCommGroup N] [Module ℝ N] {f : M →ₗ[ℝ] N}
    (hf : Function.Surjective f) :
    Module.finrank ℝ N + Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ M := by
  rw [← LinearMap.finrank_range_add_finrank_ker f, LinearMap.range_eq_top.mpr hf, finrank_top]

private theorem finrank_algebraicCurvatureSubmodule_of_inner :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) =
      (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  have : FiniteDimensional ℝ (symmetricBilinearMaps ℝ (⋀[ℝ]^2 V) ℝ) :=
    finiteDimensional_symmetricBilinearMaps_normed (⋀[ℝ]^2 V)
  have hrn := finrank_ker_of_surjective (surjective_bianchiMap (V := V))
  rw [finrank_alternatingMap_four V, (algebraicCurvatureEquivKerBianchi V).symm.finrank_eq,
    finrank_symmetricBilinearMaps_normed (⋀[ℝ]^2 V), exteriorPower.finrank_eq] at hrn
  exact choose_four_add_eq_choose_two (Module.finrank ℝ V) _ hrn

/-- The dimension of `bivectorCurvatureSubmodule V` is `n² (n² - 1) / 12`, where `n = dim V`. -/
theorem finrank_bivectorCurvatureSubmodule :
    Module.finrank ℝ (bivectorCurvatureSubmodule V) =
      (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  rw [← (algebraicCurvatureEquivBivector V).finrank_eq,
    finrank_algebraicCurvatureSubmodule_of_inner]

end InnerProductSpace

section Dimension

/-- **Dimension of the space of algebraic curvature tensors**: on a finite-dimensional real normed
space `W` of dimension `n`, `dim Curv(W) = n² (n² - 1) / 12`. -/
theorem finrank_algebraicCurvatureSubmodule (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] :
    Module.finrank ℝ (algebraicCurvatureSubmodule W) =
      (Module.finrank ℝ W) ^ 2 * ((Module.finrank ℝ W) ^ 2 - 1) / 12 := by
  let U := EuclideanSpace ℝ (Fin (Module.finrank ℝ W))
  have hU : Module.finrank ℝ U = Module.finrank ℝ W := by simp [U]
  let e : U ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hU
  let Φ : algebraicCurvatureSubmodule W ≃ₗ[ℝ] algebraicCurvatureSubmodule U :=
    { toFun r := ⟨r.1.compContinuousLinearMap fun _ ↦ (e : U →L[ℝ] W),
        compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.2 _⟩
      invFun q := ⟨q.1.compContinuousLinearMap fun _ ↦ (e.symm : W →L[ℝ] U),
        compContinuousLinearMap_mem_algebraicCurvatureSubmodule q.2 _⟩
      left_inv r := by ext m; simp
      right_inv q := by ext m; simp
      map_add' r q := by ext m; simp
      map_smul' c r := by ext m; simp }
  rw [Φ.finrank_eq, finrank_algebraicCurvatureSubmodule_of_inner, hU]

end Dimension

end TauCeti.FourTensor
