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
      (fun z₁ z₂ w ↦ by
        simp only [apply_add_third, apply_add_fourth]; ring)
      (fun c z w ↦ by
        simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring)
      (fun z w₁ w₂ ↦ by
        simp only [apply_add_third, apply_add_fourth]; ring)
      (fun c z w ↦ by
        simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring))
    (fun u₁ u₂ v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first, apply_add_second]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul, apply_smul_first,
        apply_smul_second]
      ring)
    (fun u v₁ v₂ ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first, apply_add_second]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul, apply_smul_first,
        apply_smul_second]
      ring)

private theorem pairAntisymm_apply (r : FourTensor V) (u v z w : V) :
    pairAntisymm r u v z w =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![v, u, z, w] - r ![u, v, w, z] + r ![v, u, w, z]) :=
  (rfl)

private def exteriorSquareForm (r : FourTensor V) :
    LinearMap.BilinForm ℝ (⋀[ℝ]^2 V) :=
  (pairAntisymm r).exteriorSquareBilinear
    (fun u z w ↦ by simp only [pairAntisymm_apply]; ring)
    -- Ascribe `IsAlt` explicitly so `exteriorSquareBilinear_ιMulti_ιMulti` matches.
    (fun u v ↦ show (pairAntisymm r u v).IsAlt from fun z ↦ by
      simp only [pairAntisymm_apply]; ring)

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
      (fun z₁ z₂ w ↦ by rw [ιMulti_two_add_left, inner_add_right])
      (fun c z w ↦ by rw [ιMulti_two_smul_left, real_inner_smul_right, smul_eq_mul])
      (fun z w₁ w₂ ↦ by rw [ιMulti_two_add_right, inner_add_right])
      (fun c z w ↦ by rw [ιMulti_two_smul_right, real_inner_smul_right, smul_eq_mul]))
    (fun u₁ u₂ v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, ιMulti_two_add_left, map_add,
        inner_add_left])
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul, ιMulti_two_smul_left,
        map_smul, real_inner_smul_left])
    (fun u v₁ v₂ ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply, ιMulti_two_add_right, map_add,
        inner_add_left])
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul, ιMulti_two_smul_right,
        map_smul, real_inner_smul_left])

/-- The four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` associated to an endomorphism `T` of the
exterior square `⋀[ℝ]^2 V`. With this convention the identity on `⋀[ℝ]^2 V` maps to
`constantCurvature V`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun T := ofLinearMap₄ (ofExteriorEndLinear T)
  map_add' S T := by
    ext m
    simp [ofExteriorEndLinear, inner_add_left]
  map_smul' c T := by
    ext m
    simp [ofExteriorEndLinear, real_inner_smul_left]

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
  constructor
  · intro h a b
    have ha : a ∈ Submodule.span ℝ (Set.range (ιMulti ℝ 2 (M := V))) := by
      rw [ιMulti_span]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      have hb : b ∈ Submodule.span ℝ (Set.range (ιMulti ℝ 2 (M := V))) := by
        rw [ιMulti_span]; trivial
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        have hu : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
        have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
        rw [hu, hv, real_inner_comm (T (ιMulti ℝ 2 ![v 0, v 1]))]
        simpa only [ofExteriorEnd_apply] using h (u 0) (u 1) (v 0) (v 1)
      | zero => simp
      | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
      | smul c y _ hy => simp only [map_smul, real_inner_smul_right, hy]
    | zero => simp
    | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
    | smul c x _ hx => simp only [map_smul, real_inner_smul_left, hx]
  · intro h u v z w
    simp only [ofExteriorEnd_apply]
    rw [h, real_inner_comm]

/-- `ofExteriorEnd T` is an algebraic curvature tensor iff `T` is symmetric and satisfies the first
Bianchi identity on pure bivectors. -/
theorem isAlgebraicCurvature_ofExteriorEnd_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    IsAlgebraicCurvature (ofExteriorEnd T) ↔
      T.IsSymmetric ∧
        ∀ u v z w,
          ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ +
          ⟪T (ιMulti ℝ 2 ![v, z]), ιMulti ℝ 2 ![u, w]⟫ +
          ⟪T (ιMulti ℝ 2 ![z, u]), ιMulti ℝ 2 ![v, w]⟫ = 0 := by
  constructor
  · intro h
    refine ⟨(ofExteriorEnd_swap_pairs_iff T).mp h.swap_pairs, fun u v z w ↦ ?_⟩
    simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w
  · rintro ⟨hsym, hcyc⟩
    refine ⟨ofExteriorEnd_antisymm_first T, ofExteriorEnd_antisymm_last T,
      (ofExteriorEnd_swap_pairs_iff T).mpr hsym, fun u v z w ↦ ?_⟩
    simpa only [ofExteriorEnd_apply] using hcyc u v z w

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
  rw [hm, compContinuousLinearMap_apply_vec, ofExteriorEnd_apply, ofExteriorEnd_apply]
  simp only [LinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, map_apply_ιMulti_two, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  have hiso := exteriorPower.inner_map_map e.toLinearIsometry
    (exteriorPower.map 2 e.symm.toLinearMap (T (ιMulti ℝ 2 ![e (m 0), e (m 1)])))
    (ιMulti ℝ 2 ![m 2, m 3])
  rw [← hiso, map_apply_ιMulti_two]
  simp only [LinearIsometry.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  congr 1
  have hcomp : exteriorPower.map 2 e.toLinearMap ∘ₗ exteriorPower.map 2 e.symm.toLinearMap =
      LinearMap.id := by
    rw [← exteriorPower.map_comp]
    have he : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
      ext v; simp
    rw [he, exteriorPower.map_id]
  exact (LinearMap.congr_fun hcomp _).symm

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
  map_add' r q := by
    refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      LinearMap.add_apply, inner_add_left, exteriorSquareForm_ιMulti, add_apply]
    ring
  map_smul' c r := by
    refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      LinearMap.smul_apply, RingHom.id_apply, real_inner_smul_left, exteriorSquareForm_ιMulti,
      smul_apply, smul_eq_mul]
    ring

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
    toExteriorEnd (ofExteriorEnd T) = T := by
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
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
      ∀ u v z w, ⟪T (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  constructor
  · rintro rfl u v z w
    exact inner_toExteriorEnd_ιMulti_of_antisymm h₁ h₂ u v z w
  · intro h
    refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
    rw [inner_toExteriorEnd_ιMulti_of_antisymm h₁ h₂, h]

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
        (exteriorPower.map 2 e.toLinearMap) := by
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  rw [inner_toExteriorEnd_ιMulti]
  simp only [compContinuousLinearMap_apply_vec, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearMap.comp_apply, map_apply_ιMulti_two,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← inner_toExteriorEnd_ιMulti r (e u) (e v) (e z) (e w)]
  have hiso := exteriorPower.inner_map_map e.toLinearIsometry
    (exteriorPower.map 2 e.symm.toLinearMap (toExteriorEnd r (ιMulti ℝ 2 ![e u, e v])))
    (ιMulti ℝ 2 ![z, w])
  rw [← hiso, map_apply_ιMulti_two]
  simp only [LinearIsometry.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  congr 1
  have hcomp : exteriorPower.map 2 e.toLinearMap ∘ₗ exteriorPower.map 2 e.symm.toLinearMap =
      LinearMap.id := by
    rw [← exteriorPower.map_comp]
    have he : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
      ext x; simp
    rw [he, exteriorPower.map_id]
  exact (LinearMap.congr_fun hcomp _).symm

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
    rw [h₁ (b j) (b i) (b i) (b j), h₁ (b i) (b j) (b j) (b i)]
    ring
  simp_rw [hterm]
  have hcomm : (∑ i, ∑ j, r ![b j, b i, b j, b i]) = ∑ i, ∑ j, r ![b i, b j, b i, b j] :=
    Finset.sum_comm
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hcomm, Finset.sum_comm]
  ring

/-- The scalar contraction of an algebraic curvature tensor is twice the trace of its curvature
endomorphism. -/
theorem IsAlgebraicCurvature.scalar_eq_two_mul_trace_toExteriorEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (toExteriorEnd r) :=
  scalar_eq_two_mul_trace_toExteriorEnd_of_antisymm_first hr.antisymm_first

end TauCeti.FourTensor
