/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.Topology.Sphere.TangentSections.Basic

import Mathlib.Algebra.Star.Pi

/-!
# Balanced complexification and explicit unitary trivialization of sphere tangent sections

Although the continuous real tangent-section module `P = TauCeti.tangentSections (Fin 3) ℝ` over
`R = C(S², ℝ)` is not free (`TauCeti.not_free_tangentSections_fin_three`), extending scalars from
`ℝ` to `ℂ` resolves the topological obstruction: over `R_ℂ = C(S², ℂ)`, the complexified tangent
module `P_ℂ = TauCeti.tangentSections (Fin 3) ℂ` is free of rank two.

This file establishes both halves of that phenomenon:

1. **Balanced scalar extension (`TauCeti.tangentSectionsExtendEquiv`,
   `TauCeti.tangentSectionsComplexifyEquiv`).** For any finite index type `ι` and any continuous
   `ℝ`-algebra homomorphism `φ : R →ₐ[ℝ] S`, post-composition induces a ring homomorphism
   `f : C(S_ι, R) →+* C(S_ι, S)`, and the balanced scalar extension
   `TauCeti.BalancedExtension f (tangentSections ι R)` is canonically `C(S_ι, S)`-linearly
   isomorphic to `tangentSections ι S`. Specializing to `ℝ → ℂ` identifies the balanced
   complexification `R_ℂ ⊗_R P` with `P_ℂ`.

2. **Explicit continuous unitary frame on `S²` and rank-two freeness over `C(S², ℂ)`.** On
   `S² ⊂ ℝ³`, projecting the constant complex vector `(1, i, 0)` orthogonally onto the complexified
   tangent plane gives `w(x) = (1, i, 0) - (x₀ + i x₁) x`, whose pointwise Hermitian squared norm is
   `1 + x₂² ≥ 1`. Dividing by `√(1 + x₂²)` produces a continuous unit section
   `u = TauCeti.sphereComplexFrameFst`, and setting `v = x ⨯₃ star u`
   (`TauCeti.sphereComplexFrameSnd`) completes `(u, v, x)` to a `3 × 3` unitary matrix
   `TauCeti.sphereComplexFrameMatrix ∈ Matrix.unitaryGroup (Fin 3) C(S², ℂ)`. Its first two columns
   form an explicit Hermitian-orthonormal `C(S², ℂ)`-basis
   `TauCeti.tangentSectionsSphereTwoComplexBasis` of `tangentSections (Fin 3) ℂ`, rendering
   `tangentSections (Fin 3) ℂ` free of rank two.

## Main definitions

* `TauCeti.tangentSectionsExtendEquiv`: balanced scalar extension
  `BalancedExtension ((φ : R →+* S).compLeftContinuous _ hφ) (tangentSections ι R) ≃ₗ[C(S_ι, S)]
  tangentSections ι S`.
* `TauCeti.tangentSectionsComplexifyEquiv`: balanced complexification
  `R_ℂ ⊗_R tangentSections ι ℝ ≃ₗ[R_ℂ] tangentSections ι ℂ`.
* `TauCeti.sphereComplexUnnormVec`: the unnormalized nowhere-vanishing complex tangent field
  `w(x) = (1, i, 0) - (x₀ + i x₁) x` on `S²`.
* `TauCeti.sphereComplexNormInv`, `TauCeti.sphereComplexNormInvComplex`: the `ℝ`- and `ℂ`-valued
  normalizing factors `x ↦ (√(1 + x₂²))⁻¹` on `S²`.
* `TauCeti.sphereComplexFrameFst`, `TauCeti.sphereComplexFrameSnd`: the explicit nowhere-vanishing
  Hermitian-orthonormal complex tangent fields on `S²`.
* `TauCeti.sphereComplexFrameMatrix`: the `3 × 3` matrix with columns `(u, v, x)` in
  `Matrix.unitaryGroup (Fin 3) C(S², ℂ)`.
* `TauCeti.tangentSectionsSphereTwoComplexEquiv`, `TauCeti.tangentSectionsSphereTwoComplexBasis`,
  `TauCeti.tangentSectionsSphereTwoComplexTrivializationEquiv`: the rank-two `C(S², ℂ)`-linear
  trivialization and basis of `tangentSections (Fin 3) ℂ`, together with the composite isomorphism
  `R_ℂ ⊗_R P ≃ₗ[R_ℂ] R_ℂ²`.

## References

* R. G. Swan, *Vector bundles and projective modules*, Trans. Amer. Math. Soc. **105** (1962),
  264–277, Example 1 (for the continuous tangent-section module on spheres).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society (2013), Chapter I, Example 1.2.2 and Chapter II,
  §2.8 and Example 2.8.1 (for the real sphere example and scalar extension of projective modules;
  the explicit unitary frame `(u, v, x)` above is a direct elementary construction).
-/

public section

noncomputable section

open Matrix Metric
open scoped BigOperators

namespace TauCeti

section ScalarExtension

variable {ι : Type*} [Fintype ι]
  {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Algebra ℝ R] [ContinuousSMul ℝ R]
  {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [Algebra ℝ S] [ContinuousSMul ℝ S]

/-- **Balanced scalar extension of continuous tangent sections.** For a continuous `ℝ`-algebra
homomorphism `φ : R →ₐ[ℝ] S` with induced ring homomorphism
`f = (φ : R →+* S).compLeftContinuous _ hφ : C(S_ι, R) →+* C(S_ι, S)`, the balanced tensor product
`BalancedExtension f (tangentSections ι R)` is canonically isomorphic as a `C(S_ι, S)`-module to
`tangentSections ι S`, sending `c ⊗ v` to `i ↦ c * f (v i)`. -/
def tangentSectionsExtendEquiv (φ : R →ₐ[ℝ] S) (hφ : Continuous φ) :
    BalancedExtension
      ((φ : R →+* S).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1) hφ)
      (tangentSections ι R) ≃ₗ[C(sphere (0 : EuclideanSpace ℝ ι) 1, S)]
      tangentSections ι S :=
  letI := Classical.decEq ι
  let f := (φ : R →+* S).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1) hφ
  let e₁ : tangentSections ι R ≃ₗ[C(sphere (0 : EuclideanSpace ℝ ι) 1, R)]
      LinearMap.range (sphereTangentProjMatrix ι R).vecMulLinear :=
    LinearEquiv.ofEq _ _ (range_vecMulLinear_sphereTangentProjMatrix (ι := ι) (R := R)).symm
  let e₂ : LinearMap.range ((sphereTangentProjMatrix ι R).map f).vecMulLinear ≃ₗ[
      C(sphere (0 : EuclideanSpace ℝ ι) 1, S)] tangentSections ι S :=
    LinearEquiv.ofEq _ _ <| by
      rw [map_sphereTangentProjMatrix, range_vecMulLinear_sphereTangentProjMatrix]
  (BalancedExtension.congr f e₁).trans
    ((BalancedExtension.rangeVecMulLinearEquiv f
      (isIdempotentElem_sphereTangentProjMatrix (ι := ι) (R := R))).trans e₂)

@[simp]
theorem coe_tangentSectionsExtendEquiv_tmul (φ : R →ₐ[ℝ] S) (hφ : Continuous φ)
    (c : C(sphere (0 : EuclideanSpace ℝ ι) 1, S)) (v : tangentSections ι R) :
    (tangentSectionsExtendEquiv φ hφ
      (BalancedExtension.tmul
        ((φ : R →+* S).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1) hφ) c v) :
      ι → C(sphere (0 : EuclideanSpace ℝ ι) 1, S)) =
      fun i ↦ c * (φ : R →+* S).compLeftContinuous _ hφ (v.val i) := by
  simp only [tangentSectionsExtendEquiv, LinearEquiv.trans_apply, BalancedExtension.congr_tmul,
    LinearEquiv.coe_ofEq_apply, BalancedExtension.coe_rangeVecMulLinearEquiv_tmul]

/-- Explicit formula for the inverse of `tangentSectionsExtendEquiv` through the rows of the
orthogonal-projection matrix `1 - x xᵀ`: a tangent field `w` over `S` maps to
`∑ i, wᵢ ⊗ (1 - x xᵀ)ᵢ`. -/
theorem tangentSectionsExtendEquiv_symm_apply [inst : DecidableEq ι] (φ : R →ₐ[ℝ] S)
    (hφ : Continuous φ) (w : tangentSections ι S) :
    (tangentSectionsExtendEquiv φ hφ).symm w =
      ∑ i : ι, BalancedExtension.tmul
        ((φ : R →+* S).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1) hφ)
        (w.val i)
        ⟨sphereTangentProjMatrix ι R i, by
          rw [← range_vecMulLinear_sphereTangentProjMatrix]
          exact Matrix.row_mem_range_vecMulLinear _ i⟩ := by
  obtain rfl : inst = Classical.decEq ι := Subsingleton.elim _ _
  simp only [tangentSectionsExtendEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.ofEq_symm, BalancedExtension.congr_symm,
    BalancedExtension.rangeVecMulLinearEquiv_symm_apply, map_sum, BalancedExtension.congr_tmul,
    LinearEquiv.coe_ofEq_apply]
  exact Finset.sum_congr rfl fun i _ ↦
    congrArg _ (Subtype.ext (LinearEquiv.coe_ofEq_apply _ _))

variable (ι) in
/-- **Balanced complexification of continuous tangent sections.** Extending scalars along the
inclusion `C(S_ι, ℝ) →+* C(S_ι, ℂ)` identifies the balanced tensor product
`C(S_ι, ℂ) ⊗_{C(S_ι, ℝ)} tangentSections ι ℝ` with `tangentSections ι ℂ`. -/
def tangentSectionsComplexifyEquiv :
    BalancedExtension
      ((algebraMap ℝ ℂ).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1)
        Complex.continuous_ofReal)
      (tangentSections ι ℝ) ≃ₗ[C(sphere (0 : EuclideanSpace ℝ ι) 1, ℂ)]
      tangentSections ι ℂ :=
  tangentSectionsExtendEquiv (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal

@[simp]
theorem coe_tangentSectionsComplexifyEquiv_tmul
    (c : C(sphere (0 : EuclideanSpace ℝ ι) 1, ℂ)) (v : tangentSections ι ℝ) :
    (tangentSectionsComplexifyEquiv ι
      (BalancedExtension.tmul
        ((algebraMap ℝ ℂ).compLeftContinuous (sphere (0 : EuclideanSpace ℝ ι) 1)
          Complex.continuous_ofReal) c v) :
      ι → C(sphere (0 : EuclideanSpace ℝ ι) 1, ℂ)) =
      fun i ↦ c * (algebraMap ℝ ℂ).compLeftContinuous _ Complex.continuous_ofReal (v.val i) :=
  coe_tangentSectionsExtendEquiv_tmul (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal c v

end ScalarExtension

section ComplexFrame

/-- The constant complex ambient vector `(1, i, 0)` in `C(S², ℂ)³` whose tangential projection
furnishes a nowhere-vanishing complex tangent section on `S²`. -/
private def sphereComplexSeed :
    Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  ![1, ContinuousMap.const _ Complex.I, 0]

/-- The unnormalized nowhere-vanishing complex tangent vector field
`w(x) = (1, i, 0) - (x₀ + i x₁) x` on `S² ⊂ ℝ³`. -/
def sphereComplexUnnormVec :
    Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  sphereComplexSeed - (sphereCoord ℂ ⬝ᵥ sphereComplexSeed) • sphereCoord ℂ

theorem sphereComplexUnnormVec_def :
    sphereComplexUnnormVec =
      ![1, ContinuousMap.const _ Complex.I, 0] -
        (sphereCoord ℂ (0 : Fin 3) +
          ContinuousMap.const _ Complex.I * sphereCoord ℂ (1 : Fin 3)) • sphereCoord ℂ := by
  ext i x
  simp [sphereComplexUnnormVec, sphereComplexSeed, dotProduct, Fin.sum_univ_three, mul_comm]

theorem sphereComplexUnnormVec_mem_tangentSections :
    sphereComplexUnnormVec ∈ tangentSections (Fin 3) ℂ := by
  rw [← range_mulVecLin_sphereTangentProjMatrix]
  exact ⟨sphereComplexSeed, sphereTangentProjMatrix_mulVec sphereComplexSeed⟩

@[simp]
theorem dotProduct_sphereCoord_sphereComplexUnnormVec :
    sphereCoord ℂ ⬝ᵥ sphereComplexUnnormVec = 0 :=
  mem_tangentSections_iff.mp sphereComplexUnnormVec_mem_tangentSections

/-- The Hermitian squared norm of `w(x) = (1, i, 0) - (x₀ + i x₁) x` on `S²` is `1 + x₂²`. -/
@[simp]
theorem star_sphereComplexUnnormVec_dotProduct_self :
    star sphereComplexUnnormVec ⬝ᵥ sphereComplexUnnormVec =
      1 + sphereCoord ℂ (2 : Fin 3) ^ 2 := by
  have hsq : sphereCoord ℂ (0 : Fin 3) ^ 2 +
      sphereCoord ℂ (1 : Fin 3) ^ 2 +
      sphereCoord ℂ (2 : Fin 3) ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three] using sum_sphereCoord_sq (R := ℂ) (ι := Fin 3)
  let cI : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) := ContinuousMap.const _ Complex.I
  have hcI_star : star cI = -cI := by
    ext x
    simp [cI]
  have hcI_sq : cI ^ 2 = -1 := by
    ext x
    simp [cI]
  have hseed : sphereComplexSeed = ![1, cI, 0] := rfl
  simp only [sphereComplexUnnormVec, hseed, dotProduct, Fin.sum_univ_three, Pi.star_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons, star_sub, star_mul', star_add, star_one, star_zero,
    star_sphereCoord_apply, hcI_star]
  linear_combination
    (sphereCoord ℂ (0 : Fin 3) ^ 2 - cI ^ 2 * sphereCoord ℂ (1 : Fin 3) ^ 2 - 1) * hsq +
    (sphereCoord ℂ (1 : Fin 3) ^ 2 - 1) * hcI_sq

/-- The strictly positive continuous normalizing factor `x ↦ (√(1 + x₂²))⁻¹` on `S²`. -/
def sphereComplexNormInv : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℝ) where
  toFun x := (Real.sqrt (1 + ((x : EuclideanSpace ℝ (Fin 3)) 2) ^ 2))⁻¹
  continuous_toFun := by
    refine Continuous.inv₀ ?_ fun x ↦ (Real.sqrt_pos.mpr (by positivity)).ne'
    exact Real.continuous_sqrt.comp <|
      continuous_const.add (((EuclideanSpace.proj (2 : Fin 3)).continuous.comp
        continuous_subtypeVal).pow 2)

@[simp]
theorem sphereComplexNormInv_apply (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereComplexNormInv x = (Real.sqrt (1 + ((x : EuclideanSpace ℝ (Fin 3)) 2) ^ 2))⁻¹ :=
  (rfl)

theorem sphereComplexNormInv_sq_mul :
    sphereComplexNormInv ^ 2 * (1 + sphereCoord ℝ (2 : Fin 3) ^ 2) = 1 := by
  ext x
  have hpos : 0 ≤ 1 + ((x : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by positivity
  have hne : 1 + ((x : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 ≠ 0 := by positivity
  simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, sphereComplexNormInv_apply, sphereCoord_apply,
    Algebra.algebraMap_self, RingHom.id_apply, inv_pow, Real.sq_sqrt hpos, inv_mul_cancel₀ hne]

/-- The `ℂ`-valued normalizing factor `x ↦ ((√(1 + x₂²))⁻¹ : ℂ)` in `C(S², ℂ)`. -/
def sphereComplexNormInvComplex : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  (algebraMap ℝ ℂ).compLeftContinuous _ Complex.continuous_ofReal sphereComplexNormInv

@[simp]
theorem sphereComplexNormInvComplex_apply (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereComplexNormInvComplex x =
      ((Real.sqrt (1 + ((x : EuclideanSpace ℝ (Fin 3)) 2) ^ 2) : ℂ))⁻¹ := by
  simp [sphereComplexNormInvComplex]

@[simp]
theorem star_sphereComplexNormInvComplex :
    star sphereComplexNormInvComplex = sphereComplexNormInvComplex := by
  ext x
  exact Complex.conj_ofReal (sphereComplexNormInv x)

/-- Over `C(S², ℂ)`, the square of `sphereComplexNormInvComplex` is the inverse of `1 + x₂²`. -/
theorem sphereComplexNormInvComplex_sq_mul :
    sphereComplexNormInvComplex ^ 2 * (1 + sphereCoord ℂ (2 : Fin 3) ^ 2) = 1 := by
  rw [sphereComplexNormInvComplex]
  have h := congrArg
    ((algebraMap ℝ ℂ).compLeftContinuous
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) Complex.continuous_ofReal)
    sphereComplexNormInv_sq_mul
  have hc : (algebraMap ℝ ℂ).compLeftContinuous _ Complex.continuous_ofReal
      (sphereCoord ℝ (2 : Fin 3)) = sphereCoord ℂ (2 : Fin 3) :=
    compLeftContinuous_sphereCoord (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal (2 : Fin 3)
  simpa only [map_mul, map_pow, map_add, map_one, hc] using h

/-- First vector of the continuous unitary tangent frame on `S²`:
`u(x) = (1 + x₂²)⁻¹/² ((1, i, 0) - (x₀ + i x₁) x)`. -/
def sphereComplexFrameFst :
    Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  sphereComplexNormInvComplex • sphereComplexUnnormVec

theorem sphereComplexFrameFst_def :
    sphereComplexFrameFst = sphereComplexNormInvComplex • sphereComplexUnnormVec :=
  (rfl)

/-- Second vector of the continuous unitary tangent frame on `S²`: `v(x) = x ⨯₃ star (u(x))`. -/
def sphereComplexFrameSnd :
    Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  sphereCoord ℂ ⨯₃ star sphereComplexFrameFst

theorem sphereComplexFrameSnd_def :
    sphereComplexFrameSnd = sphereCoord ℂ ⨯₃ star sphereComplexFrameFst :=
  (rfl)

theorem star_sphereComplexFrameSnd :
    star sphereComplexFrameSnd = sphereCoord ℂ ⨯₃ sphereComplexFrameFst := by
  ext i
  fin_cases i <;> simp [sphereComplexFrameSnd_def, cross_apply, mul_comm]

theorem sphereComplexFrameFst_mem_tangentSections :
    sphereComplexFrameFst ∈ tangentSections (Fin 3) ℂ :=
  Submodule.smul_mem _ _ sphereComplexUnnormVec_mem_tangentSections

@[simp]
theorem dotProduct_sphereCoord_sphereComplexFrameFst :
    sphereCoord ℂ ⬝ᵥ sphereComplexFrameFst = 0 :=
  mem_tangentSections_iff.mp sphereComplexFrameFst_mem_tangentSections

@[simp]
theorem dotProduct_sphereCoord_sphereComplexFrameSnd :
    sphereCoord ℂ ⬝ᵥ sphereComplexFrameSnd = 0 :=
  dot_self_cross _ _

theorem sphereComplexFrameSnd_mem_tangentSections :
    sphereComplexFrameSnd ∈ tangentSections (Fin 3) ℂ :=
  mem_tangentSections_iff.mpr dotProduct_sphereCoord_sphereComplexFrameSnd

@[simp]
theorem star_sphereComplexFrameFst_dotProduct_self :
    star sphereComplexFrameFst ⬝ᵥ sphereComplexFrameFst = 1 := by
  -- Supply `StarMul.toStarModule` directly so search skips `ContinuousMap.instStarModule`.
  have := StarMul.toStarModule (R := C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ))
  rw [sphereComplexFrameFst_def, star_smul, star_sphereComplexNormInvComplex,
    smul_dotProduct sphereComplexNormInvComplex (star sphereComplexUnnormVec),
    dotProduct_smul sphereComplexNormInvComplex (star sphereComplexUnnormVec),
    star_sphereComplexUnnormVec_dotProduct_self, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
    sphereComplexNormInvComplex_sq_mul]

@[simp]
theorem star_sphereComplexFrameFst_dotProduct_snd :
    star sphereComplexFrameFst ⬝ᵥ sphereComplexFrameSnd = 0 :=
  dot_cross_self _ _

@[simp]
theorem star_sphereComplexFrameSnd_dotProduct_fst :
    star sphereComplexFrameSnd ⬝ᵥ sphereComplexFrameFst = 0 := by
  simpa [dotProduct, mul_comm] using congrArg star star_sphereComplexFrameFst_dotProduct_snd

@[simp]
theorem star_sphereComplexFrameFst_dotProduct_sphereCoord :
    star sphereComplexFrameFst ⬝ᵥ sphereCoord ℂ = 0 := by
  simpa [dotProduct, mul_comm] using congrArg star dotProduct_sphereCoord_sphereComplexFrameFst

@[simp]
theorem star_sphereComplexFrameSnd_dotProduct_sphereCoord :
    star sphereComplexFrameSnd ⬝ᵥ sphereCoord ℂ = 0 := by
  simpa [dotProduct, mul_comm] using congrArg star dotProduct_sphereCoord_sphereComplexFrameSnd

@[simp]
theorem star_sphereComplexFrameSnd_dotProduct_self :
    star sphereComplexFrameSnd ⬝ᵥ sphereComplexFrameSnd = 1 := by
  rw [star_sphereComplexFrameSnd, sphereComplexFrameSnd_def, cross_dot_cross,
    dotProduct_sphereCoord_self, dotProduct_comm sphereComplexFrameFst,
    star_sphereComplexFrameFst_dotProduct_self, dotProduct_comm sphereComplexFrameFst,
    dotProduct_sphereCoord_sphereComplexFrameFst, mul_zero, sub_zero, mul_one]

/-- The continuous `3 × 3` matrix over `C(S², ℂ)` with columns
`(sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ)`. -/
def sphereComplexFrameMatrix :
    Matrix (Fin 3) (Fin 3) C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  (Matrix.of ![sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ])ᵀ

theorem sphereComplexFrameMatrix_def :
    sphereComplexFrameMatrix =
      (Matrix.of ![sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ])ᵀ :=
  (rfl)

@[simp]
theorem sphereComplexFrameMatrix_apply (i j : Fin 3) :
    sphereComplexFrameMatrix i j =
      ![sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ] j i :=
  (rfl)

@[simp]
theorem conjTranspose_mul_sphereComplexFrameMatrix :
    sphereComplexFrameMatrixᴴ * sphereComplexFrameMatrix = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  have hmul : (sphereComplexFrameMatrixᴴ * sphereComplexFrameMatrix) i j =
      star (![sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ] i) ⬝ᵥ
        ![sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ] j := by
    simp only [Matrix.mul_apply, conjTranspose_apply, sphereComplexFrameMatrix_apply, dotProduct,
      Pi.star_apply]
  rw [hmul]
  fin_cases i <;> fin_cases j <;> simp

/-- `(sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ)` defines an element of the
unitary group `U₃(C(S², ℂ))`. -/
theorem sphereComplexFrameMatrix_mem_unitaryGroup :
    sphereComplexFrameMatrix ∈
      Matrix.unitaryGroup (Fin 3) C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) :=
  Matrix.mem_unitaryGroup_iff'.mpr conjTranspose_mul_sphereComplexFrameMatrix

@[simp]
theorem sphereComplexFrameMatrix_mul_conjTranspose :
    sphereComplexFrameMatrix * sphereComplexFrameMatrixᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp sphereComplexFrameMatrix_mem_unitaryGroup

/-- Orthonormal expansion of any ambient complex field `z : C(S², ℂ)³` along the unitary frame
`(sphereComplexFrameFst, sphereComplexFrameSnd, sphereCoord ℂ)`. -/
theorem sphereComplexFrame_reconstruct
    (z : Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) :
    (star sphereComplexFrameFst ⬝ᵥ z) • sphereComplexFrameFst +
      (star sphereComplexFrameSnd ⬝ᵥ z) • sphereComplexFrameSnd +
      (sphereCoord ℂ ⬝ᵥ z) • sphereCoord ℂ = z := by
  have hmul : sphereComplexFrameMatrix *ᵥ (sphereComplexFrameMatrixᴴ *ᵥ z) = z := by
    rw [mulVec_mulVec, sphereComplexFrameMatrix_mul_conjTranspose, one_mulVec]
  have hcols (c : Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) :
      sphereComplexFrameMatrix *ᵥ c =
        c 0 • sphereComplexFrameFst + c 1 • sphereComplexFrameSnd + c 2 • sphereCoord ℂ := by
    refine funext fun i ↦ ?_
    simp only [mulVec, dotProduct, Fin.sum_univ_three, sphereComplexFrameMatrix_apply,
      cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have h0 : (sphereComplexFrameMatrixᴴ *ᵥ z) 0 = star sphereComplexFrameFst ⬝ᵥ z := by
    simp only [mulVec, dotProduct, conjTranspose_apply, sphereComplexFrameMatrix_apply,
      cons_val_zero, Pi.star_apply]
  have h1 : (sphereComplexFrameMatrixᴴ *ᵥ z) 1 = star sphereComplexFrameSnd ⬝ᵥ z := by
    simp only [mulVec, dotProduct, conjTranspose_apply, sphereComplexFrameMatrix_apply,
      cons_val_one, cons_val_zero, Pi.star_apply]
  have h2 : (sphereComplexFrameMatrixᴴ *ᵥ z) 2 = sphereCoord ℂ ⬝ᵥ z := by
    simp only [mulVec, dotProduct, conjTranspose_apply, sphereComplexFrameMatrix_apply,
      cons_val_two, head_cons, tail_cons, star_sphereCoord_apply]
  rw [hcols, h0, h1, h2] at hmul
  exact hmul

/-- Every complex tangent section on `S²` expands uniquely along `sphereComplexFrameFst` and
`sphereComplexFrameSnd`. -/
theorem sphereComplexFrame_reconstruct_of_mem_tangentSections
    {z : Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)}
    (hz : z ∈ tangentSections (Fin 3) ℂ) :
    (star sphereComplexFrameFst ⬝ᵥ z) • sphereComplexFrameFst +
      (star sphereComplexFrameSnd ⬝ᵥ z) • sphereComplexFrameSnd = z := by
  have h := sphereComplexFrame_reconstruct z
  have h0 : (0 : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) •
      sphereCoord (ι := Fin 3) ℂ = 0 :=
    funext fun _ ↦ zero_mul _
  rwa [mem_tangentSections_iff.mp hz, h0, add_zero] at h

/-- **Explicit rank-two trivialization of `tangentSections (Fin 3) ℂ` over `C(S², ℂ)`.**
Sends `(c₀, c₁)` to `c₀ • sphereComplexFrameFst + c₁ • sphereComplexFrameSnd`, with inverse
`z ↦ (star sphereComplexFrameFst ⬝ᵥ z, star sphereComplexFrameSnd ⬝ᵥ z)`. -/
def tangentSectionsSphereTwoComplexEquiv :
    (Fin 2 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) ≃ₗ[
      C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)]
      tangentSections (Fin 3) ℂ where
  toFun c :=
    ⟨c 0 • sphereComplexFrameFst + c 1 • sphereComplexFrameSnd,
      Submodule.add_mem _
        (Submodule.smul_mem _ (c 0) sphereComplexFrameFst_mem_tangentSections)
        (Submodule.smul_mem _ (c 1) sphereComplexFrameSnd_mem_tangentSections)⟩
  invFun z := ![star sphereComplexFrameFst ⬝ᵥ z.val, star sphereComplexFrameSnd ⬝ᵥ z.val]
  map_add' c d := by
    refine Subtype.ext (funext fun i ↦ ?_)
    simp only [Submodule.coe_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' a c := by
    refine Subtype.ext (funext fun i ↦ ?_)
    simp only [RingHom.id_apply, SetLike.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  left_inv c := by
    ext j
    fin_cases j <;> simp
  right_inv z :=
    Subtype.ext (sphereComplexFrame_reconstruct_of_mem_tangentSections z.property)

@[simp]
theorem coe_tangentSectionsSphereTwoComplexEquiv_apply
    (c : Fin 2 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) :
    (tangentSectionsSphereTwoComplexEquiv c :
      Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) =
      c 0 • sphereComplexFrameFst + c 1 • sphereComplexFrameSnd :=
  (rfl)

@[simp]
theorem tangentSectionsSphereTwoComplexEquiv_symm_apply
    (z : tangentSections (Fin 3) ℂ) :
    tangentSectionsSphereTwoComplexEquiv.symm z =
      ![star sphereComplexFrameFst ⬝ᵥ z.val, star sphereComplexFrameSnd ⬝ᵥ z.val] :=
  (rfl)

/-- `tangentSectionsSphereTwoComplexEquiv` is unitary with respect to the `C(S², ℂ)`-valued
Hermitian pairing `star a ⬝ᵥ b`. -/
theorem star_tangentSectionsSphereTwoComplexEquiv_dotProduct
    (c d : Fin 2 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) :
    star (tangentSectionsSphereTwoComplexEquiv c : Fin 3 → _) ⬝ᵥ
      (tangentSectionsSphereTwoComplexEquiv d : Fin 3 → _) = star c ⬝ᵥ d := by
  -- Supply `StarMul.toStarModule` directly so search skips `ContinuousMap.instStarModule`.
  have := StarMul.toStarModule (R := C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ))
  simp only [coe_tangentSectionsSphereTwoComplexEquiv_apply, star_add, star_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, star_sphereComplexFrameFst_dotProduct_self,
    star_sphereComplexFrameFst_dotProduct_snd, star_sphereComplexFrameSnd_dotProduct_fst,
    star_sphereComplexFrameSnd_dotProduct_self, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply]
  ring

/-- The explicit `C(S², ℂ)`-basis `(sphereComplexFrameFst, sphereComplexFrameSnd)` of
`tangentSections (Fin 3) ℂ`. -/
def tangentSectionsSphereTwoComplexBasis :
    Module.Basis (Fin 2) C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)
      (tangentSections (Fin 3) ℂ) :=
  Module.Basis.map
    (Pi.basisFun C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ) (Fin 2))
    tangentSectionsSphereTwoComplexEquiv

/-- The first vector of `tangentSectionsSphereTwoComplexBasis` is `sphereComplexFrameFst`.

Not a `simp` lemma, unlike `coe_tangentSectionsSphereTwoComplexBasis_one`: `simp` tries `map_zero`
on the basis applied to `0`, whose `ZeroHomClass` search times out in large environments. -/
theorem coe_tangentSectionsSphereTwoComplexBasis_zero :
    (tangentSectionsSphereTwoComplexBasis 0 :
      Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) =
      sphereComplexFrameFst := by
  ext i x
  simp [tangentSectionsSphereTwoComplexBasis, Pi.basisFun_apply]

@[simp]
theorem coe_tangentSectionsSphereTwoComplexBasis_one :
    (tangentSectionsSphereTwoComplexBasis 1 :
      Fin 3 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) =
      sphereComplexFrameSnd := by
  ext i x
  simp [tangentSectionsSphereTwoComplexBasis, Pi.basisFun_apply]

instance : Module.Free C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)
    (tangentSections (Fin 3) ℂ) :=
  Module.Free.of_basis tangentSectionsSphereTwoComplexBasis

/-- **Balanced complexification trivializes the tangent-section module on `S²`.** Composing
`tangentSectionsComplexifyEquiv (Fin 3)` with `tangentSectionsSphereTwoComplexEquiv.symm` identifies
the balanced scalar extension `C(S², ℂ) ⊗_{C(S², ℝ)} tangentSections (Fin 3) ℝ` with the free
rank-two module `C(S², ℂ)²` (contrast with `not_free_tangentSections_fin_three`). -/
def tangentSectionsSphereTwoComplexTrivializationEquiv :
    BalancedExtension
      ((algebraMap ℝ ℂ).compLeftContinuous (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        Complex.continuous_ofReal)
      (tangentSections (Fin 3) ℝ) ≃ₗ[C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)]
      (Fin 2 → C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℂ)) :=
  (tangentSectionsComplexifyEquiv (Fin 3)).trans tangentSectionsSphereTwoComplexEquiv.symm

@[simp]
theorem tangentSectionsSphereTwoComplexTrivializationEquiv_apply
    (z : BalancedExtension
      ((algebraMap ℝ ℂ).compLeftContinuous (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        Complex.continuous_ofReal)
      (tangentSections (Fin 3) ℝ)) :
    tangentSectionsSphereTwoComplexTrivializationEquiv z =
      tangentSectionsSphereTwoComplexEquiv.symm (tangentSectionsComplexifyEquiv (Fin 3) z) :=
  (rfl)

end ComplexFrame

end TauCeti
