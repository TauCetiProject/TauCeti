/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# The Hilbert–Schmidt energy of a trilinear map

For three finite-dimensional inner-product input spaces, the energy of a continuous trilinear
map is the squared Frobenius seminorm of its linearization on their Hilbert tensor product.
Otis Chodosh originally formalized the three-slot energy and its basis-independent sum formula.
The output may be infinite-dimensional. The three input bases can be chosen independently.

The energy is preserved by independent linear isometric equivalences on the inputs and a
linear isometric embedding on the output. Its basis-independence extends the one-slot result
`LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq` through the tensor-product Frobenius seminorm.
-/

public noncomputable section

open Module
open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ E₃ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₃]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local instance trilinearCompleteSpace₁ : CompleteSpace E₁ := FiniteDimensional.completeSpace 𝕜 E₁
local instance trilinearCompleteSpace₂ : CompleteSpace E₂ := FiniteDimensional.completeSpace 𝕜 E₂
local instance trilinearCompleteSpace₃ : CompleteSpace E₃ := FiniteDimensional.completeSpace 𝕜 E₃

/-- Linearize a continuous trilinear map on the tensor product of its three input spaces. -/
private def trilinearTensorLinearMap (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    (E₁ ⊗[𝕜] E₂) ⊗[𝕜] E₃ →ₗ[𝕜] F :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM 𝕜).comp
    (TensorProduct.lift T.toLinearMap₁₂))

omit [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] in
private theorem trilinearTensorLinearMap_tmul (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (x : E₁) (y : E₂) (z : E₃) :
    trilinearTensorLinearMap T ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) = T x y z := rfl

/-- Squared Frobenius energy of the tensor-product linearization of a continuous trilinear map. -/
def trilinearHilbertSchmidtEnergy (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 _ F
    (trilinearTensorLinearMap T) ^ 2

/-- The three-slot energy is the sum of squared values over any three orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (b₃ : OrthonormalBasis ι₃ 𝕜 E₃) (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
  rw [trilinearHilbertSchmidtEnergy,
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply
      ((b₁.tensorProduct b₂).tensorProduct b₃)]
  simp only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply,
    trilinearTensorLinearMap_tmul]

/-- Compute the trilinear energy in the standard orthonormal bases of its input spaces. -/
theorem trilinearHilbertSchmidtEnergy_def (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, ∑ k, ‖T (stdOrthonormalBasis 𝕜 E₁ i)
        (stdOrthonormalBasis 𝕜 E₂ j) (stdOrthonormalBasis 𝕜 E₃ k)‖ ^ 2 :=
  trilinearHilbertSchmidtEnergy_eq_sum _ _ _ T

private theorem sq_hilbertSchmidtNorm_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E₃) (S : E₃ →L[𝕜] F) :
    S.hilbertSchmidtNorm ^ 2 = ∑ k, ‖S (b k)‖ ^ 2 := by
  rw [ContinuousLinearMap.sq_hilbertSchmidtNorm _ b.toHilbertBasis,
    ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
    ENNReal.toReal_ofReal (sq_nonneg _),
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b]
  simp only [ContinuousLinearMap.coe_coe]

/-- The three-slot energy is the sum of one-slot Hilbert–Schmidt energies of its slices.
The first two slots use independently chosen orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum_sq_hilbertSchmidtNorm
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, (T (b₁ i) (b₂ j)).hilbertSchmidtNorm ^ 2 := by
  rw [trilinearHilbertSchmidtEnergy_eq_sum b₁ b₂ (stdOrthonormalBasis 𝕜 E₃)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  exact (sq_hilbertSchmidtNorm_eq_sum (stdOrthonormalBasis 𝕜 E₃) _).symm

/-- Trilinear Hilbert–Schmidt energy is homogeneous of degree two. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_smul (c : 𝕜)
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy (c • T) = ‖c‖ ^ 2 * trilinearHilbertSchmidtEnergy T := by
  simp [trilinearHilbertSchmidtEnergy_def, Finset.mul_sum, norm_smul, mul_pow]

/-- Negating a trilinear map preserves its energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_neg
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy (-T) = trilinearHilbertSchmidtEnergy T := by
  simp [trilinearHilbertSchmidtEnergy_def]

/-- The three-slot energy is nonnegative. -/
theorem trilinearHilbertSchmidtEnergy_nonneg
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    0 ≤ trilinearHilbertSchmidtEnergy T := by
  rw [trilinearHilbertSchmidtEnergy]
  exact sq_nonneg _

/-- The zero trilinear map has zero energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_zero :
    trilinearHilbertSchmidtEnergy (0 : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) = 0 := by
  simp [trilinearHilbertSchmidtEnergy_def]

/-- The energy vanishes exactly when the trilinear map vanishes. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_eq_zero_iff
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b₁ := stdOrthonormalBasis 𝕜 E₁
    let b₂ := stdOrthonormalBasis 𝕜 E₂
    let b₃ := stdOrthonormalBasis 𝕜 E₃
    rw [trilinearHilbertSchmidtEnergy_eq_sum b₁ b₂ b₃] at h
    let I₁ := Fin (finrank 𝕜 E₁)
    let I₂ := Fin (finrank 𝕜 E₂)
    let I₃ := Fin (finrank 𝕜 E₃)
    let f : (I₁ × I₂) × I₃ → ℝ :=
      fun p ↦ ‖T (b₁ p.1.1) (b₂ p.1.2) (b₃ p.2)‖ ^ 2
    have hprod : (∑ p, f p) = 0 := by
      simpa only [f, Fintype.sum_prod_type] using h
    have hf (p : (I₁ × I₂) × I₃) : f p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun p _ ↦ sq_nonneg _)).1
        hprod p (Finset.mem_univ p)
    have hijk : ∀ i j k, T (b₁ i) (b₂ j) (b₃ k) = 0 := by
      intro i j k
      apply norm_eq_zero.1
      exact sq_eq_zero_iff.1 (hf ((i, j), k))
    apply ContinuousLinearMap.coe_injective
    apply b₁.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b₂.toBasis.ext
    intro j
    apply ContinuousLinearMap.coe_injective
    apply b₃.toBasis.ext
    intro k
    exact hijk i j k
  · rintro rfl
    exact trilinearHilbertSchmidtEnergy_zero

/-- Pointwise equality of output norms preserves the three-slot energy. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (S : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] G)
    (h : ∀ x y z, ‖T x y z‖ = ‖S x y z‖) :
    trilinearHilbertSchmidtEnergy T = trilinearHilbertSchmidtEnergy S := by
  simp only [trilinearHilbertSchmidtEnergy_def, h]

/-- Independent input linear isometric equivalences and an output linear isometry preserve
trilinear energy. The output isometry need not be surjective. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquivs_of_linearIsometry
    {E₁' E₂' E₃' G : Type*}
    [NormedAddCommGroup E₁'] [InnerProductSpace 𝕜 E₁'] [FiniteDimensional 𝕜 E₁']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    [NormedAddCommGroup E₃'] [InnerProductSpace 𝕜 E₃'] [FiniteDimensional 𝕜 E₃']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (S : E₁' →L[𝕜] E₂' →L[𝕜] E₃' →L[𝕜] G)
    (e₁ : E₁' ≃ₗᵢ[𝕜] E₁) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂) (e₃ : E₃' ≃ₗᵢ[𝕜] E₃)
    (U : F →ₗᵢ[𝕜] G)
    (h : ∀ x y z, S x y z = U (T (e₁ x) (e₂ y) (e₃ z))) :
    trilinearHilbertSchmidtEnergy S = trilinearHilbertSchmidtEnergy T := by
  let b₁ := stdOrthonormalBasis 𝕜 E₁'
  let b₂ := stdOrthonormalBasis 𝕜 E₂'
  let b₃ := stdOrthonormalBasis 𝕜 E₃'
  rw [trilinearHilbertSchmidtEnergy_eq_sum b₁ b₂ b₃ S,
    trilinearHilbertSchmidtEnergy_eq_sum (b₁.map e₁) (b₂.map e₂) (b₃.map e₃) T]
  simp only [h, U.norm_map, OrthonormalBasis.map_apply]

end ContinuousLinearMap
