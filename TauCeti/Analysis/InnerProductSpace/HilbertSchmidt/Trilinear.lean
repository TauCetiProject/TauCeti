/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.Normed.Module.TensorProduct.Trilinear

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

private local instance trilinearCompleteSpace₁ : CompleteSpace E₁ :=
  FiniteDimensional.completeSpace 𝕜 E₁
private local instance trilinearCompleteSpace₂ : CompleteSpace E₂ :=
  FiniteDimensional.completeSpace 𝕜 E₂
private local instance trilinearCompleteSpace₃ : CompleteSpace E₃ :=
  FiniteDimensional.completeSpace 𝕜 E₃

/-- Squared Frobenius energy of the tensor-product linearization of a continuous trilinear map. -/
def trilinearHilbertSchmidtEnergy (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 _ F
    (uncurryThreefold T) ^ 2

/-- The trilinear energy is the squared Frobenius seminorm of its tensor linearization. -/
theorem trilinearHilbertSchmidtEnergy_eq_sq_frobenius
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 _ F
        (uncurryThreefold T) ^ 2 := (rfl)

/-- The three-slot energy is the sum of squared output norms over all triples of vectors
from three independently chosen orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (b₃ : OrthonormalBasis ι₃ 𝕜 E₃) (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
  rw [trilinearHilbertSchmidtEnergy_eq_sq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply
      ((b₁.tensorProduct b₂).tensorProduct b₃)]
  simp only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply,
    uncurryThreefold_tmul]

/-- The three-slot energy is the sum of squared Hilbert–Schmidt norms of its slices.
The first two slots use independently chosen orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum_sq_hilbertSchmidtNorm
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    letI := FiniteDimensional.completeSpace 𝕜 E₃
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, (T (b₁ i) (b₂ j)).hilbertSchmidtNorm ^ 2 := by
  rw [trilinearHilbertSchmidtEnergy_eq_sum b₁ b₂ (stdOrthonormalBasis 𝕜 E₃)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  exact (sq_hilbertSchmidtNorm_eq_sum _ (stdOrthonormalBasis 𝕜 E₃)).symm

/-- Trilinear Hilbert–Schmidt energy is homogeneous of degree two. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_smul (c : 𝕜)
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy (c • T) = ‖c‖ ^ 2 * trilinearHilbertSchmidtEnergy T := by
  simp only [trilinearHilbertSchmidtEnergy_eq_sq_frobenius,
    map_smul, map_smul_eq_mul, mul_pow]

/-- Negating a trilinear map preserves its energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_neg
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy (-T) = trilinearHilbertSchmidtEnergy T := by
  simpa only [neg_one_smul 𝕜 T, norm_neg, norm_one, one_pow, one_mul] using
    trilinearHilbertSchmidtEnergy_smul (-1 : 𝕜) T

/-- The three-slot energy is nonnegative. -/
theorem trilinearHilbertSchmidtEnergy_nonneg
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    0 ≤ trilinearHilbertSchmidtEnergy T := by
  rw [trilinearHilbertSchmidtEnergy_eq_sq_frobenius]
  exact sq_nonneg _

/-- The zero trilinear map has zero energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_zero :
    trilinearHilbertSchmidtEnergy (0 : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) = 0 := by
  simp only [trilinearHilbertSchmidtEnergy_eq_sq_frobenius,
    map_zero, zero_pow two_ne_zero]

/-- The energy vanishes exactly when the trilinear map vanishes. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_eq_zero_iff
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let L := (uncurryThreefold T).toContinuousLinearMap
    let b := (stdOrthonormalBasis 𝕜 ((E₁ ⊗[𝕜] E₂) ⊗[𝕜] E₃)).toHilbertBasis
    have hL := L.enorm_sq_le_hilbertSchmidtEnergy b
    have henergy : L.hilbertSchmidtEnergy b = ENNReal.ofReal (trilinearHilbertSchmidtEnergy T) := by
      rw [hilbertSchmidtEnergy_eq_ofReal_sq_frobenius]
      simp only [L, LinearMap.coe_toContinuousLinearMap,
        trilinearHilbertSchmidtEnergy_eq_sq_frobenius]
    rw [henergy, h, ENNReal.ofReal_zero] at hL
    have hLzero : L = 0 := by
      simpa using hL
    ext x y z
    simpa only [L, LinearMap.coe_toContinuousLinearMap', uncurryThreefold_tmul,
      zero_apply] using congrArg (fun f ↦ f ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z)) hLzero
  · rintro rfl
    exact trilinearHilbertSchmidtEnergy_zero

/-- Independent input linear isometric equivalences preserve trilinear energy when the
corresponding output norms agree pointwise. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquivs_of_norm_eq
    {E₁' E₂' E₃' G : Type*}
    [NormedAddCommGroup E₁'] [InnerProductSpace 𝕜 E₁'] [FiniteDimensional 𝕜 E₁']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    [NormedAddCommGroup E₃'] [InnerProductSpace 𝕜 E₃'] [FiniteDimensional 𝕜 E₃']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (S : E₁' →L[𝕜] E₂' →L[𝕜] E₃' →L[𝕜] G)
    (e₁ : E₁' ≃ₗᵢ[𝕜] E₁) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂) (e₃ : E₃' ≃ₗᵢ[𝕜] E₃)
    (h : ∀ x y z, ‖S x y z‖ = ‖T (e₁ x) (e₂ y) (e₃ z)‖) :
    trilinearHilbertSchmidtEnergy S = trilinearHilbertSchmidtEnergy T := by
  let b₁ := stdOrthonormalBasis 𝕜 E₁'
  let b₂ := stdOrthonormalBasis 𝕜 E₂'
  let b₃ := stdOrthonormalBasis 𝕜 E₃'
  rw [trilinearHilbertSchmidtEnergy_eq_sum b₁ b₂ b₃ S,
    trilinearHilbertSchmidtEnergy_eq_sum (b₁.map e₁) (b₂.map e₂) (b₃.map e₃) T]
  simp only [OrthonormalBasis.map_apply, h]

/-- Pointwise equality of output norms preserves the three-slot energy. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (S : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] G)
    (h : ∀ x y z, ‖T x y z‖ = ‖S x y z‖) :
    trilinearHilbertSchmidtEnergy T = trilinearHilbertSchmidtEnergy S := by
  apply trilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquivs_of_norm_eq S T
    (.refl 𝕜 E₁) (.refl 𝕜 E₂) (.refl 𝕜 E₃)
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using h

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
  apply trilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquivs_of_norm_eq T S e₁ e₂ e₃
  intro x y z
  rw [h, U.norm_map]

end ContinuousLinearMap
