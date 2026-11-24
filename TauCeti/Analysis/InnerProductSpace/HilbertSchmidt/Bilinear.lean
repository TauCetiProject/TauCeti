/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# The Hilbert–Schmidt energy of a bilinear map

The energy of a continuous bilinear map is the sum of squared output norms over orthonormal
bases in both input slots. It is independent of the chosen bases when the output is an inner
product space. This is the squared Hilbert–Schmidt norm of tensors such as a second fundamental
form; the output need not be finite-dimensional.

The main results are `ContinuousLinearMap.bilinearHilbertSchmidtEnergy_eq_sum`, its zero
criterion, its scaling law, and invariance under linear isometric equivalences of the inputs
and linear isometries of the output.
-/

public noncomputable section

open Module
open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E E₂ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local instance bilinearCompleteSpace₁ : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
local instance bilinearCompleteSpace₂ : CompleteSpace E₂ := FiniteDimensional.completeSpace 𝕜 E₂

/-- The full ordered two-slot Hilbert–Schmidt energy of a continuous bilinear map, defined
as the squared Frobenius seminorm of its tensor-product linearization. It is computed in any
pair of orthonormal bases by `bilinearHilbertSchmidtEnergy_eq_sum`. -/
def bilinearHilbertSchmidtEnergy (T : E →L[𝕜] E₂ →L[𝕜] F) : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 (E ⊗[𝕜] E₂) F
    (TensorProduct.lift T.toLinearMap₁₂) ^ 2

/-- The energy is the squared Frobenius seminorm of the tensor-product linearization. -/
theorem bilinearHilbertSchmidtEnergy_def (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 (E ⊗[𝕜] E₂) F
        (TensorProduct.lift T.toLinearMap₁₂) ^ 2 :=
  (rfl)

/-- The energy is `∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2` for any orthonormal bases `b₁` of `E`
and `b₂` of `E₂`, chosen independently. -/
theorem bilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = ∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2 := by
  rw [bilinearHilbertSchmidtEnergy_def,
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply (b₁.tensorProduct b₂)]
  simp only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply,
    TensorProduct.lift.tmul, toLinearMap₁₂_apply_apply_apply]

/-- Swapping the two input slots preserves the energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_flip (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T.flip = bilinearHilbertSchmidtEnergy T := by
  rw [bilinearHilbertSchmidtEnergy_eq_sum
    (stdOrthonormalBasis 𝕜 E₂) (stdOrthonormalBasis 𝕜 E),
    bilinearHilbertSchmidtEnergy_eq_sum
      (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 E₂)]
  simp only [flip_apply]
  exact Finset.sum_comm

/-- The energy is the sum of squared one-slot Hilbert–Schmidt norms of the slices
`T (b₁ i)`. -/
theorem bilinearHilbertSchmidtEnergy_eq_sum_sq_hilbertSchmidtNorm
    {ι₁ : Type*} [Fintype ι₁] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
    (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = ∑ i, (T (b₁ i)).hilbertSchmidtNorm ^ 2 := by
  let b₂ := stdOrthonormalBasis 𝕜 E₂
  rw [bilinearHilbertSchmidtEnergy_eq_sum b₁ b₂]
  simp [sq_hilbertSchmidtNorm _ b₂.toHilbertBasis, hilbertSchmidtEnergy_def,
    ENNReal.toReal_sum, ENNReal.toReal_pow]

/-- Bilinear Hilbert–Schmidt energy is homogeneous of degree two. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_smul (c : 𝕜) (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy (c • T) = ‖c‖ ^ 2 * bilinearHilbertSchmidtEnergy T := by
  simp [bilinearHilbertSchmidtEnergy_eq_sum
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 E₂),
    Finset.mul_sum, norm_smul, mul_pow]

/-- Negating a bilinear map preserves its energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_neg (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy (-T) = bilinearHilbertSchmidtEnergy T := by
  simpa only [neg_one_smul 𝕜 T, norm_neg, norm_one, one_pow, one_mul] using
    bilinearHilbertSchmidtEnergy_smul (-1 : 𝕜) T

/-- The two-slot contraction is nonnegative. -/
theorem bilinearHilbertSchmidtEnergy_nonneg (T : E →L[𝕜] E₂ →L[𝕜] F) :
    0 ≤ bilinearHilbertSchmidtEnergy T := by
  rw [bilinearHilbertSchmidtEnergy_eq_sum
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 E₂)]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

grind_pattern bilinearHilbertSchmidtEnergy_nonneg => bilinearHilbertSchmidtEnergy T

/-- The zero bilinear map has zero energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_zero :
    bilinearHilbertSchmidtEnergy (0 : E →L[𝕜] E₂ →L[𝕜] F) = 0 := by
  simp [bilinearHilbertSchmidtEnergy_eq_sum
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 E₂)]

/-- The contraction vanishes exactly when the bilinear map vanishes. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_eq_zero_iff (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis 𝕜 E
    let b₂ := stdOrthonormalBasis 𝕜 E₂
    rw [bilinearHilbertSchmidtEnergy_eq_sum b b₂] at h
    have hi : ∀ i, (∑ j, ‖T (b i) (b₂ j)‖ ^ 2) = 0 := by
      exact fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).1 h i (Finset.mem_univ i)
    apply (ContinuousLinearMap.toLinearMap₁₂_inj T 0).1
    apply LinearMap.ext_basis b.toBasis b₂.toBasis
    intro i j
    have hij := (Finset.sum_sq_eq_zero_iff _ _).mp (hi i) j (Finset.mem_univ j)
    simpa only [OrthonormalBasis.coe_toBasis, toLinearMap₁₂_apply_apply_apply,
      zero_apply, norm_eq_zero] using hij
  · rintro rfl
    exact bilinearHilbertSchmidtEnergy_zero

/-- Input linear isometric equivalences and pointwise equality of output norms preserve
bilinear energy, even when the maps have different output spaces. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquiv_of_norm_eq {E' E₂' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E →L[𝕜] E₂ →L[𝕜] F) (S : E' →L[𝕜] E₂' →L[𝕜] G)
    (e₁ : E' ≃ₗᵢ[𝕜] E) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂)
    (h : ∀ x y, ‖S x y‖ = ‖T (e₁ x) (e₂ y)‖) :
    bilinearHilbertSchmidtEnergy S = bilinearHilbertSchmidtEnergy T := by
  let b := stdOrthonormalBasis 𝕜 E'
  let b₂ := stdOrthonormalBasis 𝕜 E₂'
  rw [bilinearHilbertSchmidtEnergy_eq_sum b b₂ S,
    bilinearHilbertSchmidtEnergy_eq_sum (b.map e₁) (b₂.map e₂) T]
  simp only [OrthonormalBasis.map_apply, h]

/-- Pointwise equality of output norms preserves the two-slot contraction. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (T : E →L[𝕜] E₂ →L[𝕜] F)
    (S : E →L[𝕜] E₂ →L[𝕜] G)
    (h : ∀ x y, ‖T x y‖ = ‖S x y‖) :
    bilinearHilbertSchmidtEnergy T = bilinearHilbertSchmidtEnergy S := by
  apply bilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquiv_of_norm_eq S T
    (.refl 𝕜 E) (.refl 𝕜 E₂)
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using h

/-- Independent input linear isometric equivalences and an output linear isometry preserve
energy. The output isometry need not be surjective. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquiv_of_linearIsometry
    {E' E₂' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E →L[𝕜] E₂ →L[𝕜] F) (S : E' →L[𝕜] E₂' →L[𝕜] G)
    (e₁ : E' ≃ₗᵢ[𝕜] E) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂) (U : F →ₗᵢ[𝕜] G)
    (h : ∀ x y, S x y = U (T (e₁ x) (e₂ y))) :
    bilinearHilbertSchmidtEnergy S = bilinearHilbertSchmidtEnergy T := by
  apply bilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquiv_of_norm_eq T S e₁ e₂
  intro x y
  rw [h, U.norm_map]

/-- Precomposing both inputs with linear isometric equivalences preserves energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_bilinearComp_linearIsometryEquiv {E' E₂' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    (T : E →L[𝕜] E₂ →L[𝕜] F) (e₁ : E' ≃ₗᵢ[𝕜] E) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂) :
    bilinearHilbertSchmidtEnergy (T.bilinearComp (e₁ : E' →L[𝕜] E) (e₂ : E₂' →L[𝕜] E₂)) =
      bilinearHilbertSchmidtEnergy T := by
  apply bilinearHilbertSchmidtEnergy_eq_of_linearIsometryEquiv_of_norm_eq T _ e₁ e₂
  intro x y
  simp only [bilinearComp_apply, LinearIsometryEquiv.coe_coe'']

/-- Postcomposing the output with a linear isometry preserves energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_compL_linearIsometry {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E →L[𝕜] E₂ →L[𝕜] F) (U : F →ₗᵢ[𝕜] G) :
    bilinearHilbertSchmidtEnergy ((compL 𝕜 E₂ F G U.toContinuousLinearMap).comp T) =
      bilinearHilbertSchmidtEnergy T := by
  apply bilinearHilbertSchmidtEnergy_eq_of_norm_eq
  intro x y
  simp only [comp_apply, compL_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]

end InnerProduct

end ContinuousLinearMap
