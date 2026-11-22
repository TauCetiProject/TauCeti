/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The Hilbert–Schmidt energy of a trilinear map

The energy of a continuous trilinear map is the sum of squared output norms over orthonormal
bases in three input slots. It is independent of each chosen basis when the output is an inner
product space. This is a squared Hilbert–Schmidt norm for tensors such as the covariant
derivative of a second fundamental form; the output need not be finite-dimensional.

The main results are `ContinuousLinearMap.trilinearHilbertSchmidtEnergy_eq_sum`, its zero
criterion, its scaling law, and invariance under isometries of the inputs and output.
-/

public noncomputable section

open Module

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local instance : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E

/-- The three-slot Hilbert–Schmidt energy of a curried continuous trilinear map, computed
using the standard orthonormal basis in each slot. It is basis-independent by
`trilinearHilbertSchmidtEnergy_eq_sum`. -/
def trilinearHilbertSchmidtEnergy (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) : ℝ :=
  ∑ i, ∑ j, ∑ k, ‖T (stdOrthonormalBasis 𝕜 E i) (stdOrthonormalBasis 𝕜 E j)
    (stdOrthonormalBasis 𝕜 E k)‖ ^ 2


/-- The three input slots may use arbitrary, independently chosen orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 E)
    (b₃ : OrthonormalBasis ι₃ 𝕜 E) (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
  let b₀ := stdOrthonormalBasis 𝕜 E
  unfold trilinearHilbertSchmidtEnergy
  calc
    _ = ∑ j, ∑ k, ∑ i, ‖T (b₀ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply] using
        LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq
          ((T.flip (b₀ j)).flip (b₀ k)).toLinearMap b₀ b₁
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (b₁ i) (b₂ j) (b₀ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply] using
        LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq
          ((T (b₁ i)).flip (b₀ k)).toLinearMap b₀ b₂
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₀ k)‖ ^ 2 := by
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simpa only [ContinuousLinearMap.coe_coe] using
        (T (b₁ i) (b₂ j)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀ b₃

/-- The three-slot energy is the sum of the one-slot Hilbert–Schmidt energies of its slices. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum_sq_hilbertSchmidtNorm
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, (T (b i) (b j)).hilbertSchmidtNorm ^ 2 := by
  rw [trilinearHilbertSchmidtEnergy_eq_sum b b b]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ContinuousLinearMap.sq_hilbertSchmidtNorm _ b.toHilbertBasis,
    ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
    ENNReal.toReal_ofReal (sq_nonneg _),
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b]
  rfl

/-- Trilinear Hilbert–Schmidt energy is homogeneous of degree two. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_smul (c : 𝕜)
    (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy (c • T) = ‖c‖ ^ 2 * trilinearHilbertSchmidtEnergy T := by
  simp [trilinearHilbertSchmidtEnergy, Finset.mul_sum, norm_smul, mul_pow]

end InnerProduct

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The three-slot contraction is nonnegative. -/
theorem trilinearHilbertSchmidtEnergy_nonneg (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) :
    0 ≤ trilinearHilbertSchmidtEnergy T :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The zero trilinear map has zero energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_zero :
    trilinearHilbertSchmidtEnergy (0 : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) = 0 := by
  simp [trilinearHilbertSchmidtEnergy]

/-- The contraction vanishes exactly when the trilinear map vanishes. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_eq_zero_iff
    (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) :
    trilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis 𝕜 E
    have hi : ∀ i, (∑ j, ∑ k, ‖T (b i) (b j) (b k)‖ ^ 2) = 0 := by
      exact fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).1
          h i (Finset.mem_univ i)
    have hij : ∀ i j, (∑ k, ‖T (b i) (b j) (b k)‖ ^ 2) = 0 := by
      exact fun i j ↦ (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).1 (hi i) j (Finset.mem_univ j)
    have hijk : ∀ i j k, T (b i) (b j) (b k) = 0 := by
      intro i j k
      apply norm_eq_zero.1
      exact sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).1
        (hij i j) k (Finset.mem_univ k))
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro j
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro k
    exact hijk i j k
  · rintro rfl
    exact trilinearHilbertSchmidtEnergy_zero

/-- Pointwise equality of output norms preserves the three-slot contraction. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F)
    (S : E →L[𝕜] E →L[𝕜] E →L[𝕜] G)
    (h : ∀ x y z, ‖T x y z‖ = ‖S x y z‖) :
    trilinearHilbertSchmidtEnergy T = trilinearHilbertSchmidtEnergy S := by
  simp only [trilinearHilbertSchmidtEnergy, h]


/-- Independent isometric changes in the input slots and an output isometry preserve energy. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_isometries {E' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E →L[𝕜] E →L[𝕜] E →L[𝕜] F) (S : E' →L[𝕜] E' →L[𝕜] E' →L[𝕜] G)
    (e₁ e₂ e₃ : E' ≃ₗᵢ[𝕜] E) (U : F →ₗᵢ[𝕜] G)
    (h : ∀ x y z, S x y z = U (T (e₁ x) (e₂ y) (e₃ z))) :
    trilinearHilbertSchmidtEnergy S = trilinearHilbertSchmidtEnergy T := by
  let b := stdOrthonormalBasis 𝕜 E'
  rw [trilinearHilbertSchmidtEnergy_eq_sum b b b S,
    trilinearHilbertSchmidtEnergy_eq_sum (b.map e₁) (b.map e₂) (b.map e₃) T]
  simp only [h, U.norm_map, OrthonormalBasis.map_apply]

end InnerProduct

end ContinuousLinearMap
