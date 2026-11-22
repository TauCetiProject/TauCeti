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
# The Hilbert–Schmidt energy of a bilinear map

The energy of a continuous bilinear map is the sum of squared output norms over orthonormal
bases in both input slots. It is independent of the chosen bases when the output is an inner
product space. This is the squared Hilbert–Schmidt norm of tensors such as a second fundamental
form; the output need not be finite-dimensional.

The main results are `ContinuousLinearMap.bilinearHilbertSchmidtEnergy_eq_sum`, its zero
criterion, its scaling law, and invariance under isometries of the inputs and output.
-/

public noncomputable section

open Module

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E E₂ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local instance : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
local instance : CompleteSpace E₂ := FiniteDimensional.completeSpace 𝕜 E₂

/-- The full ordered two-slot Hilbert–Schmidt energy of a continuous bilinear map, computed
using the standard orthonormal basis in each slot. It is independent of that basis by
`bilinearHilbertSchmidtEnergy_eq_sum`. -/
def bilinearHilbertSchmidtEnergy (T : E →L[𝕜] E₂ →L[𝕜] F) : ℝ :=
  ∑ i, ∑ j, ‖T (stdOrthonormalBasis 𝕜 E i) (stdOrthonormalBasis 𝕜 E₂ j)‖ ^ 2


/-- The two input slots may use arbitrary, independently chosen orthonormal bases. -/
theorem bilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = ∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2 := by
  let b₀ := stdOrthonormalBasis 𝕜 E
  let b₀' := stdOrthonormalBasis 𝕜 E₂
  unfold bilinearHilbertSchmidtEnergy
  calc
    _ = ∑ j, ∑ i, ‖T (b₀ i) (b₀' j)‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖T (b₁ i) (b₀' j)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply] using
        (T.flip (b₀' j)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀ b₁
    _ = ∑ i, ∑ j, ‖T (b₁ i) (b₀' j)‖ ^ 2 := Finset.sum_comm
    _ = ∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simpa only [ContinuousLinearMap.coe_coe] using
        (T (b₁ i)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀' b₂

/-- Sum of the ordinary one-slot Hilbert–Schmidt energies of the slices. -/
theorem bilinearHilbertSchmidtEnergy_eq_sum_sq_hilbertSchmidtNorm
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = ∑ i, (T (b₁ i)).hilbertSchmidtNorm ^ 2 := by
  rw [bilinearHilbertSchmidtEnergy_eq_sum b₁ b₂]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.sq_hilbertSchmidtNorm _ b₂.toHilbertBasis,
    ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
    ENNReal.toReal_ofReal (sq_nonneg _),
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b₂]
  simp only [ContinuousLinearMap.coe_coe]

/-- Bilinear Hilbert–Schmidt energy is homogeneous of degree two. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_smul (c : 𝕜) (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy (c • T) = ‖c‖ ^ 2 * bilinearHilbertSchmidtEnergy T := by
  simp [bilinearHilbertSchmidtEnergy, Finset.mul_sum, norm_smul, mul_pow]

/-- The two-slot contraction is nonnegative. -/
theorem bilinearHilbertSchmidtEnergy_nonneg (T : E →L[𝕜] E₂ →L[𝕜] F) :
    0 ≤ bilinearHilbertSchmidtEnergy T :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The zero bilinear map has zero energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_zero :
    bilinearHilbertSchmidtEnergy (0 : E →L[𝕜] E₂ →L[𝕜] F) = 0 := by
  simp [bilinearHilbertSchmidtEnergy]

/-- The contraction vanishes exactly when the bilinear map vanishes. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_eq_zero_iff (T : E →L[𝕜] E₂ →L[𝕜] F) :
    bilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis 𝕜 E
    let b₂ := stdOrthonormalBasis 𝕜 E₂
    have hi : ∀ i, (∑ j, ‖T (b i) (b₂ j)‖ ^ 2) = 0 := by
      exact fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).1 h i (Finset.mem_univ i)
    have hij : ∀ i j, T (b i) (b₂ j) = 0 := by
      intro i j
      apply norm_eq_zero.1
      exact sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).1
        (hi i) j (Finset.mem_univ j))
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b₂.toBasis.ext
    intro j
    exact hij i j
  · rintro rfl
    exact bilinearHilbertSchmidtEnergy_zero

/-- Pointwise equality of output norms preserves the two-slot contraction. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (T : E →L[𝕜] E₂ →L[𝕜] F)
    (S : E →L[𝕜] E₂ →L[𝕜] G)
    (h : ∀ x y, ‖T x y‖ = ‖S x y‖) :
    bilinearHilbertSchmidtEnergy T = bilinearHilbertSchmidtEnergy S := by
  simp only [bilinearHilbertSchmidtEnergy, h]


/-- Independent input isometric equivalences and an output isometry preserve energy. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_isometries {E' E₂' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup E₂'] [InnerProductSpace 𝕜 E₂'] [FiniteDimensional 𝕜 E₂']
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E →L[𝕜] E₂ →L[𝕜] F) (S : E' →L[𝕜] E₂' →L[𝕜] G)
    (e₁ : E' ≃ₗᵢ[𝕜] E) (e₂ : E₂' ≃ₗᵢ[𝕜] E₂) (U : F →ₗᵢ[𝕜] G)
    (h : ∀ x y, S x y = U (T (e₁ x) (e₂ y))) :
    bilinearHilbertSchmidtEnergy S = bilinearHilbertSchmidtEnergy T := by
  let b := stdOrthonormalBasis 𝕜 E'
  let b₂ := stdOrthonormalBasis 𝕜 E₂'
  rw [bilinearHilbertSchmidtEnergy_eq_sum b b₂ S,
    bilinearHilbertSchmidtEnergy_eq_sum (b.map e₁) (b₂.map e₂) T]
  simp only [h, U.norm_map, OrthonormalBasis.map_apply]

end InnerProduct

end ContinuousLinearMap
