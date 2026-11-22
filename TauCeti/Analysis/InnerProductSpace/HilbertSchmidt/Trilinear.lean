/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The Hilbert–Schmidt energy of a trilinear map

The sum of the squared target norms over orthonormal bases in three input slots is independent
of each basis. This contraction uses the genuine target inner product and leaves the ordinary
operator-norm topology on curried continuous linear maps unchanged. The target need not be
finite-dimensional.
-/

public noncomputable section

open Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The three-slot Hilbert–Schmidt energy of a curried continuous trilinear map. -/
def trilinearHilbertSchmidtEnergy (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) : ℝ :=
  ∑ i, ∑ j, ∑ k, ‖T (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)
    (stdOrthonormalBasis ℝ E k)‖ ^ 2

end Basic

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The three input slots may use arbitrary, independently chosen orthonormal bases. -/
theorem trilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (b₁ : OrthonormalBasis ι₁ ℝ E) (b₂ : OrthonormalBasis ι₂ ℝ E)
    (b₃ : OrthonormalBasis ι₃ ℝ E) (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) :
    trilinearHilbertSchmidtEnergy T =
      ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
  let b₀ := stdOrthonormalBasis ℝ E
  unfold trilinearHilbertSchmidtEnergy
  calc
    _ = ∑ j, ∑ k, ∑ i, ‖T (b₀ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      exact LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq
        ((T.flip (b₀ j)).flip (b₀ k)).toLinearMap b₀ b₁
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (b₁ i) (b₀ j) (b₀ k)‖ ^ 2 := by
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (b₁ i) (b₂ j) (b₀ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      exact LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq
        ((T (b₁ i)).flip (b₀ k)).toLinearMap b₀ b₂
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₀ k)‖ ^ 2 := by
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ‖T (b₁ i) (b₂ j) (b₃ k)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      exact (T (b₁ i) (b₂ j)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀ b₃

end InnerProduct

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The three-slot contraction is nonnegative. -/
theorem trilinearHilbertSchmidtEnergy_nonneg (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) :
    0 ≤ trilinearHilbertSchmidtEnergy T :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The zero trilinear map has zero energy. -/
@[simp]
theorem trilinearHilbertSchmidtEnergy_zero :
    trilinearHilbertSchmidtEnergy (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) = 0 := by
  simp [trilinearHilbertSchmidtEnergy]

/-- The contraction vanishes exactly when the trilinear map vanishes. -/
theorem trilinearHilbertSchmidtEnergy_eq_zero_iff
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) :
    trilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis ℝ E
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
    [NormedSpace ℝ G] (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (S : E →L[ℝ] E →L[ℝ] E →L[ℝ] G)
    (h : ∀ x y z, ‖T x y z‖ = ‖S x y z‖) :
    trilinearHilbertSchmidtEnergy T = trilinearHilbertSchmidtEnergy S := by
  simp only [trilinearHilbertSchmidtEnergy, h]

end Basic

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Independent isometric changes in the input slots and an output isometry preserve energy. -/
theorem trilinearHilbertSchmidtEnergy_eq_of_isometries {E' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) (S : E' →L[ℝ] E' →L[ℝ] E' →L[ℝ] G)
    (e₁ e₂ e₃ : E' ≃ₗᵢ[ℝ] E) (U : F →ₗᵢ[ℝ] G)
    (h : ∀ x y z, S x y z = U (T (e₁ x) (e₂ y) (e₃ z))) :
    trilinearHilbertSchmidtEnergy S = trilinearHilbertSchmidtEnergy T := by
  let b := stdOrthonormalBasis ℝ E'
  rw [trilinearHilbertSchmidtEnergy_eq_sum b b b S,
    trilinearHilbertSchmidtEnergy_eq_sum (b.map e₁) (b.map e₂) (b.map e₃) T]
  simp only [h, U.norm_map, OrthonormalBasis.map_apply]

end InnerProduct

end TauCeti
