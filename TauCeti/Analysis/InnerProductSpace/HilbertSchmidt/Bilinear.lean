/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The Hilbert–Schmidt energy of a bilinear map

The sum of the squared target norms over orthonormal bases in two input slots is independent
of both bases. The contraction uses the genuine target inner product while retaining the
ordinary topology on curried continuous linear maps. The target need not be finite-dimensional.
-/

public noncomputable section

open Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full ordered two-slot Hilbert–Schmidt energy of a continuous bilinear map. -/
def bilinearHilbertSchmidtEnergy (T : E →L[ℝ] E →L[ℝ] F) : ℝ :=
  ∑ i, ∑ j, ‖T (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖ ^ 2

end Basic

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The two input slots may use arbitrary, independently chosen orthonormal bases. -/
theorem bilinearHilbertSchmidtEnergy_eq_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ ℝ E) (b₂ : OrthonormalBasis ι₂ ℝ E)
    (T : E →L[ℝ] E →L[ℝ] F) :
    bilinearHilbertSchmidtEnergy T = ∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2 := by
  let b₀ := stdOrthonormalBasis ℝ E
  unfold bilinearHilbertSchmidtEnergy
  calc
    _ = ∑ j, ∑ i, ‖T (b₀ i) (b₀ j)‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖T (b₁ i) (b₀ j)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact (T.flip (b₀ j)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀ b₁
    _ = ∑ i, ∑ j, ‖T (b₁ i) (b₀ j)‖ ^ 2 := Finset.sum_comm
    _ = ∑ i, ∑ j, ‖T (b₁ i) (b₂ j)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (T (b₁ i)).toLinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq b₀ b₂

end InnerProduct

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The two-slot contraction is nonnegative. -/
theorem bilinearHilbertSchmidtEnergy_nonneg (T : E →L[ℝ] E →L[ℝ] F) :
    0 ≤ bilinearHilbertSchmidtEnergy T :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The zero bilinear map has zero energy. -/
@[simp]
theorem bilinearHilbertSchmidtEnergy_zero :
    bilinearHilbertSchmidtEnergy (0 : E →L[ℝ] E →L[ℝ] F) = 0 := by
  simp [bilinearHilbertSchmidtEnergy]

/-- The contraction vanishes exactly when the bilinear map vanishes. -/
theorem bilinearHilbertSchmidtEnergy_eq_zero_iff (T : E →L[ℝ] E →L[ℝ] F) :
    bilinearHilbertSchmidtEnergy T = 0 ↔ T = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis ℝ E
    have hi : ∀ i, (∑ j, ‖T (b i) (b j)‖ ^ 2) = 0 := by
      exact fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).1 h i (Finset.mem_univ i)
    have hij : ∀ i j, T (b i) (b j) = 0 := by
      intro i j
      apply norm_eq_zero.1
      exact sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).1
        (hi i) j (Finset.mem_univ j))
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro j
    exact hij i j
  · rintro rfl
    exact bilinearHilbertSchmidtEnergy_zero

/-- Pointwise equality of output norms preserves the two-slot contraction. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_norm_eq {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : E →L[ℝ] E →L[ℝ] F) (S : E →L[ℝ] E →L[ℝ] G)
    (h : ∀ x y, ‖T x y‖ = ‖S x y‖) :
    bilinearHilbertSchmidtEnergy T = bilinearHilbertSchmidtEnergy S := by
  simp only [bilinearHilbertSchmidtEnergy, h]

end Basic

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Independent input isometric equivalences and an output isometry preserve energy. -/
theorem bilinearHilbertSchmidtEnergy_eq_of_isometries {E' G : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (T : E →L[ℝ] E →L[ℝ] F) (S : E' →L[ℝ] E' →L[ℝ] G)
    (e₁ e₂ : E' ≃ₗᵢ[ℝ] E) (U : F →ₗᵢ[ℝ] G)
    (h : ∀ x y, S x y = U (T (e₁ x) (e₂ y))) :
    bilinearHilbertSchmidtEnergy S = bilinearHilbertSchmidtEnergy T := by
  let b := stdOrthonormalBasis ℝ E'
  rw [bilinearHilbertSchmidtEnergy_eq_sum b b S,
    bilinearHilbertSchmidtEnergy_eq_sum (b.map e₁) (b.map e₂) T]
  simp only [h, U.norm_map, OrthonormalBasis.map_apply]

end InnerProduct

end TauCeti
