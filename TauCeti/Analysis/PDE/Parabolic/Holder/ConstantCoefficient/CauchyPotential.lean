/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.ConstantCoefficient.Basic
public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyPotential
public import TauCeti.Analysis.Holder.CompLinear

/-!
# The homogeneous constant-coefficient parabolic Cauchy problem

For a constant elliptic matrix `A`, the problem `u_t - A : D²u = 0`, `u(·,0) = g` has a unique
solution in the bounded order-two parabolic Hölder space for every `g ∈ C_b^{2,α}`. The solution
operator is linear and bounded by a constant depending only on the ellipticity bounds, the
exponent and the dimension, uniformly over all finite time horizons.

The construction transports the Cauchy heat potential through the linear coordinate change
reducing the principal part to the Laplacian. Both the initial datum and the solution are
transported, in opposite directions. This supplies the initial-data component of the
constant-coefficient parabolic solution operator; nonzero forcing is not treated here.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (linear reduction of a constant elliptic principal part).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] {T : ℝ}

private def transportedCauchyL (hT : 0 < T)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT :=
  (compSpatialL α ℝ hT e.symm.toContinuousLinearMap).comp
    ((heatCauchyPotentialL hT le_rfl).comp (CkHolderSpace.compLinearL e.toContinuousLinearMap))

private theorem spatialTrace_transportedCauchyL (hT : 0 < T)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (g) :
    (transportedCauchyL (α := α) hT e g).spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = g := by
  simp only [transportedCauchyL, ContinuousLinearMap.comp_apply, spatialTrace_compSpatialL,
    spatialTrace_heatCauchyPotentialL_left]
  ext x
  simp

private theorem operator_transportedCauchyL [DecidableEq ι] (hT : 0 < T) (hα : α ≤ 1)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ)
    (he : ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
          (compSpatialL α ℝ hT e.toContinuousLinearMap u) =
        HolderSpace.compLipschitzL _
          (lipschitzWith_slabSpaceMap e.toContinuousLinearMap.lipschitzWith)
          (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u)) (g) :
    euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0
      (transportedCauchyL hT e g) = 0 := by
  rw [transportedCauchyL, ContinuousLinearMap.comp_apply,
    euclideanParabolicOperatorL_compSpatialL_symm_eq hα e he, ContinuousLinearMap.comp_apply,
    euclideanParabolicOperatorL_heatCauchyPotentialL hα hT le_rfl, map_zero]

private theorem norm_transportedCauchyL_le (hT : 0 < T)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {K : ℝ} (hK : 1 ≤ K)
    (he : ‖e.toContinuousLinearMap‖ ≤ K) (hei : ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    ‖transportedCauchyL (α := α) hT e‖ ≤
      (K ^ 2 * K ^ (α : ℝ)) *
        ((1 + Module.finrank ℝ (EuclideanSpace ℝ ι)) *
          (1 + (heatKernelMoment (EuclideanSpace ℝ ι) α : ℝ))) * (K ^ 2 * K ^ (α : ℝ)) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hJ : ‖CkHolderSpace.compLinearL (k := 2) (α := α) (F := ℝ) e.toContinuousLinearMap‖ ≤
      K ^ 2 * K ^ (α : ℝ) := by
    refine (CkHolderSpace.norm_compLinearL_le _).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (max_le hK he) 2)
      (max_le (Real.one_le_rpow hK (by positivity))
        (Real.rpow_le_rpow (norm_nonneg _) he (by positivity))) (by positivity) (by positivity)
  have hR := norm_compSpatialL_le_of_norm_le α ℝ hT hK hei
  have hH := norm_heatCauchyPotentialL_le (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) hT le_rfl
  have h := (ContinuousLinearMap.opNorm_comp_le (compSpatialL α ℝ hT e.symm.toContinuousLinearMap)
      ((heatCauchyPotentialL hT le_rfl).comp
        (CkHolderSpace.compLinearL e.toContinuousLinearMap))).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  have hmul := mul_le_mul hR (mul_le_mul hH hJ (by positivity) (by positivity))
    (by positivity) (by positivity)
  exact h.trans (by nlinarith only [hmul])

/-- **The bounded solution operator for the homogeneous constant-coefficient Cauchy problem.**
For fixed positive lower ellipticity bound `lam`, upper bound `Lam` and exponent `α ≤ 1`,
one constant controls all matrices with these bounds and all finite positive horizons.
The equivalence characterizes the unique solution, with initial trace in the spatial sum-norm
space `C_b^{2,α}`. No symmetry of the matrix is needed: only its symmetric part enters the
operator. -/
theorem exists_solutionOperator_euclideanParabolicOperatorL_const [DecidableEq ι] (hα : α ≤ 1)
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix ι ι ℝ,
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ (T : ℝ) (hT : 0 < T),
      ∃ L : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →L[ℝ]
          ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖L‖ ≤ C ∧ ∀ g u,
          (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u = 0 ∧
            u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = g) ↔ u = L g := by
  let K := max 1 (max (Real.sqrt Lam) (Real.sqrt lam)⁻¹)
  let D := K ^ 2 * K ^ (α : ℝ)
  let H := (1 + Module.finrank ℝ (EuclideanSpace ℝ ι)) *
    (1 + (heatKernelMoment (EuclideanSpace ℝ ι) α : ℝ))
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  refine ⟨D * H * D, by positivity, fun A hA hA' T hT ↦ ?_⟩
  obtain ⟨e, hen, hein, he⟩ :=
    exists_continuousLinearEquiv_norm_le_euclideanParabolicOperatorL_compSpatialL_eq
      (hab := hT) hα hlam hA hA'
  refine ⟨transportedCauchyL hT e, norm_transportedCauchyL_le hT e hK hen hein,
    fun g u ↦ ⟨fun hu ↦ ?_, fun hu ↦ hu ▸
      ⟨operator_transportedCauchyL hT hα e A he g, spatialTrace_transportedCauchyL hT e g⟩⟩⟩
  have hP := operator_transportedCauchyL hT hα e A he g
  refine eq_of_euclideanParabolicOperatorL_eq hα
    (a := fun i j ↦ HolderSpace.const (A i j)) (b := 0) (c := 0)
    (fun p ξ ↦ ?_) (hu.1.trans hP.symm) fun x ↦ ?_
  · have hmatrix : (Matrix.of fun i j ↦ HolderSpace.const (α := α) (A i j) p) = A := by
      ext i j
      simp
    rw [hmatrix]
    exact (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (hA ξ)
  · have hx := congrArg (fun f : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ ↦ f x)
      (hu.2.trans (spatialTrace_transportedCauchyL hT e g).symm)
    simpa only [spatialTrace_apply] using hx

end TauCeti.ParabolicC2HolderSpace
