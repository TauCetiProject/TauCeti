/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.CompSpatial
public import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Constant-coefficient parabolic operators as the heat operator in linear coordinates

Let `A` be a constant matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and write
`P_A u = ∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. There is a linear automorphism `e` of `ℝⁿ`, stretching lengths by
at most `√Λ` and with inverse stretching lengths by at most `1 / √λ`, such that

`P_I (u ∘ (e × id)) = (P_A u) ∘ (e × id)`

for every `u ∈ C_b^{2+α,1+α/2}`, where `P_I = ∂ₜ - Δ` is the heat operator. As `u ↦ u ∘ (e × id)`
is an isomorphism (`TauCeti.ParabolicC2HolderSpace.compSpatialCLE`) whose norm and inverse norm
are bounded in terms of `λ`, `Λ` and `α` (`TauCeti.ParabolicC2HolderSpace.norm_compSpatialL_le`),
this is the identity through which the solution theory of the heat operator in parabolic Hölder
spaces passes to `P_A`. The pointwise identity is the elliptic one,
`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`, applied to each time slice.

## Main declarations

* `ParabolicC2HolderSpace.exists_continuousLinearEquiv_euclideanParabolicOperatorL_compSpatialL_eq`:
  a constant-coefficient operator is the heat operator in suitable linear coordinates.
* `ParabolicC2HolderSpace.euclideanParabolicOperatorL_compSpatialL_symm_eq`: the same identity
  read through the inverse coordinate change.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

namespace ParabolicC2HolderSpace

variable {α : ℝ≥0} {a b : ℝ} {hab : a < b} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A constant-coefficient parabolic operator is the heat operator in suitable linear
coordinates.** Let `A` be a square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let
`P_A u = ∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` act on `C_b^{2+α,1+α/2}(ℝⁿ × [a, b])`. There is a continuous linear
automorphism `e` of `ℝⁿ = EuclideanSpace ℝ ι`, with `‖e⁻¹ x‖ ≤ ‖x‖ / √λ` and `‖e y‖ ≤ √Λ ‖y‖`, such
that the heat operator `P_I = ∂ₜ - Δ` satisfies

`P_I (u ∘ (e × id)) = (P_A u) ∘ (e × id)`

for every `u`. Since `u ↦ u ∘ (e × id)` is an isomorphism (`compSpatialCLE`), this transfers
solvability and estimates for the heat operator to `P_A`. -/
theorem exists_continuousLinearEquiv_euclideanParabolicOperatorL_compSpatialL_eq (hα : α ≤ 1)
    {A : Matrix ι ι ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
      (∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) ∧ (∀ y, ‖e y‖ ≤ √Lam * ‖y‖) ∧
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab,
        euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
            (compSpatialL α ℝ hab (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) u) =
          HolderSpace.compLipschitzL _
            (lipschitzWith_slabSpaceMap (e : _ →L[ℝ] _).lipschitzWith)
            (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u) := by
  obtain ⟨e, he₁, he₂, he⟩ :=
    PDE.exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  refine ⟨e, he₁, he₂, fun u ↦ HolderSpace.ext fun p ↦ ?_⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- On the time slice through `t`, both sides are the elliptic identity for `u(·, t)`.
  have key := he _ x (u.contDiff_spatialSlice t).contDiffAt
  rw [laplacian_comp_continuousLinearEquiv_right_apply e (EuclideanSpace.basisFun ι ℝ)] at key
  simp only [u.iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply, u.fderiv_fderiv_eq, smul_eq_mul] at key
  simp only [euclideanParabolicOperatorL_apply, HolderSpace.compLipschitzL_apply,
    HolderSpace.const_apply, Pi.zero_apply, HolderSpace.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL,
    slabSpaceMap_slabMk, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
    Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, key]

/-- The coordinate change of
`exists_continuousLinearEquiv_euclideanParabolicOperatorL_compSpatialL_eq` in operator-norm form:
both `e` and `e⁻¹` have operator norm at most `max 1 (max √Λ (1 / √λ))`, which is how the change
of variables enters bounds on `u ↦ u ∘ (e × id)` (`norm_compSpatialL_le_of_norm_le`). -/
theorem exists_continuousLinearEquiv_norm_le_euclideanParabolicOperatorL_compSpatialL_eq
    (hα : α ≤ 1) {A : Matrix ι ι ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
      ‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ max 1 (max √Lam (√lam)⁻¹) ∧
      ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ max 1 (max √Lam (√lam)⁻¹) ∧
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab,
        euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
            (compSpatialL α ℝ hab (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) u) =
          HolderSpace.compLipschitzL _
            (lipschitzWith_slabSpaceMap (e : _ →L[ℝ] _).lipschitzWith)
            (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u) := by
  obtain ⟨e, he₁, he₂, he⟩ :=
    exists_continuousLinearEquiv_euclideanParabolicOperatorL_compSpatialL_eq hα hlam hA hA'
  have hK₀ : 0 ≤ max 1 (max √Lam (√lam)⁻¹) := zero_le_one.trans (le_max_left _ _)
  exact ⟨e,
    ContinuousLinearMap.opNorm_le_bound _ hK₀ fun x ↦ (he₂ x).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg x)),
    ContinuousLinearMap.opNorm_le_bound _ hK₀ fun x ↦ (he₁ x).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg x)),
    he⟩

/-- **The inverse coordinate change.** If `P_I (u ∘ (e × id)) = (P_A u) ∘ (e × id)` for every `u`,
then `P_A (w ∘ (e⁻¹ × id)) = (P_I w) ∘ (e⁻¹ × id)` for every `w`: solutions of the heat equation
transported by `e⁻¹` solve the equation for `P_A`. -/
theorem euclideanParabolicOperatorL_compSpatialL_symm_eq (hα : α ≤ 1) {A : Matrix ι ι ℝ}
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (he : ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab,
      euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
          (compSpatialL α ℝ hab (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) u) =
        HolderSpace.compLipschitzL _
          (lipschitzWith_slabSpaceMap (e : _ →L[ℝ] _).lipschitzWith)
          (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u))
    (w : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab) :
    euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0
        (compSpatialL α ℝ hab (e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) w) =
      HolderSpace.compLipschitzL _
        (lipschitzWith_slabSpaceMap (e.symm : _ →L[ℝ] _).lipschitzWith)
        (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
          w) := by
  have h := he (compSpatialL α ℝ hab (e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) w)
  rw [← compSpatialL_comp, ContinuousLinearEquiv.coe_symm_comp_coe, compSpatialL_id] at h
  ext p
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  have hp := congrArg (fun f ↦ f (slabMk (e.symm x) t)) h
  simpa only [HolderSpace.compLipschitzL_apply, slabSpaceMap_slabMk,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hp.symm

end ParabolicC2HolderSpace

end TauCeti
