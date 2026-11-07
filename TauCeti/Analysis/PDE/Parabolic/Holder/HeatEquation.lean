/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The heat initial-data isomorphism

For `0 < α < 1`, on a finite closed slab with `T > 0`, the map
`u ↦ (∂ₜu - Δu, u(·,0))` is a continuous linear isomorphism from bounded order-two parabolic
Hölder functions to the product of bounded parabolic Hölder forcing and bounded spatial
order-two Hölder initial data. Its inverse is the sum of the Cauchy potential of the initial
datum and the Duhamel potential of the forcing.
The equation includes the one-sided time derivatives at both endpoints.

This is the starting inverse for the method of continuity for variable-coefficient parabolic
problems. The inverse has operator norm at most `C (1 + T)`, where `C` is independent of the
positive time horizon `T`. The construction uses the existing heat potentials and the
whole-space comparison theorem for uniqueness, with no condition at spatial infinity beyond
boundedness.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Corollary 4.2.10.
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime InnerProductSpace Laplacian
open scoped NNReal

variable {ι : Type*} [Fintype ι] {α T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- The heat operator `u ↦ ∂ₜu - Δu` on a closed slab, as a bounded map between parabolic
Hölder spaces. -/
def heatOperatorL (hα : α ≤ 1) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ := by
  classical
  exact euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j))
    (fun _ ↦ 0) 0

/-- The heat operator is the time derivative minus the Laplacian of the spatial slice. -/
@[simp]
theorem heatOperatorL_apply (hα : α ≤ 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    heatOperatorL hα u p = timeDerivL u p -
      Δ (fun y ↦ u (slabMk y (slabTime p))) (p : ParabolicSpaceTime _).space := by
  classical
  have hΔ := laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y ↦ u (slabMk y (slabTime p))) (EuclideanSpace.basisFun ι ℝ)
  rw [heatOperatorL, euclideanParabolicOperatorL_apply]
  simp only [HolderSpace.const_apply, HolderSpace.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, Matrix.one_apply, ite_mul, one_mul]
  congr 1
  rw [hΔ]
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]

/-- The heat equation and initial trace, in the order `(forcing, initial datum)`. -/
def heatInitialDataL (hα : α ≤ 1) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  (heatOperatorL hα).prod (spatialTraceL ⟨0, left_mem_Icc.2 hT.le⟩)

/-- Evaluation of the heat initial-data operator. This expansion is not a simp rule, so
composition with the solution operator simplifies by the inverse identities instead. -/
theorem heatInitialDataL_apply (hα : α ≤ 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    heatInitialDataL hα u =
      (heatOperatorL hα u, u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) := by
  simp [heatInitialDataL, spatialTraceL_apply]

/-- The bounded solution operator: Cauchy potential of the initial datum plus Duhamel
potential of the forcing. -/
def heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    (HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) →L[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT :=
  (heatCauchyPotentialL hT le_rfl).comp (ContinuousLinearMap.snd ℝ _ _) +
    (heatDuhamelPotentialL hα₀ hα₁ hT).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The solution operator is the sum of the two heat potentials. This expansion is not a
simp rule, so the inverse identities retain their compositional normal form. -/
theorem heatSolutionL_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    heatSolutionL hα₀ hα₁ hT (f, g) =
      heatCauchyPotentialL hT le_rfl g + heatDuhamelPotentialL hα₀ hα₁ hT f := by
  simp [heatSolutionL]

/-- The constructed solution attains the forcing and the initial datum. -/
@[simp]
theorem heatInitialDataL_heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    heatInitialDataL hα₁.le (heatSolutionL hα₀ hα₁ hT d) = d := by
  rcases d with ⟨f, g⟩
  rw [heatSolutionL_apply, heatInitialDataL_apply]
  apply Prod.ext
  · ext p
    rw [map_add, HolderSpace.add_apply, heatOperatorL_apply, heatOperatorL_apply,
      timeDerivL_heatCauchyPotentialL_eq_laplacian,
      timeDerivL_heatDuhamelPotentialL_eq_laplacian_add]
    ring
  · simp [spatialTrace_add, spatialTrace_heatCauchyPotentialL_left]

/-- A bounded classical heat solution is determined by its forcing and initial datum. -/
theorem heatInitialDataL_injective (hα : α ≤ 1) :
    Function.Injective (heatInitialDataL (ι := ι) (hT := hT) hα) := by
  classical
  intro u v h
  simp only [heatInitialDataL_apply, Prod.mk.injEq] at h
  obtain ⟨hP, hg⟩ := h
  simp only [heatOperatorL] at hP
  refine eq_of_euclideanParabolicOperatorL_eq hα (fun p ξ ↦ ?_) hP (fun x ↦ ?_)
  · have hone : (Matrix.of fun i j ↦
        (HolderSpace.const ((1 : Matrix ι ι ℝ) i j) :
          HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) p) = 1 := by
      ext i j
      simp
    rw [hone, PDE.toQuadraticForm'_one]
    positivity
  · simpa only [spatialTrace_apply] using
      congrArg (fun g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ ↦ g x) hg

/-- Reconstructing from the heat equation and the initial trace recovers the original
function, not just its terminal value. -/
@[simp]
theorem heatSolutionL_heatInitialDataL (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    heatSolutionL hα₀ hα₁ hT (heatInitialDataL hα₁.le u) = u :=
  heatInitialDataL_injective hα₁.le (heatInitialDataL_heatSolutionL hα₀ hα₁ _)

/-- **The heat initial-data isomorphism.** Bounded parabolic Hölder forcing and bounded
`C^{2,α}` initial data determine a unique bounded `C^{2+α,1+α/2}` heat solution. -/
def heatInitialDataEquiv (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  ContinuousLinearEquiv.equivOfInverse (heatInitialDataL hα₁.le) (heatSolutionL hα₀ hα₁ hT)
    (heatSolutionL_heatInitialDataL hα₀ hα₁) (heatInitialDataL_heatSolutionL hα₀ hα₁)

/-- The forward isomorphism records precisely the equation and initial trace. -/
@[simp]
theorem heatInitialDataEquiv_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    heatInitialDataEquiv hα₀ hα₁ hT u = heatInitialDataL hα₁.le u := by
  simp [heatInitialDataEquiv]

/-- The inverse isomorphism is the constructed heat solution operator. -/
@[simp]
theorem heatInitialDataEquiv_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (heatInitialDataEquiv hα₀ hα₁ hT).symm d = heatSolutionL hα₀ hα₁ hT d := by
  simp [heatInitialDataEquiv]

/-- The inverse has norm `O(1 + T)`, with a constant depending only on the spatial space
and Hölder exponent, not on the positive horizon or the data. -/
theorem exists_norm_heatSolutionL_le (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C, ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T),
      ‖heatSolutionL (ι := ι) hα₀ hα₁ hT‖ ≤ C * (1 + T) := by
  obtain ⟨C, hC⟩ := exists_norm_heatDuhamelPotentialL_le (α := α) (EuclideanSpace ℝ ι) ℝ hα₀ hα₁
  let A : ℝ := (1 + Module.finrank ℝ (EuclideanSpace ℝ ι)) *
    (1 + heatKernelMoment (EuclideanSpace ℝ ι) α)
  have hA : 0 ≤ A := by positivity
  refine ⟨A + max C 0, fun T hT ↦ ?_⟩
  have hS := norm_heatCauchyPotentialL_le (α := α) (E := EuclideanSpace ℝ ι)
    (F := ℝ) hT le_rfl
  let D := HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ
  let G := CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ
  have h₁ : ‖(heatCauchyPotentialL (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) hT
      le_rfl).comp (ContinuousLinearMap.snd ℝ D G)‖ ≤ A := by
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ D G))).trans hS
  have h₂ : ‖(heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁ hT).comp
      (ContinuousLinearMap.fst ℝ D G)‖ ≤ C * (1 + T) := by
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ D G))).trans
        (hC T hT)
  have hsum := norm_add_le
    ((heatCauchyPotentialL (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) hT le_rfl).comp
      (ContinuousLinearMap.snd ℝ D G))
    ((heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁ hT).comp
      (ContinuousLinearMap.fst ℝ D G))
  rw [← heatSolutionL] at hsum
  refine hsum.trans ((add_le_add h₁ h₂).trans ?_)
  have hTA : A ≤ A * (1 + T) := le_mul_of_one_le_right hA (by linarith [T.coe_nonneg])
  have hC' : C * (1 + T) ≤ max C 0 * (1 + T) := by gcongr; exact le_max_left _ _
  nlinarith

end TauCeti.ParabolicC2HolderSpace
