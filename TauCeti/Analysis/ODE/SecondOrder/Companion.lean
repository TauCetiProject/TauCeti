/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Companion operator for second-order equations

The Jacobi equation `y'' + R y = 0` is the first-order system `(y, v)' = (v, -R y)`.
This module provides its companion operator, linear curvature variation, norm bounds,
and smooth dependence on curvature.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open ContinuousLinearMap
open scoped ContDiff

namespace ContinuousLinearMap

section Coefficient

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The first-order coefficient of the Jacobi equation `y'' + R y = 0`. -/
def jacobiODECoeff (R : F →L[𝕜] F) : (F × F) →L[𝕜] (F × F) :=
  (ContinuousLinearMap.snd 𝕜 F F).prod (-(R.comp (ContinuousLinearMap.fst 𝕜 F F)))

@[simp]
theorem jacobiODECoeff_apply (R : F →L[𝕜] F) (z : F × F) :
    jacobiODECoeff R z = (z.2, -R z.1) := by
  simp [jacobiODECoeff]

/-- The product norm controls the second-order coefficient without dimension constants. -/
theorem norm_jacobiODECoeff_le (R : F →L[𝕜] F) :
    ‖jacobiODECoeff R‖ ≤ max 1 ‖R‖ := by
  rw [jacobiODECoeff, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_neg]
  exact max_le_max (ContinuousLinearMap.norm_snd_le 𝕜 F F)
    ((R.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg R)
      (ContinuousLinearMap.norm_fst_le 𝕜 F F)))

/-- The part of the first-order Jacobi system that depends linearly on curvature. -/
def jacobiODECoeffVariation :
    (F →L[𝕜] F) →L[𝕜] ((F × F) →L[𝕜] (F × F)) :=
  -((LinearIsometry.inr 𝕜 F F).postcomp.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜 (F × F) F F).flip (ContinuousLinearMap.fst 𝕜 F F)))

/-- Evaluation of the linear variation of the Jacobi coefficient. -/
@[simp] theorem jacobiODECoeffVariation_apply (R : F →L[𝕜] F) (z : F × F) :
    jacobiODECoeffVariation R z = (0, -R z.1) := by
  simp [jacobiODECoeffVariation, LinearIsometry.postcomp]

/-- The curvature-to-Jacobi variation operator has norm at most one. -/
theorem norm_jacobiODECoeffVariation_le :
    ‖jacobiODECoeffVariation (𝕜 := 𝕜) (F := F)‖ ≤ 1 := by
  let : NormedAddCommGroup ((F × F) →L[𝕜] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace 𝕜 ((F × F) →L[𝕜] F) := ContinuousLinearMap.toNormedSpace
  let K := (ContinuousLinearMap.compL 𝕜 (F × F) F F).flip
    (ContinuousLinearMap.fst 𝕜 F F)
  -- The local normed-map instances and K are definitionally the coefficient's operator factors.
  change ‖-((LinearIsometry.inr 𝕜 F F).postcomp.toContinuousLinearMap.comp K)‖ ≤ 1
  rw [norm_neg, LinearIsometry.norm_toContinuousLinearMap_comp]
  refine ((ContinuousLinearMap.compL 𝕜 (F × F) F F).flip.le_opNorm _).trans ?_
  rw [ContinuousLinearMap.opNorm_flip]
  exact (mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.norm_compL_le 𝕜 (F × F) F F) (norm_nonneg _)).trans
    (by simpa only [one_mul] using ContinuousLinearMap.norm_fst_le 𝕜 F F)

/-- The Jacobi coefficient is a fixed free system plus its linear curvature variation. -/
theorem jacobiODECoeff_eq_jacobiODECoeff_zero_add (R : F →L[𝕜] F) :
    jacobiODECoeff R = jacobiODECoeff (0 : F →L[𝕜] F) + jacobiODECoeffVariation R := by
  ext z <;> simp [jacobiODECoeff_apply]

/-- Adding curvature adds its linear variation to the Jacobi coefficient. -/
theorem jacobiODECoeff_add (R S : F →L[𝕜] F) :
    jacobiODECoeff (R + S) = jacobiODECoeff R + jacobiODECoeffVariation S := by
  rw [jacobiODECoeff_eq_jacobiODECoeff_zero_add (R + S),
    jacobiODECoeff_eq_jacobiODECoeff_zero_add R, map_add, add_assoc]

/-- The first-order Jacobi coefficient depends smoothly on its curvature operator. -/
theorem contDiff_jacobiODECoeff {n : ℕ∞ω} :
    ContDiff 𝕜 n (jacobiODECoeff (𝕜 := 𝕜) (F := F)) := by
  have heq : jacobiODECoeff (𝕜 := 𝕜) (F := F) =
      (fun R : F →L[𝕜] F ↦ jacobiODECoeff (0 : F →L[𝕜] F) + jacobiODECoeffVariation R) := by
    funext R
    exact jacobiODECoeff_eq_jacobiODECoeff_zero_add R
  rw [heq]
  exact contDiff_const.add (jacobiODECoeffVariation (𝕜 := 𝕜) (F := F)).contDiff

end Coefficient

end ContinuousLinearMap
