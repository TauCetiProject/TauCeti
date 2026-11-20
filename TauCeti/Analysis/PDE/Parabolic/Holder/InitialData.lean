/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Perturbations of the parabolic initial-data operator

The operator `initialDataL` sends a bounded order-two parabolic Hölder function to its
forcing and initial spatial trace. Its difference for two coefficient triples has exactly the
norm of the difference of their parabolic operators: the initial traces cancel.

Consequently, invertibility persists whenever the coefficient perturbation, measured by
`‖A - A'‖ + 24 (‖B - B'‖ + ‖C - C'‖)`, is smaller than the reciprocal of a bound for the
old solution operator. The new inverse has the quantitative Neumann bound. This supplies the
openness step in continuation of parabolic Cauchy problems, without assuming an a priori
estimate for the perturbed equation.

The heat initial-data isomorphism can serve as the reference problem. The statements include
the one-sided endpoint time derivatives of the closed-slab spaces.

The perturbation argument uses `ContinuousLinearMap.IsInvertible.of_mul_norm_sub_lt` and
its inverse-norm estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 4 (continuation of the parabolic Cauchy problem).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-- The forcing and initial spatial trace of a parabolic Hölder function, in that order. -/
def initialDataL (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)) :
    ParabolicC2HolderSpace α E F ht →L[ℝ]
      HolderSpace α (slab (E := E) t₀ t₁) F × CkHolderSpace 2 α E F :=
  (parabolicOperatorL hα A B C).prod (spatialTraceL ⟨t₀, left_mem_Icc.2 ht.le⟩)

variable (hα : α ≤ 1)
  {A A' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B B' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C C' : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}

/-- The data operator pairs the parabolic operator with the initial trace operator. -/
theorem initialDataL_def :
    initialDataL (ht := ht) hα A B C =
      (parabolicOperatorL hα A B C).prod (spatialTraceL ⟨t₀, left_mem_Icc.2 ht.le⟩) := (rfl)

/-- The data of a function consist of its forcing and its initial spatial trace. -/
theorem initialDataL_apply (u : ParabolicC2HolderSpace α E F ht) :
    initialDataL hα A B C u =
      (parabolicOperatorL hα A B C u, u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩) := by
  simp [initialDataL_def, spatialTraceL_apply]

/-- The first data component is the parabolic operator. -/
@[simp]
theorem initialDataL_fst (u : ParabolicC2HolderSpace α E F ht) :
    (initialDataL hα A B C u).1 = parabolicOperatorL hα A B C u := (rfl)

/-- The second data component is the initial spatial trace. -/
@[simp]
theorem initialDataL_snd (u : ParabolicC2HolderSpace α E F ht) :
    (initialDataL hα A B C u).2 = u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ := by
  simp [initialDataL, spatialTraceL_apply]

/-- The data operator has the same coefficient bound as its parabolic component. -/
theorem norm_initialDataL_le :
    ‖initialDataL (ht := ht) hα A B C‖ ≤ 1 + ‖A‖ + 24 * (‖B‖ + ‖C‖) := by
  rw [initialDataL_def, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le (norm_parabolicOperatorL_le hα)
    ((norm_spatialTraceL_le_one _).trans (by
      linarith [norm_nonneg A, norm_nonneg B, norm_nonneg C]))

/-- Initial traces cancel in the difference of two data operators. -/
theorem initialDataL_sub_initialDataL :
    initialDataL (ht := ht) hα A B C - initialDataL hα A' B' C' =
      (parabolicOperatorL (ht := ht) hα A B C - parabolicOperatorL hα A' B' C').prod 0 := by
  ext u <;> simp [initialDataL_apply]

/-- Initial traces cancel in a difference of data operators, so their inclusion does not
increase the perturbation norm. -/
theorem norm_initialDataL_sub :
    ‖initialDataL (ht := ht) hα A B C - initialDataL hα A' B' C'‖ =
      ‖parabolicOperatorL (ht := ht) hα A B C - parabolicOperatorL hα A' B' C'‖ := by
  rw [initialDataL_sub_initialDataL, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)]

/-- A coefficient perturbation has the same explicit bound for the full initial-data operator
as for its parabolic component. -/
theorem norm_initialDataL_sub_le :
    ‖initialDataL (ht := ht) hα A B C - initialDataL hα A' B' C'‖ ≤
      ‖A - A'‖ + 24 * (‖B - B'‖ + ‖C - C'‖) := by
  rw [norm_initialDataL_sub]
  exact norm_parabolicOperatorL_sub_le hα

variable [CompleteSpace F]

/-- **Openness of solvability in Hölder coefficient norm.** A sufficiently small perturbation
of an invertible initial-data operator remains invertible. No ellipticity assumption is needed
in addition to invertibility of the reference problem. -/
theorem isInvertible_initialDataL_of_mul_norm_sub_lt
    (h : (initialDataL (ht := ht) hα A B C).IsInvertible) {M : ℝ}
    (hM : ‖(initialDataL (ht := ht) hα A B C).inverse‖ ≤ M)
    (hsmall : M * (‖A' - A‖ + 24 * (‖B' - B‖ + ‖C' - C‖)) < 1) :
    (initialDataL (ht := ht) hα A' B' C').IsInvertible := by
  apply h.of_mul_norm_sub_lt hM
  exact (mul_le_mul_of_nonneg_left (norm_initialDataL_sub_le hα)
    ((norm_nonneg _).trans hM)).trans_lt hsmall

/-- **The quantitative solution-operator bound after perturbation.** With coefficient distance
`δ`, the inverse norm is at most `M / (1 - M δ)`. -/
theorem norm_inverse_initialDataL_le_of_mul_norm_sub_lt
    (h : (initialDataL (ht := ht) hα A B C).IsInvertible) {M : ℝ}
    (hM : ‖(initialDataL (ht := ht) hα A B C).inverse‖ ≤ M)
    (hsmall : M * (‖A' - A‖ + 24 * (‖B' - B‖ + ‖C' - C‖)) < 1) :
    ‖(initialDataL (ht := ht) hα A' B' C').inverse‖ ≤
      M / (1 - M * (‖A' - A‖ + 24 * (‖B' - B‖ + ‖C' - C‖))) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hdist := mul_le_mul_of_nonneg_left
    (norm_initialDataL_sub_le (ht := ht) (A := A') (B := B') (C := C')
      (A' := A) (B' := B) (C' := C) hα) hM0
  exact (h.norm_inverse_le_of_mul_norm_sub_lt hM (hdist.trans_lt hsmall)).trans
    (div_le_div_of_nonneg_left hM0 (sub_pos.2 hsmall) (by linarith))

end TauCeti.ParabolicC2HolderSpace
