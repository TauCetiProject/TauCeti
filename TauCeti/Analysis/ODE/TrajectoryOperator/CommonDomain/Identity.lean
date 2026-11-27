/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# The trajectory operator over the identity embedding

Over the common domain `F` embedded in itself by the identity, the common-domain trajectory
operator `u ↦ (1 ∘ u)' + A u` (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`) is the
trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)` (`TauCeti.WeakDerivStep.trajectoryOperator`)
read on another realization of the same graph space. So the two have the same index
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_one`) and are Fredholm together
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_one_iff`).
-/

public section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the graph space of the identity of `Lᵖ(Ω, F)`, the formula defining
`familyDomainTrajectoryOperator` is the trajectory operator `u ↦ u' + A u`. -/
private theorem apply_compLpL_comp_weakFDerivL_add_operatorMultiplication_comp_prevL
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
        (weakFDerivL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) +
      (Lp.operatorMultiplication p AL).comp
        (prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) =
      trajectoryOperator (p := p) AL := by
  refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
  filter_upwards [trajectoryOperator_apply_ae AL u,
    Lp.coeFn_add ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u))
      (Lp.operatorMultiplication p AL
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)),
    (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLpL (p := p) (μ := mu.restrict Omega)
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u),
    Lp.operatorMultiplication_ae AL
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)] with s h₁ h₂ h₃ h₄
  simp only [add_apply, ContinuousLinearMap.comp_apply, weakFDerivL_apply,
    prevL_apply, h₂, Pi.add_apply, h₃, h₄, h₁, ContinuousLinearMap.apply_apply]

/-- The graph space of the embedding `1 ∘ ·` of `Lᵖ(Ω, F)` is the graph space of the identity of
`Lᵖ(Ω, F)`, and along this identification the operator `u ↦ (1 ∘ u)' + A u` is the trajectory
operator `u ↦ u' + A u`. The two graph spaces are equal as sets but have different types, since
`(1 : F →L[ℝ] F).compLpL p μ` is only propositionally the identity. -/
private theorem exists_familyDomainTrajectoryOperator_one_eq_comp
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ∃ e : WeakDerivStep mu Omega p ((1 : F →L[ℝ] F).compLpL p (mu.restrict Omega)) ≃L[ℝ]
        WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))),
      familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL =
        (trajectoryOperator AL).comp (e : _ →L[ℝ] _) := by
  rw [familyDomainTrajectoryOperator_def]
  -- Replace the embedding `(1 : F →L[ℝ] F).compLpL p μ` by the identity of `Lᵖ(Ω, F)`, in the
  -- types of the graph spaces as well.
  generalize hb : (1 : F →L[ℝ] F).compLpL p (mu.restrict Omega) = base
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_compLpL] at hb
  subst hb
  exact ⟨.refl ℝ _, by
    rw [apply_compLpL_comp_weakFDerivL_add_operatorMultiplication_comp_prevL,
      ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id]⟩

/-- **The common-domain operator with the identity embedding is the trajectory operator.** Over
the common domain `F` embedded in itself by the identity, `u ↦ (1 ∘ u)' + A u` has the index of the
trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)`. -/
theorem index_familyDomainTrajectoryOperator_one (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    (familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL).index =
      (trajectoryOperator (p := p) AL).index := by
  obtain ⟨e, he⟩ := exists_familyDomainTrajectoryOperator_one_eq_comp (p := p) AL
  rw [he, ContinuousLinearMap.index_comp_equiv]

/-- Over the common domain `F` embedded in itself by the identity, `u ↦ (1 ∘ u)' + A u` is
Fredholm exactly when the trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)` is. -/
theorem isFredholm_familyDomainTrajectoryOperator_one_iff
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    (familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL).IsFredholm ↔
      (trajectoryOperator (p := p) AL).IsFredholm := by
  obtain ⟨e, he⟩ := exists_familyDomainTrajectoryOperator_one_eq_comp (p := p) AL
  rw [he, ContinuousLinearMap.isFredholm_comp_equiv]

end TauCeti.WeakDerivStep
