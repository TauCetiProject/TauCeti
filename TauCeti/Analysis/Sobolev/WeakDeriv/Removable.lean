/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Integral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Weak derivatives across countable exceptional sets

A continuous map on an open subset of a finite-dimensional real space has its classical
derivative as a weak derivative if the classical derivative exists outside a countable set
and is locally integrable across that set. No differentiability at the exceptional points
is assumed. In particular, a continuous filling of a puncture does not acquire a point-mass
term in its distributional first derivative.

Integration by parts is obtained by applying
`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable` to the product of the map with a
test function. This is the weak-derivative step in the removal of isolated singularities,
separate from both integrability estimates and subsequent elliptic regularity.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- A continuous map with a locally integrable classical derivative outside a countable
exceptional set has that derivative as a weak derivative on the whole open domain.
The derivative field is unconstrained at the exceptional points. -/
theorem hasWeakFDerivOn_of_hasFDerivAt_off_countable
    {u : E → F} {U : E → E →L[ℝ] F} {s : Set E} (hs : s.Countable)
    (hu : ContinuousOn u Ω) (hU : LocallyIntegrableOn U Ω μ)
    (hd : ∀ x ∈ (Ω : Set E) \ s, HasFDerivAt u (U x) x) :
    HasWeakFDerivOn μ Ω u U := by
  have hui : LocallyIntegrableOn u Ω μ := hu.locallyIntegrableOn Ω.isOpen.measurableSet
  refine hasWeakFDerivOn_iff.2 fun v ↦ hasWeakLineDerivOn_iff_testFunction.2
    ⟨inferInstance, hui, ?_, fun φ ↦ ?_⟩
  · simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hU
  let D : E → E →L[ℝ] F := fun x ↦
    (φ : E → ℝ) x • U x + (fderiv ℝ (φ : E → ℝ) x).smulRight (u x)
  have hc : Continuous (fun x ↦ (φ : E → ℝ) x • u x) :=
    (φ.contDiff.continuous.continuousOn.smul hu).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left _ _).trans φ.tsupport_subset)
  have hdφ : ∀ x ∉ s, HasFDerivAt (fun x ↦ (φ : E → ℝ) x • u x) (D x) x := by
    intro x hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · exact (φ.contDiff.differentiable (by simp) x).hasFDerivAt.smul (hd x ⟨hxΩ, hx⟩)
    · have hxφ : x ∉ tsupport (φ : E → ℝ) := fun h ↦ hxΩ (φ.tsupport_subset h)
      have hzero : (fun x ↦ (φ : E → ℝ) x • u x) =ᶠ[nhds x] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hxφ).mono fun y hy ↦ by simp [hy]
      have hDx : D x = 0 := by
        simp [D, image_eq_zero_of_notMem_tsupport hxφ, fderiv_of_notMem_tsupport ℝ hxφ]
      rw [hDx]
      exact (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hzero
  have hφd : ∀ x, fderiv ℝ (φ : E → ℝ) x v = lineDeriv ℝ (φ : E → ℝ) x v :=
    fun x ↦ ((φ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv.symm
  have hD : ∀ x, D x v = (φ : E → ℝ) x • U x v +
      lineDeriv ℝ (φ : E → ℝ) x v • u x := by
    intro x
    simp [D, hφd]
  have hi₁ : Integrable (fun x ↦ (φ : E → ℝ) x • U x v) μ :=
    integrable_smul_of_locallyIntegrableOn
      (by simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
        (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hU) φ
  have hi₂ := integrable_lineDeriv_smul_of_locallyIntegrableOn hui φ v
  have hzero := integral_apply_eq_zero_of_hasFDerivAt_off_countable hs hc
    φ.hasCompactSupport.smul_right hdφ v (by simpa only [hD] using hi₁.fun_add hi₂)
  rw [integral_congr_ae (Filter.Eventually.of_forall hD), integral_add hi₁ hi₂] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

end TauCeti
