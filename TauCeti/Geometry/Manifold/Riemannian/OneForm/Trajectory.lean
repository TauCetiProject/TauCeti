/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.OneForm.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Negative metric-dual trajectories of one-forms

Trajectories are native manifold integral curves of `-α.metricDual`. Along a local primitive
`f` they satisfy `d(f ∘ γ)/dt = -‖α.metricDual ∘ γ‖²`. Consequently potentials are antitone,
strictly so on segments avoiding zeros, and their drop is the integral of the squared speed.
All these statements apply on the domain of a local primitive; no global exactness is assumed.

On a compact boundaryless manifold a `C¹` one-form with a `C¹` metric has global negative-dual
trajectories through every point, by the maximal integral-curve completeness theorem.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002), §1.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {α : RoughForm I M ℝ 1} {f : M → ℝ} {U : Set M} {γ : ℝ → M}
  {s : Set ℝ} {t : ℝ}

/-- The potential-drop equation within an arbitrary time set, including its endpoints. -/
theorem IsPrimitiveOn.hasDerivWithinAt_comp_neg_metricDual (hf : IsPrimitiveOn α f U)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s) (ht : t ∈ s) (hU : γ t ∈ U) :
    HasDerivWithinAt (f ∘ γ) (-‖α.metricDual (γ t)‖ ^ 2) s t := by
  simpa only [Pi.neg_apply, hf.mvfderiv_neg_metricDual hU] using
    Manifold.hasDerivWithinAt_comp_curve
      ((hf.mdifferentiableOn _ hU).mdifferentiableAt (hf.isOpen.mem_nhds hU)) (hγ t ht)

/-- A primitive has derivative minus the squared speed along a negative-dual trajectory. -/
theorem IsPrimitiveOn.hasDerivAt_comp_neg_metricDual (hf : IsPrimitiveOn α f U)
    (hγ : IsMIntegralCurveAt γ (-α.metricDual) t) (ht : γ t ∈ U) :
    HasDerivAt (f ∘ γ) (-‖α.metricDual (γ t)‖ ^ 2) t := by
  simpa only [Pi.neg_apply, hf.mvfderiv_neg_metricDual ht] using
    Manifold.hasDerivAt_comp_curve
      ((hf.mdifferentiableOn _ ht).mdifferentiableAt (hf.isOpen.mem_nhds ht)) hγ.hasMFDerivAt

/-- A local primitive is nonincreasing along a negative-dual trajectory in its domain. -/
theorem IsPrimitiveOn.antitoneOn_comp_neg_metricDual (hf : IsPrimitiveOn α f U)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s) (hconv : Convex ℝ s)
    (hU : MapsTo γ s U) : AntitoneOn (f ∘ γ) s := by
  have hd := fun (t : ℝ) (ht : t ∈ s) ↦
    hf.hasDerivWithinAt_comp_neg_metricDual hγ ht (hU ht)
  exact antitoneOn_of_hasDerivWithinAt_nonpos hconv
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).mono interior_subset)
    (fun _ _ ↦ neg_nonpos.mpr (sq_nonneg _))

/-- A local primitive strictly decreases if the trajectory avoids zeros at interior times. -/
theorem IsPrimitiveOn.strictAntiOn_comp_neg_metricDual (hf : IsPrimitiveOn α f U)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s) (hconv : Convex ℝ s)
    (hU : MapsTo γ s U) (hne : ∀ t ∈ interior s, α (γ t) ≠ 0) : StrictAntiOn (f ∘ γ) s := by
  have hd := fun (t : ℝ) (ht : t ∈ s) ↦
    hf.hasDerivWithinAt_comp_neg_metricDual hγ ht (hU ht)
  apply strictAntiOn_of_hasDerivWithinAt_neg hconv
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact neg_neg_of_pos (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (mt RoughForm.metricDual_eq_zero_iff.mp (hne t ht))))

/-- On a bounded time segment in the primitive domain, the integral of the squared speed
is the potential drop. The time integral is oriented, so no ordering of the endpoints is needed. -/
theorem IsPrimitiveOn.integral_norm_metricDual_sq_eq_sub
    [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]
    (hf : IsPrimitiveOn α f U) (hα : IsSmoothForm I 0 α)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s)
    (hU : MapsTo γ s U) {a b : ℝ} (hab : uIcc a b ⊆ s) :
    ∫ t in a..b, ‖α.metricDual (γ t)‖ ^ 2 = f (γ a) - f (γ b) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
  have : IsManifold I ((0 : ℕ∞ω) + 1) M := by
    simpa only [zero_add] using (inferInstance : IsManifold I 1 M)
  have hdual := hα.contMDiff_metricDual.continuous
  have hc : ContinuousOn (fun t ↦ ‖α.metricDual (γ t)‖ ^ 2) (uIcc a b) := by
    exact (((continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn
      (hdual.comp_continuousOn hγ.continuousOn)).pow 2).mono hab
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :=
    ((hf.hasDerivWithinAt_comp_neg_metricDual hγ (hab ht) (hU (hab ht))).mono hab).neg
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (fun t ht ↦ (hd t ht).continuousWithinAt) (fun t ht ↦ ?_) hc.intervalIntegrable
  · simpa only [Function.comp_apply, Pi.neg_apply, neg_sub_neg] using heq
  simpa only [neg_neg] using ((hd t (mem_Icc_of_Ioo ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt

/-- A `C¹` form on a compact boundaryless manifold has a global negative-dual trajectory
through every point. This uses maximal-flow completeness, with no global potential. -/
theorem IsSmoothForm.exists_isMIntegralCurve_neg_metricDual [IsManifold I 2 M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [T2Space M] [BoundarylessManifold I M] [CompactSpace M]
    (hα : IsSmoothForm I 1 α) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (-α.metricDual) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hv := hα.contMDiff_neg_metricDual
  refine ⟨maximalIntegralCurve (-α.metricDual) x, ?_, isMIntegralCurve_maximalIntegralCurve hv⟩
  exact maximalIntegralCurve_zero (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt)

end TauCeti
