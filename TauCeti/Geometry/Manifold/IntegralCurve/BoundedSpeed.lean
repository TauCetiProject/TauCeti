/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Compact confinement from bounded exhaustion speed

If the derivative of a real function along a vector field has absolute value at most `C`,
then along an integral curve its change is bounded by `C` times elapsed time. If that function
is proper, every bounded time window of the curve lies in a compact band of function values.
The time domain need only be convex, not closed: in particular this applies to a curve before
a finite endpoint of its domain, as required in escape arguments.

These results also hold on manifolds with corners. They neither assume nor supply local
existence of integral curves at boundary points.
-/

public section

open Set Metric
open scoped Manifold

namespace IsMIntegralCurveOn

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ} {f : M → ℝ}

/-- A bound on the derivative of a function along a field bounds its change along any integral
curve on a convex time domain. Only differentiability along that curve is required. -/
theorem abs_sub_le_mul_of_abs_mvfderiv_le (hγ : IsMIntegralCurveOn γ X s)
    (hs : Convex ℝ s) (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    {C : ℝ} (hC : ∀ t ∈ s, |mvfderiv I f (γ t) (X (γ t))| ≤ C)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    |f (γ t) - f (γ t₀)| ≤ C * |t - t₀| := by
  simpa only [Real.norm_eq_abs, Function.comp_apply] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu ↦ TauCeti.Manifold.hasDerivWithinAt_comp_curve (hf u hu) (hγ u hu))
      (fun u hu ↦ by simpa only [Real.norm_eq_abs] using hC u hu) hs ht₀ ht

/-- If a proper real function has bounded speed along an integral curve, every bounded time
window lies in a compact set. The window may meet a missing endpoint of the time domain. -/
theorem exists_isCompact_mapsTo_inter_closedBall_of_isProperMap
    (hγ : IsMIntegralCurveOn γ X s) (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t)) (hp : IsProperMap f)
    {C : ℝ} (hC : ∀ t ∈ s, |mvfderiv I f (γ t) (X (γ t))| ≤ C)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (T : ℝ) :
    ∃ K : Set M, IsCompact K ∧ MapsTo γ (s ∩ closedBall t₀ T) K := by
  refine ⟨f ⁻¹' Icc (f (γ t₀) - C * T) (f (γ t₀) + C * T),
    hp.isCompact_preimage isCompact_Icc, ?_⟩
  rintro t ⟨ht, htT⟩
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC t₀ ht₀)
  have htT' : |t - t₀| ≤ T := by simpa only [mem_closedBall, Real.dist_eq] using htT
  have h := (hγ.abs_sub_le_mul_of_abs_mvfderiv_le hs hf hC ht₀ ht).trans
    (mul_le_mul_of_nonneg_left htT' hC₀)
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

end IsMIntegralCurveOn
