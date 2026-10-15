/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute continuity of complex curves

A piecewise `C¹` curve on a compact parameter interval is Lipschitz there, and hence absolutely
continuous. The derivative is bounded by `IsPiecewiseC1On.isBounded_image_deriv`; the fundamental
theorem of calculus off the finite set of breakpoints then bounds every increment of the curve.

The existing contour regularity therefore specializes to absolutely continuous curves.
For a continuous curve differentiable outside a countable set, integrability of an off-curve
logarithmic derivative also suffices for absolute continuity.
-/

public section

namespace TauCeti.Contour

open MeasureTheory Set
open scoped NNReal

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- A continuous complex curve differentiable off a countable set is absolutely continuous
if its logarithmic derivative about an avoided point is interval integrable. -/
theorem _root_.ContinuousOn.absolutelyContinuousOnInterval_of_intervalIntegrable_inv_sub_mul_deriv
    {w : ℂ} {P : Set ℝ} (hγ : ContinuousOn γ (uIcc a b)) (hP : P.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (havoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (hi : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    AbsolutelyContinuousOnInterval γ a b := by
  have hderiv : IntervalIntegrable (deriv γ) volume a b := by
    refine (hi.continuousOn_mul (hγ.sub (continuousOn_const (c := w)))).congr (fun t ht ↦ ?_)
    dsimp
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (havoid t (uIoc_subset_uIcc ht))), one_mul]
  exact hγ.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (hd t ht).hasDerivAt) hderiv

/-- A piecewise `C¹` curve is Lipschitz on its compact parameter interval, including across its
breakpoints. -/
theorem IsPiecewiseC1On.exists_lipschitzOnWith (hγ : IsPiecewiseC1On γ a b) :
    ∃ K : ℝ≥0, LipschitzOnWith K γ (uIcc a b) := by
  obtain ⟨C, hCpos, hC⟩ := hγ.isBounded_image_deriv.exists_pos_norm_le
  refine ⟨⟨C, hCpos.le⟩, lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro x hx y hy
  have hsub : uIcc y x ⊆ uIcc a b := uIcc_subset_uIcc hy hx
  have hγ' := hγ.mono hsub
  obtain ⟨P, hP, hdiff⟩ := hγ'.exists_countable_differentiableAt
  have hFTC := integral_eq_of_hasDerivAt_off_countable γ (deriv γ) hP hγ'.continuousOn
    (fun t ht ↦ (hdiff t ht).hasDerivAt) hγ'.intervalIntegrable_deriv
  rw [dist_eq_norm, ← hFTC, Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
    hC _ ⟨t, hsub (uIoc_subset_uIcc ht), rfl⟩

/-- Every piecewise `C¹` contour is absolutely continuous on its parameter interval. -/
theorem IsPiecewiseC1On.absolutelyContinuousOnInterval (hγ : IsPiecewiseC1On γ a b) :
    AbsolutelyContinuousOnInterval γ a b := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith
  exact hK.absolutelyContinuousOnInterval

end TauCeti.Contour
