/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Absolute continuity of piecewise `C¹` curves

A piecewise `C¹` curve on a compact parameter interval is Lipschitz there, and hence absolutely
continuous. The derivative is bounded by `IsPiecewiseC1On.isBounded_image_deriv`; the fundamental
theorem of calculus off the finite set of breakpoints then bounds every increment of the curve.

The existing contour regularity therefore specializes to absolutely continuous curves.
-/

public section

namespace TauCeti.Contour

open MeasureTheory Set
open scoped NNReal

variable {γ : ℝ → ℂ} {a b : ℝ}

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
