/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# The increment of a function along a segment

This file bounds the increment of a function between `x` and `x + h` by the integral of its
directional derivative along the segment joining them. It is the multi-dimensional form of
Mathlib's one-dimensional `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`, obtained by
composing with the affine parametrization `t ↦ x + t • h` of the segment.

The hypothesis of the first estimate is local to the segment: differentiability at each of its
points. The normalized real-valued estimate
instead assumes continuity of the function along the unit-speed parameterized segment,
differentiability at interior parameters, and interval integrability of the norm of the full
Fréchet derivative rather than continuity merely of its fixed directional evaluation; for a
zero-length segment these hypotheses hold trivially.

## Main declarations

* `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`: the segment increment estimate.
* `TauCeti.norm_sub_le_integral_norm_fderiv_along_segment`: the corresponding normalized
  real-integral estimate.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, where this is the starting point of the
difference-quotient characterization of Sobolev functions.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- **The segment increment estimate**: the norm of `u (x + h) - u x` is at most the integral
along the segment from `x` to `x + h` of the norm of the directional derivative
`Du(x + t • h) h`. -/
theorem enorm_sub_le_lintegral_enorm_fderiv_apply (x h : E)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (x + t • h)) :
    ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
  set G : ℝ → F := fun s => u (x + s • h)
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ G t :=
    fun t ht => (hd t ht).comp t (by fun_prop)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, deriv G t = fderiv ℝ u (x + t • h) h := fun t ht =>
    (hd t ht).deriv_comp_add_smul
  by_cases hJ : ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ = ∞
  · rw [hJ]
    exact le_top
  -- Measurability of the derivative is checked in the completion of `F`.
  set Gc : ℝ → UniformSpace.Completion F := fun s => (G s : UniformSpace.Completion F)
  have hGc : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv Gc t‖ = ‖fderiv ℝ u (x + t • h) h‖ := by
    intro t ht
    have hcoe : HasFDerivAt (𝕜 := ℝ) ((↑) : F → UniformSpace.Completion F)
        UniformSpace.Completion.toComplL (G t) := by
      rw [← UniformSpace.Completion.coe_toComplL (S := ℝ)]
      exact (UniformSpace.Completion.toComplL (α := F) (S := ℝ)).hasFDerivAt
    rw [show Gc = ((↑) : F → UniformSpace.Completion F) ∘ G from rfl,
      (hcoe.comp_hasDerivAt t (hline t ht).hasDerivAt).deriv,
      UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.norm_coe, hderiv t ht]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖deriv Gc t‖) volume :=
    (aestronglyMeasurable_deriv Gc volume).norm
  have hint : IntegrableOn (fun t : ℝ => ‖fderiv ℝ u (x + t • h) h‖) (Ioc (0 : ℝ) 1) := by
    have hnorm : IntegrableOn (fun t : ℝ => ‖deriv Gc t‖) (Ioc (0 : ℝ) 1) := by
      refine ⟨hmeas.restrict, ?_⟩
      simp only [HasFiniteIntegral, enorm_norm]
      refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hJ)
      refine (lintegral_mono_set Ioc_subset_Icc_self).trans_eq' ?_
      exact setLIntegral_congr_fun measurableSet_Ioc fun t ht => by
        rw [← ofReal_norm, ← ofReal_norm (deriv Gc t), hGc t (Ioc_subset_Icc_self ht)]
    exact hnorm.congr_fun (fun t ht => hGc t (Ioc_subset_Icc_self ht)) measurableSet_Ioc
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := G) (a := 0) (b := 1)
    (B := fun t => ‖fderiv ℝ u (x + t • h) h‖) zero_le_one
    (fun t ht => (hline t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hline t (Ioo_subset_Icc_self ht)).differentiableWithinAt)
    (.of_forall fun t ht => by rw [hderiv t (Ioo_subset_Icc_self ht)])
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint)
  rw [intervalIntegral.integral_of_le zero_le_one] at hmain
  calc ‖u (x + h) - u x‖ₑ = ENNReal.ofReal ‖G 1 - G 0‖ := by simp [G]
    _ ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun t => norm_nonneg _)]
        simp only [ofReal_norm]
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ :=
        lintegral_mono_set Ioc_subset_Icc_self

/-- The oscillation of a function along a segment is bounded by the integrated norm of its
Fréchet derivative along that segment, traversed at unit speed: the function is continuous along
the closed parameter interval, differentiable at its interior parameters, and the operator-norm
bound is interval-integrable. For a zero-length segment these hypotheses hold trivially.

This is adapted from Scott Armstrong and Julia Kempe's Apache-2.0
`scottnarmstrong/DeGiorgi/DeGiorgi/Poincare.lean`, commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`, lines 382--431. -/
theorem norm_sub_le_integral_norm_fderiv_along_segment (x y : E)
    (hd : ∀ t ∈ Ioo (0 : ℝ) ‖x - y‖,
      DifferentiableAt ℝ u (x + t • (‖x - y‖⁻¹ • (y - x))))
    (hc : ContinuousOn (fun t : ℝ => u (x + t • (‖x - y‖⁻¹ • (y - x)))) (Icc 0 ‖x - y‖))
    (hBi : IntervalIntegrable (fun t : ℝ => ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖)
      volume 0 ‖x - y‖) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set L : ℝ := ‖x - y‖
  set ω : E := L⁻¹ • (y - x) with hω_def
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_def, norm_smul, norm_inv, norm_norm, norm_sub_rev y x, inv_mul_cancel₀ hL.ne']
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo 0 L →
      ‖deriv (fun s : ℝ => u (x + s • ω)) t‖ ≤ ‖fderiv ℝ u (x + t • ω)‖ :=
    .of_forall fun t ht => by
      rw [(hd t ht).deriv_comp_add_smul]
      simpa only [hω_norm, mul_one] using (fderiv ℝ u (x + t • ω)).le_opNorm ω
  have hkey := norm_sub_le_integral_of_norm_deriv_le_of_le hL.le hc
    (fun t ht => ((hd t ht).comp t (by fun_prop)).differentiableWithinAt) hfB hBi
  rw [norm_sub_rev]
  simpa [hω_def, smul_smul, hL.ne'] using hkey

end TauCeti
