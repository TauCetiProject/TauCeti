/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The locally integrable kernel for the Poincaré--Wirtinger inequality

Let `E` be a nontrivial finite-dimensional real normed space of dimension `d`.  This file
computes the integral of the weakly singular kernel

`x ↦ ‖x‖ ^ (1 - d)`

on a ball centred at the origin.  The singularity is locally integrable because its radial
Jacobian is `r ^ (d - 1)`, so the powers cancel.  For an additive Haar measure `μ` and `R > 0`,

`\int x in ball 0 R, ‖x‖ ^ (1 - d) ∂μ = d * μ.real (ball 0 1) * R`.

The translated estimate bounds the same kernel on a ball centred elsewhere, with its pole at a
point of that ball.  This is the kernel bound used when the straight-segment estimate is averaged
over a ball in the proof of the Poincaré--Wirtinger inequality.

## Main declarations

* `TauCeti.integrableOn_norm_rpow_one_sub_finrank`: local integrability on a centred ball.
* `TauCeti.integral_norm_rpow_one_sub_finrank_ball`: the exact radial integral.
* `TauCeti.integrableOn_norm_sub_rpow_one_sub_finrank_ball`: integrability after translation.
* `TauCeti.integral_norm_sub_rpow_one_sub_finrank_ball`: the exact integral with any centre.
* `TauCeti.integral_norm_sub_rpow_one_sub_finrank_le`: the translated-ball bound.

## References

The statements and radial proof are adapted from Scott Armstrong and Julia Kempe's Apache-2.0
`scottnarmstrong/DeGiorgi/DeGiorgi/Poincare.lean`, commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`, lines 750--870.  The formulation here uses an
arbitrary additive Haar measure and Mathlib's `MeasureTheory.integral_fun_norm_addHaar`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {mu : Measure E} [mu.IsAddHaarMeasure]

/-- The kernel `x ↦ ‖x‖ ^ (1 - dim E)` is integrable on every ball centred at the origin. -/
theorem integrableOn_norm_rpow_one_sub_finrank {R : ℝ} :
    IntegrableOn (fun x : E => ‖x‖ ^ (1 - (Module.finrank ℝ E : ℝ))) (ball 0 R) mu := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  apply (integrableOn_fun_norm_addHaar (F := ℝ)
    (f := fun r => r ^ (1 - (Module.finrank ℝ E : ℝ))) (r := R) mu).2
  refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioo_lt_top.ne)).congr_fun ?_
    measurableSet_Ioo
  intro r hr
  simp only [smul_eq_mul]
  rw [← Real.rpow_natCast r (Module.finrank ℝ E - 1), Nat.cast_sub hd,
    ← Real.rpow_add hr.1]
  norm_num

/-- The exact integral of the kernel `x ↦ ‖x‖ ^ (1 - dim E)` on a ball centred at the origin.
The coefficient is stated using the chosen additive Haar measure, so the result applies to both
Lebesgue volume and its scalar multiples. -/
theorem integral_norm_rpow_one_sub_finrank_ball {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in ball (0 : E) R, ‖x‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu =
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * R := by
  let d := Module.finrank ℝ E
  let f : ℝ → ℝ := fun r => if 0 < r ∧ r < R then r ^ (1 - (d : ℝ)) else 0
  have hconv : ∫ x in ball (0 : E) R, ‖x‖ ^ (1 - (d : ℝ)) ∂mu =
      ∫ x : E, f ‖x‖ ∂mu := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae ?_
    have hzero : mu ({0} : Set E) = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.mpr hzero] with x hx
    simp only [f, indicator, mem_ball, dist_zero_right]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [and_iff_right hxpos]
  have hradial : ∫ x : E, f ‖x‖ ∂mu =
      d • mu.real (ball (0 : E) 1) •
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r :=
    integral_fun_norm_addHaar mu f
  have hradialIntegral : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r = R := by
    have hd : 1 ≤ d := Module.finrank_pos
    have heq : Set.EqOn (fun r : ℝ => r ^ (d - 1) • f r)
        (fun r => (Ioo (0 : ℝ) R).indicator (fun _ => (1 : ℝ)) r) (Ioi 0) := by
      intro r hr
      simp only [mem_Ioi] at hr
      simp only [f, smul_eq_mul, indicator, mem_Ioo]
      split_ifs with h
      · rw [← Real.rpow_natCast r (d - 1), Nat.cast_sub hd, ← Real.rpow_add hr]
        norm_num
      · simp
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    rw [setIntegral_indicator measurableSet_Ioo]
    have hinter : Ioi (0 : ℝ) ∩ Ioo 0 R = Ioo 0 R :=
      inter_eq_right.mpr Ioo_subset_Ioi_self
    rw [hinter]
    simp [hR]
  rw [hconv, hradial, hradialIntegral]
  simp only [nsmul_eq_mul, smul_eq_mul]
  simp [d, mul_assoc]

/-- The kernel with pole `x` is integrable on every ball centred at `x`. -/
theorem integrableOn_norm_sub_rpow_one_sub_finrank_ball (x : E) {R : ℝ} :
    IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ))) (ball x R) mu := by
  have hpres := measurePreserving_add_right mu x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : (fun z : E => z + x) ⁻¹' ball x R = ball (0 : E) R := by
    ext z
    simp [mem_ball]
  rw [← hpres.integrableOn_comp_preimage hemb, hpre]
  exact (integrableOn_norm_rpow_one_sub_finrank (mu := mu) (R := R)).congr
    (ae_of_all _ fun z => by simp [norm_neg])

/-- The integral of the kernel with pole `x` over a ball centred at `x` does not depend on the
centre and has the same exact value as the radial integral at the origin. -/
theorem integral_norm_sub_rpow_one_sub_finrank_ball {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ∫ y in ball x R, ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu =
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * R := by
  have hpres := measurePreserving_add_right mu x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : (fun z : E => z + x) ⁻¹' ball x R = ball (0 : E) R := by
    ext z
    simp [mem_ball]
  rw [← hpres.setIntegral_preimage_emb hemb, hpre]
  have hfun : (fun z : E => ‖x - (z + x)‖ ^ (1 - (Module.finrank ℝ E : ℝ))) =
      fun z => ‖z‖ ^ (1 - (Module.finrank ℝ E : ℝ)) := by
    funext z
    simp [norm_neg]
  rw [hfun, integral_norm_rpow_one_sub_finrank_ball hR]

/-- If `x` lies in `ball 0 R`, then the integral there of the kernel with pole `x` is bounded by
the exact integral on `ball 0 (2R)`. -/
theorem integral_norm_sub_rpow_one_sub_finrank_le {R : ℝ} (x : E)
    (hx : x ∈ ball (0 : E) R) :
    ∫ y in ball (0 : E) R, ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu ≤
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * (2 * R) := by
  have hxR : dist x 0 < R := mem_ball.mp hx
  have hR : 0 < R := dist_nonneg.trans_lt hxR
  have hsub : ball (0 : E) R ⊆ ball x (2 * R) := by
    intro y hy
    rw [mem_ball] at hy ⊢
    calc
      dist y x ≤ dist y 0 + dist 0 x := dist_triangle y 0 x
      _ < R + R := by rw [dist_comm] at hxR; exact add_lt_add hy hxR
      _ = 2 * R := by ring
  have htwoR : 0 ≤ 2 * R := by positivity
  have hintegrable :
      IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)))
        (ball x (2 * R)) mu :=
    integrableOn_norm_sub_rpow_one_sub_finrank_ball x
  calc
    ∫ y in ball (0 : E) R, ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu ≤
        ∫ y in ball x (2 * R), ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu := by
      apply setIntegral_mono_set hintegrable
      · exact ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _
      · exact hsub.eventuallyLE
    _ = (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * (2 * R) :=
      integral_norm_sub_rpow_one_sub_finrank_ball htwoR x

end TauCeti
