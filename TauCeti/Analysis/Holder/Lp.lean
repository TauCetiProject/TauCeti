/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Holder.Normed

import TauCeti.MeasureTheory.Function.Lp.BallAverage

/-!
# Global Hölder functions in `Lᵖ`

This file proves that a globally Hölder function with finite `Lᵖ` norm is bounded and bundles it
as an element of the global Hölder Banach space. The pointwise estimate compares the function with
its average on a unit ball: Hölder continuity controls the difference from the average, while
Hölder's inequality controls the average itself.

## Main declarations

* `HolderWith.enorm_le_add_eLpNorm`: a global Hölder function in `Lᵖ` has a pointwise bound.
* `HolderWith.toHolderSpace`: bundle a global Hölder `Lᵖ` function in `TauCeti.HolderSpace`.
* `HolderWith.norm_toHolderSpace_le`: the resulting Hölder-space norm estimate.
-/

public section

noncomputable section

namespace HolderWith

open MeasureTheory Metric Set
open scoped ENNReal NNReal BoundedContinuousFunction
open TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F} {C α : ℝ≥0} {p : ℝ≥0∞}

/-- A globally Hölder function with finite `Lᵖ` norm is pointwise bounded. At unit scale the
bound is the sum of its Hölder constant and the `Lᵖ` norm multiplied by the inverse `p`-th power
of the volume of the unit ball. -/
theorem enorm_le_add_eLpNorm (hg : HolderWith C α g) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) (x : E) :
    ‖g x‖ₑ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu := by
  have hdev : ‖ballAverage mu 1 g x - g x‖ₑ ≤ C := by
    rw [ballAverage_sub_self hp hgLp one_pos]
    rw [setAverage_eq, enorm_smul]
    refine (mul_le_mul le_rfl (enorm_integral_le_lintegral_enorm _) bot_le bot_le).trans ?_
    calc
      _ ≤ ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ *
          ∫⁻ e in ball (0 : E) 1, (C : ℝ≥0∞) ∂mu := by
        refine mul_le_mul le_rfl (lintegral_mono_ae ?_) bot_le bot_le
        filter_upwards [ae_restrict_mem measurableSet_ball] with e he
        rw [← edist_eq_enorm_sub]
        refine (hg (x + e) x).trans ?_
        have he' : edist (x + e) x ≤ 1 := by
          simpa only [edist_dist, ENNReal.ofReal_le_one, dist_eq_norm, add_sub_cancel_left,
            norm_neg] using (mem_ball_zero_iff.1 he).le
        exact (mul_le_mul le_rfl (ENNReal.rpow_le_one he' (by positivity)) bot_le bot_le).trans
          (mul_one _).le
      _ = ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ * mu (ball (0 : E) 1) * C := by
        rw [setLIntegral_const]
        ac_rfl
      _ = C := by
        have hinv : ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ =
            (mu (ball (0 : E) 1))⁻¹ := by
          rw [Real.enorm_eq_ofReal (by positivity), measureReal_def, ← ENNReal.toReal_inv,
            ENNReal.ofReal_toReal
              (ENNReal.inv_ne_top.2 (measure_ball_pos mu 0 one_pos).ne')]
        rw [hinv]
        simp only [ENNReal.inv_mul_cancel (measure_ball_pos mu 0 one_pos).ne'
          measure_ball_lt_top.ne, one_mul]
  calc
    ‖g x‖ₑ = edist (g x) 0 := by rw [edist_zero_right]
    _ ≤ edist (g x) (ballAverage mu 1 g x) + ‖ballAverage mu 1 g x‖ₑ := by
      simpa only [edist_zero_right] using edist_triangle (g x) (ballAverage mu 1 g x) 0
    _ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu :=
      add_le_add (by rw [edist_comm]; simpa only [edist_eq_enorm_sub] using hdev)
        (enorm_ballAverage_le hp hp' hgLp.aestronglyMeasurable one_pos x)

/-- A global Hölder function in `Lᵖ`, bundled as an element of the Hölder Banach space. -/
def toHolderSpace (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) : TauCeti.HolderSpace α E F := by
  let R : ℝ≥0∞ := C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu
  have hR : R ≠ ∞ := by
    rw [← lt_top_iff_ne_top]
    simp only [R]
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
          (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)) hgLp.eLpNorm_lt_top⟩
  have hpoint (x : E) : ‖g x‖ ≤ R.toReal := by
    simpa only [toReal_enorm] using (ENNReal.toReal_le_toReal enorm_ne_top hR).2
      (hg.enorm_le_add_eLpNorm hp hp' hgLp x)
  let G : E →ᵇ F := BoundedContinuousFunction.mkOfBound ⟨g, hg.continuous hα⟩
    (2 * R.toReal) (BoundedContinuousFunction.dist_le_two_norm' hpoint)
  have hG : (G : E → F) = g := by
    funext x
    rfl
  exact TauCeti.HolderSpace.ofBoundedContinuousFunction G (hG.symm ▸ hg.memHolder)

/-- The Hölder-space bundling does not change the underlying function. -/
@[simp]
theorem toHolderSpace_apply (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hgLp : MemLp g p mu) (x : E) :
    hg.toHolderSpace hα hp hp' hgLp x = g x := by
  rw [← TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
  rw [toHolderSpace, TauCeti.HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  rfl

/-- The Hölder-space norm is controlled by the pointwise bound and the given Hölder
constant. -/
theorem norm_toHolderSpace_le (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hgLp : MemLp g p mu) :
    ‖hg.toHolderSpace hα hp hp' hgLp‖ ≤
      (C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu).toReal + C := by
  rw [TauCeti.HolderSpace.norm_def]
  apply add_le_add
  · rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply, toHolderSpace_apply]
    have hx := (ENNReal.toReal_le_toReal enorm_ne_top (by
      rw [← lt_top_iff_ne_top, ENNReal.add_lt_top]
      exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
          (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
            (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne))
          hgLp.eLpNorm_lt_top⟩)).2 (hg.enorm_le_add_eLpNorm hp hp' hgLp x)
    simpa only [toReal_enorm] using hx
  · have hb : HolderWith C α (fun x => hg.toHolderSpace hα hp hp' hgLp x) := by
      intro x y
      simpa only [toHolderSpace_apply] using hg x y
    have heq : ((hg.toHolderSpace hα hp hp' hgLp).toBoundedContinuousFunction : E → F) =
        fun x => hg.toHolderSpace hα hp hp' hgLp x := by
      funext x
      rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
    rw [heq]
    exact_mod_cast hb.nnholderNorm_le

end HolderWith
