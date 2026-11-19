/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Holder.Normed

import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.Lp.BallAverage
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.MetricSpace.Holder

/-!
# Global Hölder functions in `Lᵖ`

This file proves that a globally Hölder function with finite `Lᵖ` norm is bounded and bundles it
as an element of the global Hölder normed space (a Banach space when the target is complete). The
pointwise estimate compares the function with its average on a ball: Hölder continuity controls the
difference from the average, while Hölder's inequality controls the average itself.

It also bounds the `L²` oscillation of a function that is Hölder on a set contained in a ball in a
finite-dimensional space, as used in Campanato's approach to Schauder estimates.

## Main declarations

* `HolderWith.enorm_le_add_eLpNorm`: a global Hölder function in `Lᵖ` has a pointwise bound.
* `HolderWith.norm_le_add_eLpNorm_toReal`: the same bound for the real-valued norm.
* `HolderWith.toHolderSpace`: bundle a global Hölder `Lᵖ` function in `TauCeti.HolderSpace`.
* `HolderWith.norm_toHolderSpace_le`: the resulting Hölder-space norm estimate.
* `HolderOnWith.setIntegral_norm_sub_sq_le`: if `G` is `α`-Hölder with constant `K` on a set
  `s ⊆ ball x₀ r` and `y ∈ s`, then `∫_s ‖G - G y‖² ≤ 2^(2α) |B₁| K² r^(n + 2α)`.
-/

public section

noncomputable section

namespace HolderWith

open MeasureTheory Metric Set
open scoped ENNReal NNReal BoundedContinuousFunction
open TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F} {C α : ℝ≥0} {p : ℝ≥0∞}

/-- The case of `HolderWith.enorm_le_add_eLpNorm` with a complete target, where the function is
compared with its average on a ball. -/
private theorem enorm_le_add_eLpNorm_of_completeSpace [CompleteSpace F] (hg : HolderWith C α g)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hgLp : MemLp g p mu) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖g x‖ₑ ≤ C * ENNReal.ofReal r ^ (α : ℝ) +
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu := by
  have hdev : ‖ballAverage mu r g x - g x‖ₑ ≤ C * ENNReal.ofReal r ^ (α : ℝ) := by
    rw [ballAverage_sub_self hp hgLp hr]
    rw [setAverage_eq, eNorm_smul]
    refine (mul_le_mul le_rfl (eNorm_integral_le_lintegral_eNorm _) bot_le bot_le).trans ?_
    calc
      _ ≤ ‖(mu.real (ball (0 : E) r))⁻¹‖ₑ *
          ∫⁻ _ in ball (0 : E) r, (C * ENNReal.ofReal r ^ (α : ℝ)) ∂mu := by
        refine mul_le_mul le_rfl (lintegral_mono_ae ?_) bot_le bot_le
        filter_upwards [ae_restrict_mem measurableSet_ball] with e he
        rw [← eDist_eq_eNorm_sub]
        refine (hg (x + e) x).trans ?_
        have he' : edist (x + e) x ≤ ENNReal.ofReal r := by
          rw [edist_dist, dist_eq_norm, add_sub_cancel_left]
          exact ENNReal.ofReal_le_ofReal (mem_ball_zero_iff.1 he).le
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow he' (by positivity))
      _ = ‖(mu.real (ball (0 : E) r))⁻¹‖ₑ * mu (ball (0 : E) r) *
          (C * ENNReal.ofReal r ^ (α : ℝ)) := by
        rw [setLIntegral_const]
        ac_rfl
      _ = C * ENNReal.ofReal r ^ (α : ℝ) := by
        have hinv : ‖(mu.real (ball (0 : E) r))⁻¹‖ₑ =
            (mu (ball (0 : E) r))⁻¹ := by
          rw [Real.eNorm_eq_ofReal (by positivity), measureReal_def, ← ENNReal.toReal_inv,
            ENNReal.ofReal_toReal
              (ENNReal.inv_ne_top.2 (measure_ball_pos mu 0 hr).ne')]
        rw [hinv]
        simp only [ENNReal.inv_mul_cancel (measure_ball_pos mu 0 hr).ne'
          measure_ball_lt_top.ne, one_mul]
  calc
    ‖g x‖ₑ = edist (g x) 0 := by rw [edist_zero_right]
    _ ≤ edist (g x) (ballAverage mu r g x) + ‖ballAverage mu r g x‖ₑ := by
      simpa only [edist_zero_right] using edist_triangle (g x) (ballAverage mu r g x) 0
    _ ≤ C * ENNReal.ofReal r ^ (α : ℝ) + mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu :=
      add_le_add (by rw [edist_comm]; simpa only [eDist_eq_eNorm_sub] using hdev)
        (enorm_ballAverage_le hp hp' x)

/-- A globally Hölder function with finite `Lᵖ` norm is pointwise bounded. At any positive
scale `r`, the bound is its Hölder constant times `r^α`, plus the `Lᵖ` norm multiplied by
the reciprocal `p`-th root of the volume of the radius-`r` ball. -/
theorem enorm_le_add_eLpNorm (hg : HolderWith C α g) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖g x‖ₑ ≤ C * ENNReal.ofReal r ^ (α : ℝ) +
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu := by
  -- Pass to the completion of `F`, which changes neither the Hölder constant, nor the `Lᵖ` norm,
  -- nor the pointwise norms.
  let e : F → UniformSpace.Completion F := (↑)
  have hge : HolderWith C α (e ∘ g) :=
    Isometry.comp_holderWith UniformSpace.Completion.coe_isometry hg
  have hgeLp : MemLp (e ∘ g) p mu :=
    hgLp.of_le ((UniformSpace.Completion.continuous_coe F).comp_aestronglyMeasurable
      hgLp.aestronglyMeasurable)
      (.of_forall fun y ↦ (UniformSpace.Completion.norm_coe (g y)).le)
  have hnorm : eLpNorm (e ∘ g) p mu = eLpNorm g p mu :=
    eLpNorm_congr_eNorm_ae hgeLp.aestronglyMeasurable hgLp.aestronglyMeasurable
      (.of_forall fun y ↦ UniformSpace.Completion.eNorm_coe (g y))
  simpa only [Function.comp_apply, e, UniformSpace.Completion.eNorm_coe, hnorm] using
    enorm_le_add_eLpNorm_of_completeSpace hge hp hp' hgeLp hr x

/-- Real-valued form of `HolderWith.enorm_le_add_eLpNorm`: a globally Hölder function with finite
`Lᵖ` norm is pointwise bounded by its Hölder constant times `r ^ α` plus its `Lᵖ` norm times the
reciprocal `p`-th root of the volume of the radius-`r` ball. -/
theorem norm_le_add_eLpNorm_toReal (hg : HolderWith C α g) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖g x‖ ≤ C * r ^ (α : ℝ) +
      (mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹)).toReal * (eLpNorm g p mu).toReal := by
  have hvol : mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 hr).ne' measure_ball_lt_top.ne
  have hx := hg.enorm_le_add_eLpNorm hp hp' hgLp hr x
  have hfin : (C : ℝ≥0∞) * ENNReal.ofReal r ^ (α : ℝ) +
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu ≠ ∞ := by
    finiteness
  have hx' := (ENNReal.toReal_le_toReal eNorm_ne_top hfin).2 hx
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top hvol hgLp.eLpNorm_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hr.le] at hx'
  simpa only [toReal_eNorm] using hx'

/-- A global Hölder function in `Lᵖ`, bundled as an element of the Hölder normed space. -/
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
    have hx : ‖g x‖ₑ ≤ R := by
      simpa [R] using hg.enorm_le_add_eLpNorm hp hp' hgLp one_pos x
    simpa only [toReal_eNorm] using (ENNReal.toReal_le_toReal eNorm_ne_top hR).2 hx
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
    have hunit : ‖g x‖ₑ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) *
        eLpNorm g p mu := by
      simpa using hg.enorm_le_add_eLpNorm hp hp' hgLp one_pos x
    have hfin : (C : ℝ≥0∞) + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) *
        eLpNorm g p mu ≠ ∞ := by
      rw [← lt_top_iff_ne_top, ENNReal.add_lt_top]
      exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
          (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)) hgLp.eLpNorm_lt_top⟩
    simpa only [toReal_eNorm] using (ENNReal.toReal_le_toReal eNorm_ne_top hfin).2 hunit
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

namespace HolderOnWith

open MeasureTheory Metric Module
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {G : E → F} {K α : ℝ≥0} {s : Set E} {x₀ y : E} {r : ℝ}

/-- **The `L²` oscillation of a Hölder function.** If `G` is `α`-Hölder with constant `K` on a set
`s ⊆ ball x₀ r` and `y ∈ s`, then `∫_s ‖G - G y‖² ≤ 2^(2α) |B₁| K² r^(n + 2α)`, where `|B₁|` is
the measure of the unit ball and `n` is the dimension. -/
theorem setIntegral_norm_sub_sq_le (hG : HolderOnWith K α G s) (hsr : s ⊆ ball x₀ r)
    (hy : y ∈ s) :
    ∫ x in s, ‖G x - G y‖ ^ 2 ∂mu ≤
      2 ^ (2 * (α : ℝ)) * mu.real (ball (0 : E) 1) * (K : ℝ) ^ 2 *
        r ^ ((finrank ℝ E : ℝ) + 2 * α) := by
  have hr : 0 < r := pos_of_mem_ball (hsr hy)
  -- On `s`, `G` stays within `K (2 r)^α` of `G y`.
  have hbd : ∀ x ∈ s, ‖‖G x - G y‖ ^ 2‖ ≤ ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 := fun x hx => by
    rw [norm_pow, norm_norm, ← dist_eq_norm]
    refine pow_le_pow_left₀ dist_nonneg ((hG.dist_le hx hy).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg ?_ α.2) K.2)) 2
    linarith [dist_triangle_right x y x₀, mem_ball.1 (hsr hx), mem_ball.1 (hsr hy)]
  have hs : mu s < ⊤ := (measure_mono hsr).trans_lt measure_ball_lt_top
  have hvol : mu.real s ≤ r ^ finrank ℝ E * mu.real (ball (0 : E) 1) := by
    rw [← mu.addHaar_real_ball_of_pos x₀ hr]
    exact measureReal_mono hsr measure_ball_lt_top.ne
  have h2 : ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 =
      2 ^ (2 * (α : ℝ)) * (K : ℝ) ^ 2 * r ^ (2 * (α : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast ((2 * r) ^ (α : ℝ)) 2, ← Real.rpow_mul (by linarith),
      Real.mul_rpow (by norm_num) hr.le, mul_comm (α : ℝ)]
    push_cast
    ring
  calc ∫ x in s, ‖G x - G y‖ ^ 2 ∂mu
      ≤ ‖∫ x in s, ‖G x - G y‖ ^ 2 ∂mu‖ := Real.le_norm_self _
    _ ≤ ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 * mu.real s :=
      norm_setIntegral_le_of_norm_le_const hs hbd
    _ ≤ ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 * (r ^ finrank ℝ E * mu.real (ball (0 : E) 1)) := by
      gcongr
    _ = 2 ^ (2 * (α : ℝ)) * mu.real (ball (0 : E) 1) * (K : ℝ) ^ 2 *
        r ^ ((finrank ℝ E : ℝ) + 2 * α) := by
      rw [h2, Real.rpow_add hr, Real.rpow_natCast]
      ring

end HolderOnWith
