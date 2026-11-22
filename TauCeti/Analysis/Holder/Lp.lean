/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Holder.Normed

import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.MeasureTheory.Function.Lp.BallAverage
import TauCeti.Topology.MetricSpace.Holder

/-!
# Global Hölder functions in `Lᵖ`

This file proves that a globally Hölder function with finite `Lᵖ` norm is bounded and bundles it
as an element of the global Hölder normed space (a Banach space when the target is complete). The
pointwise estimate compares the function with its average on a ball: Hölder continuity controls the
difference from the average, while Hölder's inequality controls the average itself. The local form
for a function Hölder on a set compares its value at a point with its values on a ball nearby in
the set.

## Main declarations

* `HolderWith.enorm_le_add_eLpNorm`: a global Hölder function in `Lᵖ` has a pointwise bound.
* `HolderWith.norm_le_add_eLpNorm_toReal`: the same bound for the real-valued norm.
* `HolderOnWith.enorm_le_add_eLpNorm` and `HolderOnWith.norm_le_add_eLpNorm_toReal`: a function
  Hölder on a set is bounded at each of its points by its `Lᵖ` norm on a nearby ball in the set.
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

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F] {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F}
  {C α : ℝ≥0} {p : ℝ≥0∞} {s : Set E}

/-- A function that is `α`-Hölder with constant `C` on a set `s` is bounded at each point `x ∈ s`
by its `Lᵖ` norm on any ball `B(y, ρ) ⊆ s` with `dist x y ≤ ρ`: the bound is `C (2 ρ)^α` plus that
`Lᵖ` norm times the reciprocal `p`-th root of the volume of the radius-`ρ` ball. The point `x`
need not lie in the ball, so this applies at points of the boundary of a half-space, with a ball
inside the half-space. -/
theorem enorm_le_add_eLpNorm (hg : HolderOnWith C α g s) (hp : p ≠ 0) (hp' : p ≠ ∞) {x y : E}
    {ρ : ℝ} (hρ : 0 < ρ) (hx : x ∈ s) (hys : ball y ρ ⊆ s) (hxy : dist x y ≤ ρ) :
    ‖g x‖ₑ ≤ C * ENNReal.ofReal (2 * ρ) ^ (α : ℝ) +
      mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) * eLpNorm g p (mu.restrict (ball y ρ)) := by
  set N := eLpNorm g p (mu.restrict (ball y ρ))
  -- At every point `z` of the ball, `‖g x‖ₑ ≤ ‖g z‖ₑ + C (2 ρ)^α`, since `dist x z < 2 ρ`.
  have hpt : ∀ z ∈ ball y ρ, ‖g x‖ₑ - C * ENNReal.ofReal (2 * ρ) ^ (α : ℝ) ≤ ‖g z‖ₑ :=
    fun z hz => by
      rw [tsub_le_iff_right]
      calc ‖g x‖ₑ = edist (g x) 0 := (edist_zero_right _).symm
        _ ≤ edist (g z) 0 + edist (g x) (g z) := by
            rw [add_comm]
            exact edist_triangle _ _ _
        _ ≤ ‖g z‖ₑ + C * ENNReal.ofReal (2 * ρ) ^ (α : ℝ) := by
            rw [edist_zero_right]
            gcongr
            refine (hg.edist_le hx (hys hz)).trans ?_
            gcongr
            rw [edist_dist]
            exact ENNReal.ofReal_le_ofReal (by linarith [dist_triangle x y z, mem_ball'.1 hz])
  -- So the constant `‖g x‖ₑ - C (2 ρ)^α` has `Lᵖ` norm on the ball at most `N`.
  have hconst : eLpNorm (fun _ : E => ‖g x‖ₑ - C * ENNReal.ofReal (2 * ρ) ^ (α : ℝ)) p
      (mu.restrict (ball y ρ)) ≤ N :=
    eLpNorm_mono_eNorm_ae aestronglyMeasurable_const
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun z hz => by
        simpa only [eNorm_eq_self] using hpt z hz))
  rw [eLpNorm_const' _ hp hp', Measure.restrict_apply_univ, Measure.addHaar_ball_center,
    eNorm_eq_self] at hconst
  have hm0 : mu (ball (0 : E) ρ) ^ (1 / p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (measure_ball_pos mu 0 hρ) measure_ball_lt_top.ne).ne'
  have hmt : mu (ball (0 : E) ρ) ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  have hdiv : ‖g x‖ₑ - C * ENNReal.ofReal (2 * ρ) ^ (α : ℝ) ≤
      mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) * N := by
    rw [ENNReal.rpow_neg, ← one_div p.toReal, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmt)).2 hconst
  exact tsub_le_iff_left.1 hdiv

/-- Real-valued form of `HolderOnWith.enorm_le_add_eLpNorm`, for a function with finite `Lᵖ` norm
on the ball. -/
theorem norm_le_add_eLpNorm_toReal (hg : HolderOnWith C α g s) (hp : p ≠ 0) (hp' : p ≠ ∞)
    {x y : E} {ρ : ℝ} (hρ : 0 < ρ) (hx : x ∈ s) (hys : ball y ρ ⊆ s) (hxy : dist x y ≤ ρ)
    (hfin : eLpNorm g p (mu.restrict (ball y ρ)) ≠ ∞) :
    ‖g x‖ ≤ C * (2 * ρ) ^ (α : ℝ) +
      (mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹)).toReal *
        (eLpNorm g p (mu.restrict (ball y ρ))).toReal := by
  have hvol : mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 hρ).ne' measure_ball_lt_top.ne
  have hx' := (ENNReal.toReal_le_toReal eNorm_ne_top (by finiteness)).2
    (hg.enorm_le_add_eLpNorm (mu := mu) hp hp' hρ hx hys hxy)
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top hvol hfin),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)] at hx'
  simpa only [toReal_eNorm] using hx'

end HolderOnWith
