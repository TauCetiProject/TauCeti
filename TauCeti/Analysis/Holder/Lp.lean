/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Holder.Normed

import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder functions in `Lᵖ`

This file proves that a Hölder function is bounded at each point by its `Lᵖ` norm on a nearby ball,
and bundles a globally Hölder function with finite `Lᵖ` norm as an element of the global Hölder
normed space (a Banach space when the target is complete). The pointwise estimate compares the
value at a point with the values on the ball: Hölder continuity controls the difference, and the
`Lᵖ` norm on the ball controls the values there. For a function Hölder on a set, the ball lies in
the set but need not contain the point, which gives the bound at points of the closure of a
half-space from a ball inside the open half-space. The bounds hold for every exponent `p ≠ 0`,
including `p = ∞`, where the volume factor is `1` and the `Lᵖ` norm is the essential supremum.

## Main declarations

* `HolderOnWith.enorm_le_add_eLpNorm` and `HolderOnWith.norm_le_add_eLpNorm_toReal`: a function
  Hölder on a set is bounded at each of its points by its `Lᵖ` norm on a nearby ball in the set.
* `HolderOnWith.norm_le_add_eLpNorm_toReal_of_halfSpace`: a function Hölder on a closed half-space
  is bounded there by its `Lᵖ` norm on the open half-space.
* `HolderWith.enorm_le_add_eLpNorm`: a global Hölder function has a pointwise bound by its `Lᵖ`
  norm.
* `HolderWith.norm_le_add_eLpNorm_toReal`: the same bound for the real-valued norm.
* `HolderWith.toHolderSpace`: bundle a global Hölder `Lᵖ` function in `TauCeti.HolderSpace`.
* `HolderWith.norm_toHolderSpace_le`: the resulting Hölder-space norm estimate.
-/

public section

noncomputable section

namespace HolderOnWith

open MeasureTheory Metric Set
open scoped ENNReal NNReal InnerProductSpace

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F] {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F}
  {C α : ℝ≥0} {p : ℝ≥0∞} {s : Set E}

/-- A function that is `α`-Hölder with constant `C` on a set `s` is bounded at each point `x ∈ s`
by its `Lᵖ` norm on any ball `B(y, ρ) ⊆ s`: the bound is `C (dist x y + ρ)^α` plus that `Lᵖ` norm
times the reciprocal `p`-th root of the volume of the radius-`ρ` ball. The point `x` need not lie
in the ball, so this applies at points of the boundary of a half-space, with a ball inside the
half-space. -/
theorem enorm_le_add_eLpNorm (hg : HolderOnWith C α g s) (hp : p ≠ 0) {x y : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ s) (hys : ball y ρ ⊆ s) :
    ‖g x‖ₑ ≤ C * ENNReal.ofReal (dist x y + ρ) ^ (α : ℝ) +
      mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) * eLpNorm g p (mu.restrict (ball y ρ)) := by
  set N := eLpNorm g p (mu.restrict (ball y ρ))
  -- At every point `z` of the ball, `‖g x‖ₑ ≤ ‖g z‖ₑ + C (dist x y + ρ)^α`, since
  -- `dist x z < dist x y + ρ`.
  have hpt : ∀ z ∈ ball y ρ, ‖g x‖ₑ - C * ENNReal.ofReal (dist x y + ρ) ^ (α : ℝ) ≤ ‖g z‖ₑ :=
    fun z hz => by
      rw [tsub_le_iff_right]
      calc ‖g x‖ₑ = edist (g x) 0 := (edist_zero_right _).symm
        _ ≤ edist (g z) 0 + edist (g x) (g z) := by
            rw [add_comm]
            exact edist_triangle _ _ _
        _ ≤ ‖g z‖ₑ + C * ENNReal.ofReal (dist x y + ρ) ^ (α : ℝ) := by
            rw [edist_zero_right]
            gcongr
            refine (hg.edist_le hx (hys hz)).trans ?_
            gcongr
            rw [edist_dist]
            exact ENNReal.ofReal_le_ofReal (by linarith [dist_triangle x y z, mem_ball'.1 hz])
  -- So the constant `‖g x‖ₑ - C (dist x y + ρ)^α` has `Lᵖ` norm on the ball at most `N`.
  have hconst : eLpNorm (fun _ : E => ‖g x‖ₑ - C * ENNReal.ofReal (dist x y + ρ) ^ (α : ℝ)) p
      (mu.restrict (ball y ρ)) ≤ N :=
    eLpNorm_mono_eNorm_ae aestronglyMeasurable_const
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun z hz => by
        simpa only [eNorm_eq_self] using hpt z hz))
  rw [eLpNorm_const _ hp (Measure.restrict_eq_zero.not.2 (measure_ball_pos mu y hρ).ne'),
    Measure.restrict_apply_univ, Measure.addHaar_ball_center, eNorm_eq_self] at hconst
  have hm0 : mu (ball (0 : E) ρ) ^ (1 / p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (measure_ball_pos mu 0 hρ) measure_ball_lt_top.ne).ne'
  have hmt : mu (ball (0 : E) ρ) ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  have hdiv : ‖g x‖ₑ - C * ENNReal.ofReal (dist x y + ρ) ^ (α : ℝ) ≤
      mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) * N := by
    rw [ENNReal.rpow_neg, ← one_div p.toReal, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmt)).2 hconst
  exact tsub_le_iff_left.1 hdiv

/-- Real-valued form of `HolderOnWith.enorm_le_add_eLpNorm`, for a function with finite `Lᵖ` norm
on the ball. -/
theorem norm_le_add_eLpNorm_toReal (hg : HolderOnWith C α g s) (hp : p ≠ 0) {x y : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ s) (hys : ball y ρ ⊆ s)
    (hfin : eLpNorm g p (mu.restrict (ball y ρ)) ≠ ∞) :
    ‖g x‖ ≤ C * (dist x y + ρ) ^ (α : ℝ) +
      (mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹)).toReal *
        (eLpNorm g p (mu.restrict (ball y ρ))).toReal := by
  have hvol : mu (ball (0 : E) ρ) ^ (-(p.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 hρ).ne' measure_ball_lt_top.ne
  have hx' := (ENNReal.toReal_le_toReal eNorm_ne_top (by finiteness)).2
    (hg.enorm_le_add_eLpNorm (mu := mu) hp hρ hx hys)
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top hvol hfin),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)] at hx'
  simpa only [toReal_eNorm] using hx'

/-- A function that is `α`-Hölder with constant `C` on the closed half-space `{z | c ≤ ⟪z, ν⟫}`,
`ν ≠ 0`, is bounded at each point `x` of it, for every `r > 0`, by `C r^α` plus its `Lᵖ` norm on
the open half-space `{z | c < ⟪z, ν⟫}` times the reciprocal `p`-th root of the volume of the
radius-`r / 2` ball: compare `g x` with the values of `g` on the ball of radius `r / 2` in the open
half-space whose centre is `x + (r / (2 ‖ν‖)) ν`. -/
theorem norm_le_add_eLpNorm_toReal_of_halfSpace [InnerProductSpace ℝ E] {ν : E} {c r : ℝ}
    (hν : ν ≠ 0) (hr : 0 < r) (hg : HolderOnWith C α g {z | c ≤ ⟪z, ν⟫_ℝ}) (hp : p ≠ 0)
    (hgLp : MemLp g p (mu.restrict {z | c < ⟪z, ν⟫_ℝ})) {x : E} (hx : c ≤ ⟪x, ν⟫_ℝ) :
    ‖g x‖ ≤ C * r ^ (α : ℝ) + (mu (ball (0 : E) (r / 2)) ^ (-(p.toReal)⁻¹)).toReal *
      (eLpNorm g p (mu.restrict {z | c < ⟪z, ν⟫_ℝ})).toReal := by
  have hball : ball (x + (r / 2 / ‖ν‖) • ν) (r / 2) ⊆ {z | c < ⟪z, ν⟫_ℝ} :=
    TauCeti.ball_add_smul_subset_setOf_lt_inner hν hx
  have hxy : dist x (x + (r / 2 / ‖ν‖) • ν) = r / 2 := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg
      (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hν)]
  have hle : eLpNorm g p (mu.restrict (ball (x + (r / 2 / ‖ν‖) • ν) (r / 2))) ≤
      eLpNorm g p (mu.restrict {z | c < ⟪z, ν⟫_ℝ}) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)
  have h := hg.norm_le_add_eLpNorm_toReal (mu := mu) hp (half_pos hr)
    (by simpa only [mem_ofPred_eq] using hx)
    (hball.trans fun _ hz => mem_ofPred.2 (mem_ofPred.1 hz).le)
    (hle.trans_lt hgLp.eLpNorm_lt_top).ne
  rw [hxy, add_halves] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hgLp.eLpNorm_ne_top hle) ENNReal.toReal_nonneg))

end HolderOnWith

namespace HolderWith

open MeasureTheory Metric Set
open scoped ENNReal NNReal BoundedContinuousFunction
open TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F} {C α : ℝ≥0} {p : ℝ≥0∞}

/-- A globally Hölder function is pointwise bounded by its `Lᵖ` norm. At any positive scale `r`,
the bound is its Hölder constant times `r^α`, plus the `Lᵖ` norm multiplied by the reciprocal
`p`-th root of the volume of the radius-`r` ball. -/
theorem enorm_le_add_eLpNorm (hg : HolderWith C α g) (hp : p ≠ 0) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖g x‖ₑ ≤ C * ENNReal.ofReal r ^ (α : ℝ) +
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu := by
  -- Compare `g x` with the values of `g` on the ball of radius `r` about `x`.
  have h := (hg.holderOnWith univ).enorm_le_add_eLpNorm (mu := mu) hp hr (mem_univ x)
    (subset_univ (ball x r))
  rw [dist_self, zero_add] at h
  refine h.trans ?_
  gcongr
  exact Measure.restrict_le_self

/-- Real-valued form of `HolderWith.enorm_le_add_eLpNorm`: a globally Hölder function with finite
`Lᵖ` norm is pointwise bounded by its Hölder constant times `r ^ α` plus its `Lᵖ` norm times the
reciprocal `p`-th root of the volume of the radius-`r` ball. -/
theorem norm_le_add_eLpNorm_toReal (hg : HolderWith C α g) (hp : p ≠ 0) (hgLp : MemLp g p mu)
    {r : ℝ} (hr : 0 < r) (x : E) :
    ‖g x‖ ≤ C * r ^ (α : ℝ) +
      (mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹)).toReal * (eLpNorm g p mu).toReal := by
  have hvol : mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 hr).ne' measure_ball_lt_top.ne
  have hx := hg.enorm_le_add_eLpNorm (mu := mu) hp hr x
  have hfin : (C : ℝ≥0∞) * ENNReal.ofReal r ^ (α : ℝ) +
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu ≠ ∞ := by
    finiteness
  have hx' := (ENNReal.toReal_le_toReal eNorm_ne_top hfin).2 hx
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top hvol hgLp.eLpNorm_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hr.le] at hx'
  simpa only [toReal_eNorm] using hx'

variable [NormedSpace ℝ F]

/-- A global Hölder function in `Lᵖ`, bundled as an element of the Hölder normed space. -/
def toHolderSpace (hg : HolderWith C α g) (hα : 0 < α) (hp : p ≠ 0) (hgLp : MemLp g p mu) :
    TauCeti.HolderSpace α E F := by
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
      simpa [R] using hg.enorm_le_add_eLpNorm (mu := mu) hp one_pos x
    simpa only [toReal_eNorm] using (ENNReal.toReal_le_toReal eNorm_ne_top hR).2 hx
  let G : E →ᵇ F := BoundedContinuousFunction.mkOfBound ⟨g, hg.continuous hα⟩
    (2 * R.toReal) (BoundedContinuousFunction.dist_le_two_norm' hpoint)
  have hG : (G : E → F) = g := by
    funext x
    rfl
  exact TauCeti.HolderSpace.ofBoundedContinuousFunction G (hG.symm ▸ hg.memHolder)

/-- The Hölder-space bundling does not change the underlying function. -/
@[simp]
theorem toHolderSpace_apply (hg : HolderWith C α g) (hα : 0 < α) (hp : p ≠ 0)
    (hgLp : MemLp g p mu) (x : E) : hg.toHolderSpace hα hp hgLp x = g x := by
  rw [← TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
  rw [toHolderSpace, TauCeti.HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  rfl

/-- The Hölder-space norm is controlled by the pointwise bound and the given Hölder
constant. -/
theorem norm_toHolderSpace_le (hg : HolderWith C α g) (hα : 0 < α) (hp : p ≠ 0)
    (hgLp : MemLp g p mu) :
    ‖hg.toHolderSpace hα hp hgLp‖ ≤
      (C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu).toReal + C := by
  rw [TauCeti.HolderSpace.norm_def]
  apply add_le_add
  · rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply, toHolderSpace_apply]
    have hunit : ‖g x‖ₑ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) *
        eLpNorm g p mu := by
      simpa using hg.enorm_le_add_eLpNorm (mu := mu) hp one_pos x
    have hfin : (C : ℝ≥0∞) + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) *
        eLpNorm g p mu ≠ ∞ := by
      rw [← lt_top_iff_ne_top, ENNReal.add_lt_top]
      exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
          (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)) hgLp.eLpNorm_lt_top⟩
    simpa only [toReal_eNorm] using (ENNReal.toReal_le_toReal eNorm_ne_top hfin).2 hunit
  · have hb : HolderWith C α (fun x => hg.toHolderSpace hα hp hgLp x) := by
      intro x y
      simpa only [toHolderSpace_apply] using hg x y
    have heq : ((hg.toHolderSpace hα hp hgLp).toBoundedContinuousFunction : E → F) =
        fun x => hg.toHolderSpace hα hp hgLp x := by
      funext x
      rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
    rw [heq]
    exact_mod_cast hb.nnholderNorm_le

end HolderWith
