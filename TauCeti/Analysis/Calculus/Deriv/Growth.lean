/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Linear growth from a convergent derivative

If the derivative of a function `f` of one real variable tends to `c` at `+∞`, then `f` grows like
`x • c`: `x⁻¹ • f x → c` (`TauCeti.tendsto_inv_smul_atTop_of_tendsto_deriv`). This is the `∞ / ∞`
form of l'Hôpital's rule with denominator `x`, which Mathlib's `HasDerivAt.lhopital_zero_atTop`
(a `0 / 0` statement) does not cover. The local counterpart at a point, integrating a little-o
bound on the derivative, is Mathlib's `Convex.isLittleO_pow_succ_real`.
-/

public section

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}

namespace TauCeti

/-- **Linear growth from a convergent derivative.** If the derivative of `f` tends to `c` at
`+∞`, then `x⁻¹ • f x` tends to `c`. -/
theorem tendsto_inv_smul_atTop_of_tendsto_deriv {c : E}
    (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x) (hf' : Tendsto f' atTop (𝓝 c)) :
    Tendsto (fun x ↦ x⁻¹ • f x) atTop (𝓝 c) := by
  -- Subtract the linear function `x • c`; its remainder `g` has derivative tending to `0`.
  set g : ℝ → E := fun x ↦ f x - x • c with hg_def
  have hg : ∀ᶠ x in atTop, HasDerivAt g (f' x - c) x :=
    hf.mono fun x hx ↦ by
      convert hx.sub ((hasDerivAt_id x).smul_const c) using 1 <;> first | rfl | simp
  have hg' : Tendsto (fun x ↦ f' x - c) atTop (𝓝 0) := by
    simpa using hf'.sub_const c
  suffices h : Tendsto (fun x ↦ x⁻¹ • g x) atTop (𝓝 0) by
    refine (by simpa using h.add_const c : Tendsto (fun x ↦ x⁻¹ • g x + c) atTop (𝓝 c)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [hg_def, smul_sub, smul_smul, inv_mul_cancel₀ hx.ne']
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hg.and
    ((NormedAddGroup.tendsto_nhds_zero.1 hg') (ε / 2) (half_pos hε)))
  set a' := max a 0
  filter_upwards [eventually_gt_atTop (a' + 4 * ‖g a'‖ / ε)] with x hx
  have ha'x : a' ≤ x := by
    have : 0 ≤ 4 * ‖g a'‖ / ε := by positivity
    linarith
  have hx0 : 0 < x := by
    have : 0 ≤ 4 * ‖g a'‖ / ε := by positivity
    linarith [le_max_right a 0]
  -- The mean value inequality on `[a', x]`.
  have hmvt : ‖g x - g a'‖ ≤ ε / 2 * (x - a') :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y hy ↦ ((ha y ((le_max_left a 0).trans hy.1)).1).hasDerivWithinAt)
      (fun y hy ↦ ((ha y ((le_max_left a 0).trans hy.1)).2).le) x ⟨ha'x, le_rfl⟩
  have hga : ‖g a'‖ < ε / 4 * x := by
    have h4 : 4 * ‖g a'‖ / ε < x := by linarith [le_max_right a 0]
    rw [div_lt_iff₀ hε] at h4
    linarith
  have hgx : ‖g x‖ < ε * x := by
    have := norm_le_insert' (g x) (g a')
    nlinarith [le_max_right a 0]
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hx0.le, inv_mul_lt_iff₀ hx0]
  linarith

end TauCeti
