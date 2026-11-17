/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
public import TauCeti.Analysis.Calculus.Morse.IntervalBase
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.Calculus.Deriv.Growth

/-!
# The index-preserving trajectories of the circle continuation field

For `δ > 0` the function `f_r(θ) = δ cos (2 (θ - r))` on the circle has its maxima at `r + j π`
and its minima at `r + π / 2 + j π`. A path `t ↦ r(t)` which is constant, equal to `r₀`, for
`t ≤ 1/6` and constant, equal to `r₁`, for `t ≥ 5/6` gives the positive parameter field
`TauCeti.circleContinuationField δ r` on the cylinder. Its zeros at `t = 0` and `t = 1` are the
critical points of `f_{r₀}` and `f_{r₁}`, with the index of the critical point raised by one at
`t = 0`, and the continuation map counts its trajectories between zeros of equal index. This file
determines all these trajectories when `δ` is small, in lifted angles.

Write `T = ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt`, the time the parameter `t` takes to cross the window
`[1/6, 5/6]` containing all the variation of the path, and assume `2 δ T < π / 12`; this holds for
instance when `δ < π / 100` (`TauCeti.two_mul_mul_integral_lt_pi_div_twelve`). Outside the window
the angle follows the gradient flow of `f_{r₀}` or of `f_{r₁}`, along which `cos (2 (θ - r_i))`
decreases; inside it the angle moves by at most `2 δ T < π / 12`.

* **Minima.** A trajectory leaving the source minimum `θ₀ = r₀ + j π + π / 2` stays at `θ₀` until
  `t = 1/6`, reaches `t = 5/6` within `π / 12` of `θ₀`, and then flows into the minimum of `f_{r₁}`
  whose basin contains that point. So if `θ₀` lies in
  `(r₁ + k π + π / 12, r₁ + (k + 1) π - π / 12)`, at distance more than `π / 12` from the maxima of
  `f_{r₁}`, every such trajectory ends at the target minimum `r₁ + k π + π / 2`
  (`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`); it exists
  (`TauCeti.exists_circleContinuationField_connection_of_min`) and is unique up to translation of
  time (`TauCeti.exists_eq_comp_add_of_circleContinuationField_min`).
* **Maxima.** Dually, a trajectory arriving at the target maximum `θ₁ = r₁ + k π` stays there after
  `t = 5/6`, and comes from the source maximum whose backward basin contains its point at
  `t = 1/6`: if `θ₁ - r₀ ∈ (j π - π / 2 + π / 12, j π + π / 2 - π / 12)`, it comes from
  `r₀ + j π` (`TauCeti.eq_add_int_mul_pi_of_hasDerivAt_circleContinuationField`). It exists and is
  unique up to translation of time.
* **Admissibility.** Under the same separation, no trajectory runs from a source minimum, of index
  `1`, to a target maximum, of index `1`
  (`TauCeti.ne_add_int_mul_pi_of_hasDerivAt_circleContinuationField`). Trajectories between
  critical points of different index (source maxima of index `2`, target minima of index `0`) are
  not counted by the continuation map.

So in each degree, up to translation of time, exactly one counted trajectory joins each critical
point to the critical point of the same kind in whose basin it lies, and only the end values `r₀`
and `r₁` matter. (The continuation map counts these trajectories with signs coming from orientations
of the unstable manifolds, which are not treated here.) Writing
`r₁ - r₀ = n π + d` with `|d| < 5 π / 12`, minima and maxima are both moved by `d`
(`TauCeti.eq_add_sub_of_hasDerivAt_circleContinuationField_min` and
`TauCeti.eq_sub_sub_of_hasDerivAt_circleContinuationField_max`). This gives the check values of the
circle continuation counterexamples, in the moving labels `p_j(r) = r + j π` and
`q_j(r) = r + π / 2 + j π`, with `j` modulo `2`:

* for the half-turn `r₁ = r₀ + π` every critical point goes to the same point of the circle, so the
  continuation map is the identity `I` in fixed spatial bases, while tracking the labels gives the
  exchange `S`, since `q_j(r₀) = q_{j - 1}(r₁)` and `p_j(r₀) = p_{j - 1}(r₁)`;
* for `r₁ = r₀ + π / 3` the labels are preserved, `q_j ↦ q_j` and `p_j ↦ p_j`: the map is `I`;
* for `r₁ = r₀ + 2 π / 3` they are exchanged, `q_j ↦ q_{j - 1}` and `p_{j + 1} ↦ p_j`: the map is
  `S`. Hence for `β = π / 3` the continuations along `r = β ρ` and along `r = β + β ρ` are both `I`,
  while their concatenation, which runs from `0` to `2 β`, gives `S`.

## Main results

* `TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`: the end of a trajectory
  leaving a source minimum.
* `TauCeti.eq_add_int_mul_pi_of_hasDerivAt_circleContinuationField`: the start of a trajectory
  arriving at a target maximum.
* `TauCeti.ne_add_int_mul_pi_of_hasDerivAt_circleContinuationField`: admissibility.
* `TauCeti.exists_circleContinuationField_connection_of_min`,
  `TauCeti.exists_circleContinuationField_connection_of_max`: existence.
* `TauCeti.exists_eq_comp_add_of_circleContinuationField_min`,
  `TauCeti.exists_eq_comp_add_of_circleContinuationField_max`: uniqueness up to translation.
* `TauCeti.eq_add_sub_of_hasDerivAt_circleContinuationField_min`,
  `TauCeti.eq_sub_sub_of_hasDerivAt_circleContinuationField_max`: the continuation map in terms of
  `r₁ - r₀`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology
open scoped NNReal

namespace TauCeti

/-! ### The angle equation

Along a trajectory of the parameter field, the angle `x` solves `x' = 2 δ sin (2 (x - ρ s))`, where
`ρ s` is the value of the path at the parameter reached at time `s`. -/

section Angle

variable {δ a b c c₀ c₁ : ℝ} {ρ x : ℝ → ℝ}

/-- Where `ρ = c`, the derivative of `cos (2 (x - c))` along the angle equation is
`-4 δ sin² (2 (x - c))`: the function `δ cos (2 (θ - c))` decreases along its gradient flow. -/
private theorem hasDerivAt_cos_angle {s : ℝ} (hx : HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s)
    (hρ : ρ s = c) :
    HasDerivAt (fun s ↦ cos (2 * (x s - c))) (-(4 * δ * sin (2 * (x s - c)) ^ 2)) s := by
  have h := ((hx.sub_const c).const_mul 2).cos
  rw [hρ] at h
  convert h using 1
  ring

/-- On an interval where `ρ = c`, `cos (2 (x - c))` does not increase along the angle equation. -/
private theorem antitoneOn_cos_angle (hδ : 0 ≤ δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) {D : Set ℝ} (hD : Convex ℝ D)
    (hρ : ∀ s ∈ D, ρ s = c) : AntitoneOn (fun s ↦ cos (2 * (x s - c))) D := by
  have hcont : Continuous x := continuous_iff_continuousAt.2 fun s ↦ (hx s).continuousAt
  refine antitoneOn_of_hasDerivWithinAt_nonpos hD (by fun_prop)
    (fun s hs ↦ (hasDerivAt_cos_angle (hx s) (hρ s (interior_subset hs))).hasDerivWithinAt)
    fun s _ ↦ ?_
  have := mul_nonneg hδ (sq_nonneg (sin (2 * (x s - c))))
  linarith

/-- **Backward from a minimum.** If `ρ = c` on `(-∞, a]` and `x` tends at `-∞` to a minimum
`c + j π + π / 2` of `δ cos (2 (θ - c))`, then `x` stays at that minimum up to time `a`. -/
private theorem eq_of_tendsto_atBot_min (hδ : 0 ≤ δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hρ : ∀ s ≤ a, ρ s = c) {j : ℤ}
    (hlim : Tendsto x atBot (𝓝 (c + j * π + π / 2))) : ∀ s ≤ a, x s = c + j * π + π / 2 := by
  have hcont : Continuous x := continuous_iff_continuousAt.2 fun s ↦ (hx s).continuousAt
  have hanti := antitoneOn_cos_angle hδ hx (convex_Iic a) hρ
  have hglim : Tendsto (fun s ↦ cos (2 * (x s - c))) atBot (𝓝 (-1)) := by
    have h : cos (2 * (c + j * π + π / 2 - c)) = -1 :=
      cos_eq_neg_one_iff.2 ⟨j, by ring⟩
    rw [← h]
    exact ((continuous_cos.comp ((continuous_id.sub continuous_const).const_mul 2)).tendsto
      _).comp hlim
  -- `cos (2 (x - c))` decreases from `-1`, so it is `-1` and the angle does not move.
  have hsin : ∀ s ≤ a, sin (2 * (x s - c)) = 0 := fun s hs ↦ by
    have hg : cos (2 * (x s - c)) = -1 := le_antisymm
      (ge_of_tendsto hglim ((eventually_le_atBot s).mono fun u hu ↦ hanti (hu.trans hs) hs hu))
      (neg_one_le_cos _)
    have h1 := sin_sq_add_cos_sq (2 * (x s - c))
    rw [hg] at h1
    exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
  have hconst : ∀ u ≤ a, ∀ s ∈ Icc u a, x s = x u := fun u _ ↦
    constant_of_has_deriv_right_zero hcont.continuousOn fun s hs ↦ by
      have h := hx s
      rw [hρ s hs.2.le, hsin s hs.2.le, mul_zero] at h
      exact h.hasDerivWithinAt
  intro s hs
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_le_atBot s] with u hu
  exact hconst u (hu.trans hs) s ⟨hu, hs⟩

/-- **The basins are invariant.** If `ρ = c` on `[b, ∞)` and `x b - c` lies in the basin
`(k π, (k + 1) π)` of the minimum `c + k π + π / 2` of `δ cos (2 (θ - c))`, then `cos (2 (x - c))`
is less than `1` at `b` and does not increase after `b`, and `x s - c` stays in the basin. -/
private theorem mem_Ioo_of_hasDerivAt_angle (hδ : 0 ≤ δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hρ : ∀ s, b ≤ s → ρ s = c)
    {k : ℤ} (hk : x b - c ∈ Ioo (k * π) ((k + 1) * π)) :
    cos (2 * (x b - c)) < 1 ∧ ∀ s, b ≤ s →
      x s - c ∈ Ioo (k * π) ((k + 1) * π) ∧ cos (2 * (x s - c)) ≤ cos (2 * (x b - c)) := by
  have hcont : Continuous x := continuous_iff_continuousAt.2 fun s ↦ (hx s).continuousAt
  have hanti := antitoneOn_cos_angle hδ hx (convex_Ici b) hρ
  have hle : ∀ s, b ≤ s → cos (2 * (x s - c)) ≤ cos (2 * (x b - c)) := fun s hs ↦
    hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
  -- `cos (2 (y - c)) = 1` at the maxima, where `y - c` is a multiple of `π`.
  have hone : ∀ y, cos (2 * (y - c)) < 1 → ∀ n : ℤ, y - c ≠ n * π := fun y hy n h ↦ by
    rw [h, show 2 * (n * π) = n * (2 * π) by ring, cos_int_mul_two_pi] at hy
    exact lt_irrefl _ hy
  have hgb : cos (2 * (x b - c)) < 1 := by
    refine lt_of_le_of_ne (cos_le_one _) fun h ↦ ?_
    obtain ⟨n, hn⟩ := (cos_eq_one_iff _).1 h
    have h₁ : (k : ℝ) < n := lt_of_mul_lt_mul_right (by linarith [hk.1]) pi_pos.le
    have h₂ : (n : ℝ) < k + 1 := lt_of_mul_lt_mul_right (by linarith [hk.2]) pi_pos.le
    have h₁' : k < n := by exact_mod_cast h₁
    have h₂' : n < k + 1 := by exact_mod_cast h₂
    omega
  -- So the angle never reaches the maxima bounding the basin.
  refine ⟨hgb, fun s hs ↦ ⟨⟨lt_of_not_ge fun h ↦ ?_, lt_of_not_ge fun h ↦ ?_⟩, hle s hs⟩⟩
  · obtain ⟨u, hu, hxu⟩ := intermediate_value_Icc' hs
      (hcont.sub continuous_const).continuousOn ⟨h, hk.1.le⟩
    exact hone _ ((hle u hu.1).trans_lt hgb) k hxu
  · obtain ⟨u, hu, hxu⟩ := intermediate_value_Icc hs
      (hcont.sub continuous_const).continuousOn ⟨hk.2.le, h⟩
    exact hone _ ((hle u hu.1).trans_lt hgb) (k + 1) (by push_cast; exact hxu)

/-- **Limits are zeros of the field.** If `ρ = c` on `[b, ∞)` and `x` converges at `+∞`, its limit
is a critical point of `δ cos (2 (θ - c))`, since the derivative of `x` converges as well. -/
private theorem sin_eq_zero_of_tendsto_angle (hδ : δ ≠ 0)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hρ : ∀ s, b ≤ s → ρ s = c)
    {θ : ℝ} (hlim : Tendsto x atTop (𝓝 θ)) : sin (2 * (θ - c)) = 0 := by
  have hd : ∀ᶠ s in atTop, HasDerivAt x (2 * δ * sin (2 * (x s - c))) s :=
    (eventually_ge_atTop b).mono fun s hs ↦ by simpa only [hρ s hs] using hx s
  have hd' : Tendsto (fun s ↦ 2 * δ * sin (2 * (x s - c))) atTop
      (𝓝 (2 * δ * sin (2 * (θ - c)))) :=
    ((continuous_const.mul (continuous_sin.comp
      ((continuous_id.sub continuous_const).const_mul 2))).tendsto _).comp hlim
  have h₂ : Tendsto (fun s : ℝ ↦ s⁻¹ • x s) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.smul hlim
  have h := tendsto_nhds_unique (tendsto_inv_smul_atTop_of_tendsto_deriv hd hd') h₂
  simpa [hδ] using h

/-- **Forward into a basin.** If `ρ = c` on `[b, ∞)`, `x b - c` lies in the basin
`(k π, (k + 1) π)` of the minimum `c + k π + π / 2` of `δ cos (2 (θ - c))`, and `x` has a limit at
`+∞`, then this limit is that minimum. -/
private theorem eq_of_tendsto_atTop_of_mem_Ioo (hδ : 0 < δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hρ : ∀ s, b ≤ s → ρ s = c)
    {θ : ℝ} (hlim : Tendsto x atTop (𝓝 θ)) {k : ℤ} (hk : x b - c ∈ Ioo (k * π) ((k + 1) * π)) :
    θ = c + k * π + π / 2 := by
  obtain ⟨hgb, hmem⟩ := mem_Ioo_of_hasDerivAt_angle hδ.le hx hρ hk
  have hev : ∀ᶠ s in atTop, b ≤ s := eventually_ge_atTop b
  have hθ₁ : k * π ≤ θ - c :=
    ge_of_tendsto (hlim.sub_const c) (hev.mono fun s hs ↦ (hmem s hs).1.1.le)
  have hθ₂ : θ - c ≤ (k + 1) * π :=
    le_of_tendsto (hlim.sub_const c) (hev.mono fun s hs ↦ (hmem s hs).1.2.le)
  have hcθ : cos (2 * (θ - c)) < 1 := by
    refine lt_of_le_of_lt (le_of_tendsto ?_ (hev.mono fun s hs ↦ (hmem s hs).2)) hgb
    exact ((continuous_cos.comp ((continuous_id.sub continuous_const).const_mul 2)).tendsto
      _).comp hlim
  -- `2 (θ - c)` is a multiple `n π` of `π` in `[2 k π, (2 k + 2) π]`, and an odd one since the
  -- cosine is not `1` there.
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_of_tendsto_angle hδ.ne' hx hρ hlim)
  have heven : ∀ m : ℤ, n ≠ 2 * m := fun m hm ↦ by
    rw [← hn, hm, show ((2 * m : ℤ) : ℝ) * π = m * (2 * π) by push_cast; ring,
      cos_int_mul_two_pi] at hcθ
    exact lt_irrefl _ hcθ
  have h₁ : ((2 * k : ℤ) : ℝ) ≤ n :=
    le_of_mul_le_mul_right (by push_cast; linarith) pi_pos
  have h₂ : (n : ℝ) ≤ ((2 * k + 2 : ℤ) : ℝ) :=
    le_of_mul_le_mul_right (by push_cast; linarith) pi_pos
  have h₁' : 2 * k ≤ n := by exact_mod_cast h₁
  have h₂' : n ≤ 2 * k + 2 := by exact_mod_cast h₂
  have := heven k
  have := heven (k + 1)
  obtain rfl : n = 2 * k + 1 := by omega
  push_cast at hn
  linarith

/-- The angle moves at speed at most `2 δ`. -/
private theorem abs_sub_le_of_hasDerivAt_angle (hδ : 0 ≤ δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hab : a ≤ b) :
    |x b - x a| ≤ 2 * δ * (b - a) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := x) (C := 2 * δ)
    (fun s _ ↦ (hx s).hasDerivWithinAt) (fun s _ ↦ ?_) b ⟨hab, le_rfl⟩
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * δ)]
    exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)

/-- **Reversing time.** If `x` solves the angle equation for `ρ`, then `s ↦ x (-s)` solves it for
`s ↦ ρ (-s) + π / 2`: the minima and the maxima exchange their roles. -/
private theorem hasDerivAt_comp_neg_angle
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (s : ℝ) :
    HasDerivAt (fun s ↦ x (-s)) (2 * δ * sin (2 * (x (-s) - (ρ (-s) + π / 2)))) s := by
  have h := (hx (-s)).comp s (hasDerivAt_neg s)
  rw [show 2 * (x (-s) - (ρ (-s) + π / 2)) = 2 * (x (-s) - ρ (-s)) - π by ring, sin_sub_pi]
  convert h using 1
  · rfl
  · ring

/-- **Forward from a maximum.** If `ρ = c` on `[b, ∞)` and `x` tends at `+∞` to a maximum `c + k π`
of `δ cos (2 (θ - c))`, then `x` stays at that maximum from time `b` on. -/
private theorem eq_of_tendsto_atTop_max (hδ : 0 ≤ δ)
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) (hρ : ∀ s, b ≤ s → ρ s = c) {k : ℤ}
    (hlim : Tendsto x atTop (𝓝 (c + k * π))) : ∀ s, b ≤ s → x s = c + k * π := by
  have h := eq_of_tendsto_atBot_min (a := -b) (c := c + π / 2) (j := k - 1) hδ
    (hasDerivAt_comp_neg_angle hx) (fun s hs ↦ by rw [hρ (-s) (by linarith)])
    (by
      rw [show c + π / 2 + ((k - 1 : ℤ) : ℝ) * π + π / 2 = c + k * π by push_cast; ring]
      exact hlim.comp tendsto_neg_atBot_atTop)
  intro s hs
  have := h (-s) (by linarith)
  simp only [neg_neg] at this
  rw [this]
  push_cast
  ring

/-- The end of the angle of a trajectory leaving a source minimum. -/
private theorem eq_of_tendsto_angle_min (hδ : 0 < δ) (hab : a ≤ b)
    (hT : 2 * δ * (b - a) < π / 12) (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s)
    (hρ₀ : ∀ s ≤ a, ρ s = c₀) (hρ₁ : ∀ s, b ≤ s → ρ s = c₁) {j k : ℤ} {θ₁ : ℝ}
    (h₀ : Tendsto x atBot (𝓝 (c₀ + j * π + π / 2))) (h₁ : Tendsto x atTop (𝓝 θ₁))
    (hk : c₀ + j * π + π / 2 - c₁ ∈ Ioo (k * π + π / 12) ((k + 1) * π - π / 12)) :
    θ₁ = c₁ + k * π + π / 2 := by
  have hd := abs_sub_le_of_hasDerivAt_angle hδ.le hx hab
  rw [eq_of_tendsto_atBot_min hδ.le hx hρ₀ h₀ a le_rfl] at hd
  have hd' := abs_lt.1 (hd.trans_lt hT)
  exact eq_of_tendsto_atTop_of_mem_Ioo hδ hx hρ₁ h₁
    ⟨by linarith [hk.1, hd'.1], by linarith [hk.2, hd'.2]⟩

/-- The start of the angle of a trajectory arriving at a target maximum: the time reversal of
`eq_of_tendsto_angle_min`. -/
private theorem eq_of_tendsto_angle_max (hδ : 0 < δ) (hab : a ≤ b)
    (hT : 2 * δ * (b - a) < π / 12) (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s)
    (hρ₀ : ∀ s ≤ a, ρ s = c₀) (hρ₁ : ∀ s, b ≤ s → ρ s = c₁) {j k : ℤ} {θ₀ : ℝ}
    (h₀ : Tendsto x atBot (𝓝 θ₀)) (h₁ : Tendsto x atTop (𝓝 (c₁ + k * π)))
    (hj : c₁ + k * π - c₀ ∈ Ioo (j * π - π / 2 + π / 12) (j * π + π / 2 - π / 12)) :
    θ₀ = c₀ + j * π := by
  have h := eq_of_tendsto_angle_min (a := -b) (b := -a) (c₀ := c₁ + π / 2) (c₁ := c₀ + π / 2)
    (j := k - 1) (k := j - 1) hδ (by linarith) (by linarith) (hasDerivAt_comp_neg_angle hx)
    (fun s hs ↦ by rw [hρ₁ (-s) (by linarith)]) (fun s hs ↦ by rw [hρ₀ (-s) (by linarith)])
    (by
      rw [show c₁ + π / 2 + ((k - 1 : ℤ) : ℝ) * π + π / 2 = c₁ + k * π by push_cast; ring]
      exact h₁.comp tendsto_neg_atBot_atTop)
    (h₀.comp tendsto_neg_atTop_atBot)
    (by push_cast; constructor <;> linarith [hj.1, hj.2])
  push_cast at h
  linarith

/-- The angle equation has a unique solution with a given value at a given time, since its right
side is `4 |δ|`-Lipschitz in the angle. -/
private theorem eq_of_hasDerivAt_angle {y : ℝ → ℝ}
    (hx : ∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s)
    (hy : ∀ s, HasDerivAt y (2 * δ * sin (2 * (y s - ρ s))) s) {s₀ : ℝ} (h : x s₀ = y s₀) :
    x = y := by
  have hlip : ∀ s, LipschitzWith (4 * ‖δ‖₊) (fun z ↦ 2 * δ * sin (2 * (z - ρ s))) := fun s ↦ by
    refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
    have hs := abs_sin_sub_sin_le (2 * (z - ρ s)) (2 * (z' - ρ s))
    rw [show 2 * (z - ρ s) - 2 * (z' - ρ s) = 2 * (z - z') by ring, abs_mul, abs_two] at hs
    simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm, Real.norm_eq_abs]
    rw [← mul_sub, abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg δ]
  exact ODE_solution_unique_univ (v := fun s z ↦ 2 * δ * sin (2 * (z - ρ s)))
    (s := fun _ ↦ univ) (fun s ↦ (hlip s).lipschitzOnWith) (fun s ↦ ⟨hx s, mem_univ _⟩)
    (fun s ↦ ⟨hy s, mem_univ _⟩) h

/-- **The flow into a minimum.** If `ρ = c` on `[b, ∞)`, then
`c + k π + π / 2 + arctan (A e^{-4 δ (s - b)})` solves the angle equation on `[b, ∞)`. -/
private theorem hasDerivAt_arctan_angle (hρ : ∀ s, b ≤ s → ρ s = c) (k : ℤ) (A : ℝ) {s : ℝ}
    (hs : b ≤ s) :
    HasDerivAt (fun s ↦ c + k * π + π / 2 + arctan (A * exp (-(4 * δ * (s - b)))))
      (2 * δ * sin (2 * (c + k * π + π / 2 + arctan (A * exp (-(4 * δ * (s - b)))) - ρ s))) s := by
  have h1 : HasDerivAt (fun s ↦ -(4 * δ * (s - b))) (-(4 * δ)) s := by
    have h := ((hasDerivAt_id' s).sub_const b).const_mul (-(4 * δ))
    simp only [mul_one, neg_mul] at h
    exact h
  have h := (h1.exp.const_mul A).arctan.const_add (c + k * π + π / 2)
  -- Relative to the minimum the angle is `arctan y`, and `sin (2 arctan y) = 2 y / (1 + y²)`.
  have hsin : ∀ y, sin (arctan y) * cos (arctan y) = y / (1 + y ^ 2) := fun y ↦ by
    rw [sin_arctan, cos_arctan, div_mul_div_comm, mul_one, mul_self_sqrt (by positivity)]
  rw [hρ s hs, show 2 * (c + k * π + π / 2 + arctan (A * exp (-(4 * δ * (s - b)))) - c) =
    2 * arctan (A * exp (-(4 * δ * (s - b)))) + π + (k : ℝ) * (2 * π) by ring,
    sin_add_int_mul_two_pi, sin_add_pi, sin_two_mul, mul_assoc 2 (sin _), hsin]
  convert h using 1
  field_simp
  ring

private theorem tendsto_arctan_angle (hδ : 0 < δ) (A : ℝ) :
    Tendsto (fun s ↦ c + arctan (A * exp (-(4 * δ * (s - b))))) atTop (𝓝 c) := by
  have h : Tendsto (fun s ↦ A * exp (-(4 * δ * (s - b)))) atTop (𝓝 0) := by
    have hsub : Tendsto (fun s ↦ s - b) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-b) tendsto_id).congr fun s ↦ (sub_eq_add_neg s b).symm
    simpa using (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (hsub.const_mul_atTop (by positivity : 0 < 4 * δ)))).const_mul A
  simpa using tendsto_const_nhds.add ((continuous_arctan.tendsto 0).comp h)

/-- **Across the window.** On `[a, b]` the angle equation has a solution starting from `θ₀` at time
`a`, by the Picard–Lindelöf theorem, and it moves by at most `2 δ (b - a)`. -/
private theorem exists_angle_window (hδ : 0 < δ) (hab : a < b) (hρ : Continuous ρ) (θ₀ : ℝ) :
    ∃ X : ℝ → ℝ, X a = θ₀ ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt X (2 * δ * sin (2 * (X s - ρ s))) (Icc a b) s) ∧
      |X b - θ₀| ≤ 2 * δ * (b - a) := by
  set f : ℝ → ℝ → ℝ := fun s z ↦ 2 * δ * sin (2 * (z - ρ s))
  have hf : ∀ s z, |f s z| ≤ 2 * δ := fun s z ↦ by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * δ)]
    exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)
  have hPL : IsPicardLindelof f (tmin := a) (tmax := b) ⟨a, left_mem_Icc.2 hab.le⟩ θ₀
      ⟨2 * δ * (b - a), by nlinarith⟩ 0 ⟨2 * δ, by positivity⟩ ⟨4 * δ, by positivity⟩ := by
    refine ⟨fun s _ ↦ (LipschitzWith.of_dist_le_mul fun z z' ↦ ?_).lipschitzOnWith,
      fun z _ ↦ by fun_prop, fun s _ z _ ↦ ?_, ?_⟩
    · have hs := abs_sin_sub_sin_le (2 * (z - ρ s)) (2 * (z' - ρ s))
      rw [show 2 * (z - ρ s) - 2 * (z' - ρ s) = 2 * (z - z') by ring, abs_mul, abs_two] at hs
      -- Unfold the coercion of the `ℝ≥0` Lipschitz constant.
      change dist (f s z) (f s z') ≤ (4 * δ) * dist z z'
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_mul, abs_two, abs_of_pos hδ]
      nlinarith
    · -- Unfold the coercion of the `ℝ≥0` bound.
      change ‖f s z‖ ≤ 2 * δ
      exact (Real.norm_eq_abs _).trans_le (hf s z)
    · -- Unfold the coercions of the `ℝ≥0` constants and of the initial time.
      change 2 * δ * max (b - a) (a - a) ≤ 2 * δ * (b - a) - 0
      rw [sub_self, max_eq_left (by linarith), sub_zero]
  obtain ⟨X, hXa, hX⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨X, hXa, hX, ?_⟩
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := X) (C := 2 * δ) hX
    (fun s _ ↦ (Real.norm_eq_abs _).trans_le (hf s _)) b ⟨hab.le, le_rfl⟩
  rwa [Real.norm_eq_abs, show X a = θ₀ from hXa] at h

/-- **Gluing.** Let `θ₀` be an equilibrium of the angle equation up to time `a`, `X` a solution on
`[a, b]` starting from `θ₀`, and `R` a solution on `[b, ∞)` starting from `X b`. Then the angle
equal to `θ₀`, then to `X`, then to `R` is a solution on the whole line. -/
private theorem exists_hasDerivAt_angle_of_pieces (hab : a < b) {θ₀ : ℝ} {X R : ℝ → ℝ}
    (hzero : ∀ s ≤ a, sin (2 * (θ₀ - ρ s)) = 0) (hXa : X a = θ₀)
    (hX : ∀ s ∈ Icc a b, HasDerivWithinAt X (2 * δ * sin (2 * (X s - ρ s))) (Icc a b) s)
    (hRb : R b = X b) (hR : ∀ s, b ≤ s → HasDerivAt R (2 * δ * sin (2 * (R s - ρ s))) s) :
    ∃ x : ℝ → ℝ, (∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) ∧
      (∀ s ≤ a, x s = θ₀) ∧ ∀ s, b ≤ s → x s = R s := by
  set x : ℝ → ℝ := fun s ↦ if s ≤ a then θ₀ else if s ≤ b then X s else R s
  have hx₀ : ∀ s ≤ a, x s = θ₀ := fun s hs ↦ by simp only [x, hs, ↓reduceIte]
  have hxX : ∀ s ∈ Icc a b, x s = X s := fun s hs ↦ by
    rcases hs.1.eq_or_lt with rfl | h
    · rw [hx₀ _ le_rfl, hXa]
    · simp only [x, not_le.2 h, hs.2, ↓reduceIte]
  have hxR : ∀ s, b ≤ s → x s = R s := fun s hs ↦ by
    rcases hs.eq_or_lt with rfl | h
    · rw [hxX _ ⟨hab.le, le_rfl⟩, hRb]
    · simp only [x, not_le.2 (hab.trans h), not_le.2 h, ↓reduceIte]
  have hleft : ∀ s ≤ a, HasDerivWithinAt x (2 * δ * sin (2 * (x s - ρ s))) (Iic a) s :=
    fun s hs ↦ by
      rw [hx₀ s hs, hzero s hs, mul_zero]
      exact (hasDerivWithinAt_const s _ θ₀).congr (fun y hy ↦ hx₀ y hy) (hx₀ s hs)
  have hmid : ∀ s ∈ Icc a b, HasDerivWithinAt x (2 * δ * sin (2 * (x s - ρ s))) (Icc a b) s :=
    fun s hs ↦ by
      rw [hxX s hs]
      exact (hX s hs).congr (fun y hy ↦ hxX y hy) (hxX s hs)
  have hright : ∀ s, b ≤ s → HasDerivWithinAt x (2 * δ * sin (2 * (x s - ρ s))) (Ici b) s :=
    fun s hs ↦ by
      rw [hxR s hs]
      exact (hR s hs).hasDerivWithinAt.congr (fun y hy ↦ hxR y hy) (hxR s hs)
  refine ⟨x, fun s ↦ ?_, hx₀, hxR⟩
  rcases lt_trichotomy s a with h | rfl | h
  · exact (hleft s h.le).hasDerivAt (Iic_mem_nhds h)
  · rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
    exact (hleft _ le_rfl).union
      ((hmid _ ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab))
  rcases lt_trichotomy s b with h' | rfl | h'
  · exact (hmid s ⟨h.le, h'.le⟩).hasDerivAt (Icc_mem_nhds h h')
  · rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
    exact ((hmid _ ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)).union
      (hright _ le_rfl)
  · exact (hright s h'.le).hasDerivAt (Ici_mem_nhds h')

/-- **Existence of the trajectory leaving a source minimum.** The angle stays at the source minimum
up to time `a`, crosses the window `[a, b]` within `π / 12` of it, and then flows into the target
minimum along the explicit solution `hasDerivAt_arctan_angle`. -/
private theorem exists_angle_min (hδ : 0 < δ) (hab : a < b) (hT : 2 * δ * (b - a) < π / 12)
    (hρ : Continuous ρ) (hρ₀ : ∀ s ≤ a, ρ s = c₀) (hρ₁ : ∀ s, b ≤ s → ρ s = c₁) {j k : ℤ}
    (hk : c₀ + j * π + π / 2 - c₁ ∈ Ioo (k * π + π / 12) ((k + 1) * π - π / 12)) :
    ∃ x : ℝ → ℝ, (∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) ∧
      (∀ s ≤ a, x s = c₀ + j * π + π / 2) ∧ Tendsto x atTop (𝓝 (c₁ + k * π + π / 2)) := by
  obtain ⟨X, hXa, hX, hXb⟩ := exists_angle_window hδ hab hρ (c₀ + j * π + π / 2)
  have hXb' := abs_lt.1 (hXb.trans_lt hT)
  set A := tan (X b - (c₁ + k * π + π / 2))
  have hRb : c₁ + k * π + π / 2 + arctan (A * exp (-(4 * δ * (b - b)))) = X b := by
    rw [sub_self, mul_zero, neg_zero, exp_zero, mul_one,
      arctan_tan (by linarith [hk.1, hXb'.1]) (by linarith [hk.2, hXb'.2])]
    ring
  have hzero : ∀ s ≤ a, sin (2 * (c₀ + j * π + π / 2 - ρ s)) = 0 := fun s hs ↦ by
    rw [hρ₀ s hs, show 2 * (c₀ + j * π + π / 2 - c₀) = (2 * j + 1 : ℤ) * π by push_cast; ring,
      sin_int_mul_pi]
  obtain ⟨x, hx, hx₀, hxR⟩ := exists_hasDerivAt_angle_of_pieces hab hzero hXa hX hRb
    fun s hs ↦ hasDerivAt_arctan_angle hρ₁ k A hs
  refine ⟨x, hx, hx₀, (tendsto_arctan_angle (b := b) hδ A).congr' ?_⟩
  filter_upwards [eventually_ge_atTop b] with s hs
  exact (hxR s hs).symm

/-- **Existence of the trajectory arriving at a target maximum**: the time reversal of
`exists_angle_min`. -/
private theorem exists_angle_max (hδ : 0 < δ) (hab : a < b) (hT : 2 * δ * (b - a) < π / 12)
    (hρ : Continuous ρ) (hρ₀ : ∀ s ≤ a, ρ s = c₀) (hρ₁ : ∀ s, b ≤ s → ρ s = c₁) {j k : ℤ}
    (hj : c₁ + k * π - c₀ ∈ Ioo (j * π - π / 2 + π / 12) (j * π + π / 2 - π / 12)) :
    ∃ x : ℝ → ℝ, (∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - ρ s))) s) ∧
      Tendsto x atBot (𝓝 (c₀ + j * π)) ∧ ∀ s, b ≤ s → x s = c₁ + k * π := by
  obtain ⟨y, hy, hy₀, hy₁⟩ := exists_angle_min (ρ := fun s ↦ ρ (-s) + π / 2) (a := -b) (b := -a)
    (c₀ := c₁ + π / 2) (c₁ := c₀ + π / 2) (j := k - 1) (k := j - 1) hδ (by linarith)
    (by linarith) (by fun_prop) (fun s hs ↦ by rw [hρ₁ (-s) (by linarith)])
    (fun s hs ↦ by rw [hρ₀ (-s) (by linarith)])
    (by push_cast; constructor <;> linarith [hj.1, hj.2])
  refine ⟨fun s ↦ y (-s), fun s ↦ ?_, ?_, fun s hs ↦ ?_⟩
  · have h := hasDerivAt_comp_neg_angle hy s
    simp only [neg_neg] at h
    rwa [show 2 * (y (-s) - (ρ s + π / 2 + π / 2)) = 2 * (y (-s) - ρ s) - 2 * π by ring,
      sin_sub_two_pi] at h
  · rw [show c₀ + j * π = c₀ + π / 2 + ((j - 1 : ℤ) : ℝ) * π + π / 2 by push_cast; ring]
    exact hy₁.comp tendsto_neg_atBot_atTop
  · beta_reduce
    rw [hy₀ (-s) (by linarith)]
    push_cast
    ring

end Angle

/-! ### Trajectories of the parameter field -/

section Trajectory

variable {δ r₀ r₁ θ₀ θ₁ : ℝ} {r : ℝ → ℝ} {γ : ℝ → ℝ × ℝ}

private theorem hasDerivAt_fst_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).1) (2 * δ * sin (2 * ((γ s).1 - r (γ s).2))) s := by
  have e : circleContinuationField δ r (γ s) =
      (2 * δ * sin (2 * ((γ s).1 - r (γ s).2)), (γ s).2 * (1 - (γ s).2 ^ 2)) :=
    circleContinuationField_apply δ r (γ s).1 (γ s).2
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s)
  rw [e] at h
  exact h

private theorem hasDerivAt_snd_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (1 * (γ s).2 * (1 - (γ s).2 ^ 2)) s := by
  have e : circleContinuationField δ r (γ s) =
      (2 * δ * sin (2 * ((γ s).1 - r (γ s).2)), 1 * (γ s).2 * (1 - (γ s).2 ^ 2)) := by
    rw [one_mul]
    exact circleContinuationField_apply δ r (γ s).1 (γ s).2
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s)
  rw [e] at h
  exact h

/-- **The crossing window of a trajectory.** Along a trajectory of the parameter field from `t = 0`
to `t = 1`, the parameter is at most `1/6` up to a time `a` and at least `5/6` from a time `b`,
and `b - a = ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt`. -/
private theorem exists_window (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (h₀ : Tendsto (fun s ↦ (γ s).2) atBot (𝓝 0)) (h₁ : Tendsto (fun s ↦ (γ s).2) atTop (𝓝 1)) :
    ∃ a b, a < b ∧ b - a = ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ ∧
      (∀ s ≤ a, (γ s).2 ≤ 1 / 6) ∧ ∀ s, b ≤ s → 5 / 6 ≤ (γ s).2 := by
  have hτ := hasDerivAt_snd_circleContinuationField hγ
  have hmem := mem_Ioo_of_hasDerivAt_of_tendsto zero_le_one hτ h₀ h₁
  have hU := intervalBaseTimeCoordinate_eq_add_of_hasDerivAt hτ hmem
  have h16 : (1 / 6 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have h56 : (5 / 6 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  set e := intervalBaseTimeCoordinate (γ 0).2
  refine ⟨intervalBaseTimeCoordinate (1 / 6) - e, intervalBaseTimeCoordinate (5 / 6) - e, ?_, ?_,
    fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · linarith [strictMonoOn_intervalBaseTimeCoordinate h16 h56 (by norm_num)]
  · rw [integral_inv_mul_one_sub_sq h16 h56]
    ring
  · exact (strictMonoOn_intervalBaseTimeCoordinate.le_iff_le (hmem s) h16).1
      (by rw [hU s]; linarith)
  · exact (strictMonoOn_intervalBaseTimeCoordinate.le_iff_le h56 (hmem s)).1
      (by rw [hU s]; linarith)

/-- **The end of a trajectory leaving a source minimum.** Let the path `r` be `r₀` for `t ≤ 1/6`
and `r₁` for `t ≥ 5/6`, and let `0 < δ` with `2 δ ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt < π / 12`. If a
trajectory of the parameter field runs from the source minimum `(r₀ + j π + π / 2, 0)` to a point
`(θ₁, 1)`, and `r₀ + j π + π / 2 - r₁ ∈ (k π + π / 12, (k + 1) π - π / 12)`, then `θ₁` is the target
minimum `r₁ + k π + π / 2`. -/
theorem eq_add_pi_div_two_of_hasDerivAt_circleContinuationField (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {j k : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (r₀ + j * π + π / 2, 0))) (h₁ : Tendsto γ atTop (𝓝 (θ₁, 1)))
    (hk : r₀ + j * π + π / 2 - r₁ ∈ Ioo (k * π + π / 12) ((k + 1) * π - π / 12)) :
    θ₁ = r₁ + k * π + π / 2 := by
  obtain ⟨a, b, hab, hba, ha, hb⟩ :=
    exists_window hγ ((continuous_snd.tendsto _).comp h₀) ((continuous_snd.tendsto _).comp h₁)
  exact eq_of_tendsto_angle_min hδ hab.le (by rwa [hba]) (hasDerivAt_fst_circleContinuationField hγ)
    (fun s hs ↦ hr₀ _ (ha s hs)) (fun s hs ↦ hr₁ _ (hb s hs)) ((continuous_fst.tendsto _).comp h₀)
    ((continuous_fst.tendsto _).comp h₁) hk

/-- **The start of a trajectory arriving at a target maximum.** Under the hypotheses on `r` and `δ`
of `TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, if a trajectory of the
parameter field runs from a point `(θ₀, 0)` to the target maximum `(r₁ + k π, 1)`, and
`r₁ + k π - r₀ ∈ (j π - π / 2 + π / 12, j π + π / 2 - π / 12)`, then `θ₀` is the source maximum
`r₀ + j π`. -/
theorem eq_add_int_mul_pi_of_hasDerivAt_circleContinuationField (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {j k : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (θ₀, 0))) (h₁ : Tendsto γ atTop (𝓝 (r₁ + k * π, 1)))
    (hj : r₁ + k * π - r₀ ∈ Ioo (j * π - π / 2 + π / 12) (j * π + π / 2 - π / 12)) :
    θ₀ = r₀ + j * π := by
  obtain ⟨a, b, hab, hba, ha, hb⟩ :=
    exists_window hγ ((continuous_snd.tendsto _).comp h₀) ((continuous_snd.tendsto _).comp h₁)
  exact eq_of_tendsto_angle_max hδ hab.le (by rwa [hba]) (hasDerivAt_fst_circleContinuationField hγ)
    (fun s hs ↦ hr₀ _ (ha s hs)) (fun s hs ↦ hr₁ _ (hb s hs)) ((continuous_fst.tendsto _).comp h₀)
    ((continuous_fst.tendsto _).comp h₁) hj

/-- **Admissibility.** Under the hypotheses of
`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, a trajectory leaving the source
minimum `(r₀ + j π + π / 2, 0)` does not end at a target maximum `(r₁ + k' π, 1)`: there is no
connection between these two zeros of index one. -/
theorem ne_add_int_mul_pi_of_hasDerivAt_circleContinuationField (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {j k : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (r₀ + j * π + π / 2, 0))) (h₁ : Tendsto γ atTop (𝓝 (θ₁, 1)))
    (hk : r₀ + j * π + π / 2 - r₁ ∈ Ioo (k * π + π / 12) ((k + 1) * π - π / 12)) (k' : ℤ) :
    θ₁ ≠ r₁ + k' * π := by
  rw [eq_add_pi_div_two_of_hasDerivAt_circleContinuationField hδ hT hr₀ hr₁ hγ h₀ h₁ hk]
  intro h
  have h' : ((2 * (k' - k) : ℤ) : ℝ) * π = (1 : ℤ) * π := by push_cast; linarith
  have := Int.cast_injective (α := ℝ) (mul_right_cancel₀ pi_ne_zero h')
  omega

/-- Along the base orbit `τ = intervalBaseOrbit 1`, the path `r ∘ τ` is `r₀` up to the time
`U(1/6)` and `r₁` from the time `U(5/6)` on, where `U` is the time coordinate of the base, and a
solution `x` of the angle equation for `r ∘ τ` gives the trajectory `(x, τ)` of the parameter
field. -/
private theorem intervalBaseOrbit_window (hr₀ : ∀ t ≤ 1 / 6, r t = r₀)
    (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁) :
    intervalBaseTimeCoordinate (1 / 6) < intervalBaseTimeCoordinate (5 / 6) ∧
      intervalBaseTimeCoordinate (5 / 6) - intervalBaseTimeCoordinate (1 / 6) =
        ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ ∧
      (∀ s ≤ intervalBaseTimeCoordinate (1 / 6), r (intervalBaseOrbit 1 s) = r₀) ∧
      (∀ s, intervalBaseTimeCoordinate (5 / 6) ≤ s → r (intervalBaseOrbit 1 s) = r₁) ∧
      ∀ x : ℝ → ℝ, (∀ s, HasDerivAt x (2 * δ * sin (2 * (x s - r (intervalBaseOrbit 1 s)))) s) →
        ∀ s, HasDerivAt (fun s ↦ (x s, intervalBaseOrbit 1 s))
          (circleContinuationField δ r (x s, intervalBaseOrbit 1 s)) s := by
  have h16 : (1 / 6 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have h56 : (5 / 6 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have hU : ∀ s, intervalBaseTimeCoordinate (intervalBaseOrbit 1 s) = s := fun s ↦ by
    rw [intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul]
  refine ⟨strictMonoOn_intervalBaseTimeCoordinate h16 h56 (by norm_num),
    (integral_inv_mul_one_sub_sq h16 h56).symm, fun s hs ↦ hr₀ _ ?_, fun s hs ↦ hr₁ _ ?_,
    fun x hx s ↦ ?_⟩
  · exact (strictMonoOn_intervalBaseTimeCoordinate.le_iff_le (intervalBaseOrbit_mem_Ioo 1 s)
      h16).1 (by rwa [hU])
  · exact (strictMonoOn_intervalBaseTimeCoordinate.le_iff_le h56
      (intervalBaseOrbit_mem_Ioo 1 s)).1 (by rwa [hU])
  · rw [circleContinuationField_apply]
    have h := HasDerivAt.prodMk (hx s) (hasDerivAt_intervalBaseOrbit 1 s)
    rw [one_mul] at h
    exact h

private theorem continuous_intervalBaseOrbit_one : Continuous (intervalBaseOrbit 1) :=
  continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_intervalBaseOrbit 1 s).continuousAt

/-- **Existence of the trajectory leaving a source minimum.** For a continuous path `r` which is
`r₀` for `t ≤ 1/6` and `r₁` for `t ≥ 5/6`, and `δ` as in
`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, the parameter field has a
trajectory from the source minimum `(r₀ + j π + π / 2, 0)` to the target minimum
`(r₁ + k π + π / 2, 1)` whenever `r₀ + j π + π / 2 - r₁ ∈ (k π + π / 12, (k + 1) π - π / 12)`. -/
theorem exists_circleContinuationField_connection_of_min (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12) (hr : Continuous r)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁) {j k : ℤ}
    (hk : r₀ + j * π + π / 2 - r₁ ∈ Ioo (k * π + π / 12) ((k + 1) * π - π / 12)) :
    ∃ γ : ℝ → ℝ × ℝ, (∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) ∧
      Tendsto γ atBot (𝓝 (r₀ + j * π + π / 2, 0)) ∧
      Tendsto γ atTop (𝓝 (r₁ + k * π + π / 2, 1)) := by
  obtain ⟨hab, hba, hρ₀, hρ₁, htraj⟩ := intervalBaseOrbit_window (δ := δ) hr₀ hr₁
  obtain ⟨x, hx, hx₀, hx₁⟩ := exists_angle_min hδ hab (by rwa [hba])
    (hr.comp continuous_intervalBaseOrbit_one) hρ₀ hρ₁ hk
  refine ⟨fun s ↦ (x s, intervalBaseOrbit 1 s), htraj x hx, ?_,
    hx₁.prodMk_nhds (tendsto_intervalBaseOrbit_atTop one_pos)⟩
  refine (tendsto_const_nhds.congr' ?_).prodMk_nhds (tendsto_intervalBaseOrbit_atBot one_pos)
  filter_upwards [eventually_le_atBot (intervalBaseTimeCoordinate (1 / 6))] with s hs
  exact (hx₀ s hs).symm

/-- **Existence of the trajectory arriving at a target maximum.** For a continuous path `r` which is
`r₀` for `t ≤ 1/6` and `r₁` for `t ≥ 5/6`, and `δ` as in
`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, the parameter field has a
trajectory from the source maximum `(r₀ + j π, 0)` to the target maximum `(r₁ + k π, 1)` whenever
`r₁ + k π - r₀ ∈ (j π - π / 2 + π / 12, j π + π / 2 - π / 12)`. -/
theorem exists_circleContinuationField_connection_of_max (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12) (hr : Continuous r)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁) {j k : ℤ}
    (hj : r₁ + k * π - r₀ ∈ Ioo (j * π - π / 2 + π / 12) (j * π + π / 2 - π / 12)) :
    ∃ γ : ℝ → ℝ × ℝ, (∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) ∧
      Tendsto γ atBot (𝓝 (r₀ + j * π, 0)) ∧ Tendsto γ atTop (𝓝 (r₁ + k * π, 1)) := by
  obtain ⟨hab, hba, hρ₀, hρ₁, htraj⟩ := intervalBaseOrbit_window (δ := δ) hr₀ hr₁
  obtain ⟨x, hx, hx₀, hx₁⟩ := exists_angle_max hδ hab (by rwa [hba])
    (hr.comp continuous_intervalBaseOrbit_one) hρ₀ hρ₁ hj
  refine ⟨fun s ↦ (x s, intervalBaseOrbit 1 s), htraj x hx,
    hx₀.prodMk_nhds (tendsto_intervalBaseOrbit_atBot one_pos), ?_⟩
  refine (tendsto_const_nhds.congr' ?_).prodMk_nhds (tendsto_intervalBaseOrbit_atTop one_pos)
  filter_upwards [eventually_ge_atTop (intervalBaseTimeCoordinate (5 / 6))] with s hs
  exact (hx₁ s hs).symm

/-- Two trajectories from `t = 0` to `t = 1` have parameter components differing by a translation
of time, and the translated angle of the first solves the angle equation of the second. -/
private theorem exists_snd_comp_add_eq {γ' : ℝ → ℝ × ℝ}
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hγ' : ∀ s, HasDerivAt γ' (circleContinuationField δ r (γ' s)) s)
    (h₀ : Tendsto (fun s ↦ (γ s).2) atBot (𝓝 0)) (h₁ : Tendsto (fun s ↦ (γ s).2) atTop (𝓝 1))
    (h₀' : Tendsto (fun s ↦ (γ' s).2) atBot (𝓝 0)) (h₁' : Tendsto (fun s ↦ (γ' s).2) atTop (𝓝 1)) :
    ∃ e, (∀ s, (γ (s + e)).2 = (γ' s).2) ∧ ∀ s, HasDerivAt (fun s ↦ (γ (s + e)).1)
      (2 * δ * sin (2 * ((γ (s + e)).1 - r (γ' s).2))) s := by
  have hτ := hasDerivAt_snd_circleContinuationField hγ
  have hτ' := hasDerivAt_snd_circleContinuationField hγ'
  have hmem := mem_Ioo_of_hasDerivAt_of_tendsto zero_le_one hτ h₀ h₁
  have hmem' := mem_Ioo_of_hasDerivAt_of_tendsto zero_le_one hτ' h₀' h₁'
  set e := intervalBaseTimeCoordinate (γ' 0).2 - intervalBaseTimeCoordinate (γ 0).2
  have hτe : ∀ s, (γ (s + e)).2 = (γ' s).2 := fun s ↦
    strictMonoOn_intervalBaseTimeCoordinate.injOn (hmem _) (hmem' s) (by
      rw [intervalBaseTimeCoordinate_eq_add_of_hasDerivAt hτ hmem,
        intervalBaseTimeCoordinate_eq_add_of_hasDerivAt hτ' hmem']
      ring)
  refine ⟨e, hτe, fun s ↦ ?_⟩
  have h := (hasDerivAt_fst_circleContinuationField hγ (s + e)).comp_add_const s e
  rwa [hτe] at h

/-- **Uniqueness of the trajectory leaving a source minimum.** For `δ ≥ 0` and a path `r` equal to
`r₀` for `t ≤ 1/6`, two trajectories of the parameter field leaving the source minimum
`(r₀ + j π + π / 2, 0)` and reaching `t = 1` differ by a translation of time. -/
theorem exists_eq_comp_add_of_circleContinuationField_min (hδ : 0 ≤ δ)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) {γ' : ℝ → ℝ × ℝ}
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hγ' : ∀ s, HasDerivAt γ' (circleContinuationField δ r (γ' s)) s) {j : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (r₀ + j * π + π / 2, 0)))
    (h₀' : Tendsto γ' atBot (𝓝 (r₀ + j * π + π / 2, 0)))
    (h₁ : Tendsto (fun s ↦ (γ s).2) atTop (𝓝 1)) (h₁' : Tendsto (fun s ↦ (γ' s).2) atTop (𝓝 1)) :
    ∃ e, γ' = fun s ↦ γ (s + e) := by
  obtain ⟨e, hτe, hx⟩ := exists_snd_comp_add_eq hγ hγ' ((continuous_snd.tendsto _).comp h₀) h₁
    ((continuous_snd.tendsto _).comp h₀') h₁'
  obtain ⟨a, -, -, -, ha, -⟩ := exists_window hγ' ((continuous_snd.tendsto _).comp h₀') h₁'
  have hρ : ∀ s ≤ a, r (γ' s).2 = r₀ := fun s hs ↦ hr₀ _ (ha s hs)
  have hxa := eq_of_tendsto_atBot_min hδ hx hρ
    (((continuous_fst.tendsto _).comp h₀).comp (tendsto_atBot_add_const_right _ e tendsto_id)) a
    le_rfl
  have hxa' := eq_of_tendsto_atBot_min hδ (hasDerivAt_fst_circleContinuationField hγ') hρ
    ((continuous_fst.tendsto _).comp h₀') a le_rfl
  have heq := eq_of_hasDerivAt_angle hx (hasDerivAt_fst_circleContinuationField hγ')
    (hxa.trans hxa'.symm)
  refine ⟨e, funext fun s ↦ Prod.ext ?_ (hτe s).symm⟩
  exact (congrFun heq s).symm

/-- **Uniqueness of the trajectory arriving at a target maximum.** For `δ ≥ 0` and a path `r`
equal to `r₁` for `t ≥ 5/6`, two trajectories of the parameter field starting from `t = 0` and
arriving at the target maximum `(r₁ + k π, 1)` differ by a translation of time. -/
theorem exists_eq_comp_add_of_circleContinuationField_max (hδ : 0 ≤ δ)
    (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁) {γ' : ℝ → ℝ × ℝ}
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hγ' : ∀ s, HasDerivAt γ' (circleContinuationField δ r (γ' s)) s) {k : ℤ}
    (h₀ : Tendsto (fun s ↦ (γ s).2) atBot (𝓝 0)) (h₀' : Tendsto (fun s ↦ (γ' s).2) atBot (𝓝 0))
    (h₁ : Tendsto γ atTop (𝓝 (r₁ + k * π, 1))) (h₁' : Tendsto γ' atTop (𝓝 (r₁ + k * π, 1))) :
    ∃ e, γ' = fun s ↦ γ (s + e) := by
  obtain ⟨e, hτe, hx⟩ := exists_snd_comp_add_eq hγ hγ' h₀ ((continuous_snd.tendsto _).comp h₁) h₀'
    ((continuous_snd.tendsto _).comp h₁')
  obtain ⟨-, b, -, -, -, hb⟩ := exists_window hγ' h₀' ((continuous_snd.tendsto _).comp h₁')
  have hρ : ∀ s, b ≤ s → r (γ' s).2 = r₁ := fun s hs ↦ hr₁ _ (hb s hs)
  have hxb := eq_of_tendsto_atTop_max hδ hx hρ
    (((continuous_fst.tendsto _).comp h₁).comp (tendsto_atTop_add_const_right _ e tendsto_id)) b
    le_rfl
  have hxb' := eq_of_tendsto_atTop_max hδ (hasDerivAt_fst_circleContinuationField hγ') hρ
    ((continuous_fst.tendsto _).comp h₁') b le_rfl
  have heq := eq_of_hasDerivAt_angle hx (hasDerivAt_fst_circleContinuationField hγ')
    (hxb.trans hxb'.symm)
  refine ⟨e, funext fun s ↦ Prod.ext ?_ (hτe s).symm⟩
  exact (congrFun heq s).symm

/-! ### The continuation map in terms of `r₁ - r₀` -/

/-- **The continuation map on minima.** Under the hypotheses on `r` and `δ` of
`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, write
`r₁ - r₀ = n π + d` with `|d| < 5 π / 12`. Then a trajectory from a source minimum `(θ₀, 0)` to
`(θ₁, 1)` ends at `θ₁ = θ₀ + d`: every minimum is moved by `d`. -/
theorem eq_add_sub_of_hasDerivAt_circleContinuationField_min (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {j n : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (r₀ + j * π + π / 2, 0))) (h₁ : Tendsto γ atTop (𝓝 (θ₁, 1)))
    (hn : r₁ - r₀ - n * π ∈ Ioo (-(5 * π / 12)) (5 * π / 12)) :
    θ₁ = r₀ + j * π + π / 2 + (r₁ - r₀ - n * π) := by
  rw [eq_add_pi_div_two_of_hasDerivAt_circleContinuationField (k := j - n) hδ hT hr₀ hr₁ hγ h₀ h₁
    (by push_cast; constructor <;> linarith [hn.1, hn.2])]
  push_cast
  ring

/-- **The continuation map on maxima.** Under the hypotheses on `r` and `δ` of
`TauCeti.eq_add_pi_div_two_of_hasDerivAt_circleContinuationField`, write
`r₁ - r₀ = n π + d` with `|d| < 5 π / 12`. Then a trajectory from `(θ₀, 0)` to a target maximum
`(θ₁, 1)` starts at `θ₀ = θ₁ - d`: every maximum is moved by `d`. -/
theorem eq_sub_sub_of_hasDerivAt_circleContinuationField_max (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hr₀ : ∀ t ≤ 1 / 6, r t = r₀) (hr₁ : ∀ t, 5 / 6 ≤ t → r t = r₁)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {k n : ℤ}
    (h₀ : Tendsto γ atBot (𝓝 (θ₀, 0))) (h₁ : Tendsto γ atTop (𝓝 (r₁ + k * π, 1)))
    (hn : r₁ - r₀ - n * π ∈ Ioo (-(5 * π / 12)) (5 * π / 12)) :
    θ₀ = r₁ + k * π - (r₁ - r₀ - n * π) := by
  rw [eq_add_int_mul_pi_of_hasDerivAt_circleContinuationField (j := k + n) hδ hT hr₀ hr₁ hγ h₀ h₁
    (by push_cast; constructor <;> linarith [hn.1, hn.2])]
  push_cast
  ring

/-- **A sufficient smallness condition.** If `0 ≤ δ < π / 100`, then
`2 δ ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt < π / 12`, since `t (1 - t²) ≥ 4 / 25` on `[1/6, 5/6]`. -/
theorem two_mul_mul_integral_lt_pi_div_twelve {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ < π / 100) :
    2 * δ * ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ < π / 12 := by
  have hlow : ∀ t ∈ Icc (1 / 6 : ℝ) (5 / 6), 4 / 25 ≤ t * (1 - t ^ 2) := fun t ht ↦ by
    -- `t (1 - t²)` lies above its chord on `[1/6, 5/6]`, which stays above `4 / 25`.
    have h := mul_nonneg (mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2))
      (by linarith [ht.1] : (0 : ℝ) ≤ t + 1)
    nlinarith [ht.1, ht.2]
  have hle : ∫ t in (1 / 6 : ℝ)..5 / 6, (t * (1 - t ^ 2))⁻¹ ≤
      ∫ _ in (1 / 6 : ℝ)..5 / 6, (25 / 4 : ℝ) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const
      fun t ht ↦ ?_
    · refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) fun t ht ↦ ?_
      exact (ContinuousAt.inv₀ (f := fun t : ℝ ↦ t * (1 - t ^ 2)) (by fun_prop)
        (by linarith [hlow t ht] : t * (1 - t ^ 2) ≠ 0)).continuousWithinAt
    · rw [inv_le_comm₀ (by linarith [hlow t ht]) (by norm_num)]
      norm_num
      linarith [hlow t ht]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith [mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * δ)]

end Trajectory

end TauCeti
