/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
import TauCeti.Analysis.ODE.SinTwoMul

/-!
# Trajectories of small-amplitude circle continuations

A path `t ↦ r(t)` of rotations gives the continuation family `δ cos (2 (θ - r(t)))` on the circle,
with positive parameter field `W = 2 δ sin (2 (θ - r(t))) ∂_θ + t (1 - t²) ∂_t`
(`TauCeti.circleContinuationField`). Let `δ > 0`, and let the path be `r₀` for `t ≤ a` and `r₁` for
`t ≥ b`, where `0 < a ≤ b < 1`. The zeros of `W` at `t = 0` are the maxima `(r₀ + j π, 0)`, of
index `2` for `W`, and the minima `(r₀ + π / 2 + j π, 0)`, of index `1`; at `t = 1` the maxima
`(r₁ + k π, 1)` have index `1` and the minima `(r₁ + π / 2 + k π, 1)` index `0`. The continuation
map counts the unparametrized trajectories of `W` between critical points of the same Morse index
on the circle, that is from a zero of index `d + 1` at `t = 0` to a zero of index `d` at `t = 1`:
from maxima to maxima in degree one, and from minima to minima in degree zero. This file computes
these trajectories when `δ` is small, by the basin of the source or target slice in which a
trajectory ends up.

Trajectories are taken in the plane, with lifted angle `θ`
(`TauCeti.circleContinuationTrajectories`). The parameter component of a trajectory from the level
`t = 0` to the level `t = 1` is a time translate of the trajectory `TauCeti.intervalBaseOrbit 1` of
`t' = t (1 - t²)`, so it crosses the window `a ≤ t ≤ b` in the time
`T = ∫_a^b (t (1 - t²))⁻¹ dt`, during which the angle moves by at most `2 δ T`. Outside the window
the slice is fixed, and the angle `ψ` relative to one of its critical points solves
`ψ' = ± 2 δ sin (2 ψ)`, whose solutions in `(-π / 2, π / 2)` are `arctan (c e^{± 4 δ s})`
(`TauCeti.eqOn_arctan_mul_exp_of_hasDerivAt`).

* **Into a target maximum.** For `δ > 0` the maximum `(r₁ + k π, 1)` repels in the angle, and for
  `δ = 0` the angle is constant, so a trajectory into it arrives along the invariant line
  `θ = r₁ + k π`, and two such trajectories are time translates of each other. Followed backwards
  across the window it drifts by at most `2 δ T`. If `|r₁ + k π - (r₀ + j π)| + 2 δ T < π / 2`, it
  enters the basin of the source maximum `r₀ + j π` and converges to it.
* **Out of a source minimum.** Symmetrically, the trajectory out of the minimum
  `(r₀ + π / 2 + j π, 0)` leaves along `θ = r₀ + π / 2 + j π`, and under the same condition it ends
  at the target minimum `(r₁ + π / 2 + k π, 1)`. No trajectory runs from a source minimum to a
  target maximum, a connection of expected dimension `-1`, as soon as the drift `2 δ T` is smaller
  than the distance between their angles.

These uniqueness and basin statements hold for every path `r` that is constant outside `[a, b]`.
For a Lipschitz path, trajectories exist, so under the condition the trajectories from
`r₀ + j π` to `r₁ + k π`, and from `r₀ + π / 2 + j π` to `r₁ + π / 2 + k π`, are the time
translates of a single one, and these are the only trajectories into the target maximum,
respectively out of the source minimum. For the half-turn `r = π ρ` from `δ cos (2 θ)` to the same
function, the trajectories between the critical points of the common end function therefore join
each critical point to the one at the same lifted angle, whereas following the critical points
along the path exchanges the two maxima and the two minima. The orientations and signs of these
counts are not treated here.

## Main declarations

* `TauCeti.fst_eq_of_mem_circleContinuationTrajectories_int_mul_pi` and
  `TauCeti.fst_eq_of_mem_circleContinuationTrajectories_pi_div_two`: a trajectory into a target
  maximum, respectively out of a source minimum, lies on the invariant line where the slice is
  fixed.
* `TauCeti.exists_eq_comp_add_of_mem_circleContinuationTrajectories_int_mul_pi` and
  `TauCeti.eq_of_mem_circleContinuationTrajectories_int_mul_pi`: uniqueness of the trajectory into
  a target maximum, and its source.
* `TauCeti.exists_circleContinuationTrajectories_int_mul_pi_eq_range`: exactly one trajectory
  between paired maxima, up to time translation.
* `TauCeti.exists_eq_comp_add_of_mem_circleContinuationTrajectories_pi_div_two`,
  `TauCeti.eq_of_mem_circleContinuationTrajectories_pi_div_two` and
  `TauCeti.exists_circleContinuationTrajectories_pi_div_two_eq_range`: the same for minima.
* `TauCeti.circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty_of_lt` and
  `TauCeti.circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty`: no trajectory from a
  source minimum to a target maximum.
* `TauCeti.exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range`,
  `TauCeti.eq_of_mem_circleContinuationTrajectories_pi_mul_int_mul_pi`,
  `TauCeti.exists_circleContinuationTrajectories_pi_mul_pi_div_two_eq_range` and
  `TauCeti.eq_of_mem_circleContinuationTrajectories_pi_mul_pi_div_two`: for the half-turn, the
  trajectories between maxima and between minima join equal lifted angles.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology
open scoped NNReal

namespace TauCeti

section Trajectory

variable {δ : ℝ} {r : ℝ → ℝ} {γ γ' : ℝ → ℝ × ℝ}

/-- Before the time `U a - c` the parameter component of a translate `q (· + c)` of the base orbit
stays below `a`, where `U` is the time coordinate. -/
private theorem apply_snd_eq_of_le {c a r₀ : ℝ} (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c))
    (ha : a ∈ Ioo 0 1) (hr₀ : ∀ t ≤ a, r t = r₀) {s : ℝ}
    (hs : s ≤ intervalBaseTimeCoordinate a - c) : r (γ s).2 = r₀ := by
  refine hr₀ _ ?_
  rw [hc, ← intervalBaseOrbit_one_intervalBaseTimeCoordinate ha]
  exact (strictMono_intervalBaseOrbit one_pos).monotone (by linarith)

/-- After the time `U b - c` the parameter component of a translate `q (· + c)` of the base orbit
stays above `b`, where `U` is the time coordinate. -/
private theorem apply_snd_eq_of_ge {c b r₁ : ℝ} (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c))
    (hb : b ∈ Ioo 0 1) (hr₁ : ∀ t, b ≤ t → r t = r₁) {s : ℝ}
    (hs : intervalBaseTimeCoordinate b - c ≤ s) : r (γ s).2 = r₁ := by
  refine hr₁ _ ?_
  rw [hc, ← intervalBaseOrbit_one_intervalBaseTimeCoordinate hb]
  exact (strictMono_intervalBaseOrbit one_pos).monotone (by linarith)

/-- Where `r = r₀`, the angle relative to the maximum `r₀ + j π` of the slice solves
`ψ' = 2 δ sin (2 ψ)`. -/
private theorem hasDerivAt_fst_sub_int_mul_pi
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {s r₀ : ℝ}
    (hs : r (γ s).2 = r₀) (j : ℤ) :
    HasDerivAt (fun s ↦ (γ s).1 - (r₀ + j * π))
      (2 * δ * sin (2 * ((γ s).1 - (r₀ + j * π)))) s := by
  refine ((hasDerivAt_fst_of_hasDerivAt_circleContinuationField hγ s).sub_const _).congr_deriv ?_
  rw [hs, show 2 * ((γ s).1 - r₀) = 2 * ((γ s).1 - (r₀ + j * π)) + j * (2 * π) by ring,
    sin_add_int_mul_two_pi]

/-- Where `r = r₀`, the angle relative to the minimum `r₀ + π / 2 + j π` of the slice solves
`ψ' = -2 δ sin (2 ψ)`. -/
private theorem hasDerivAt_fst_sub_pi_div_two
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {s r₀ : ℝ}
    (hs : r (γ s).2 = r₀) (j : ℤ) :
    HasDerivAt (fun s ↦ (γ s).1 - (r₀ + π / 2 + j * π))
      (-(2 * δ) * sin (2 * ((γ s).1 - (r₀ + π / 2 + j * π)))) s := by
  refine ((hasDerivAt_fst_of_hasDerivAt_circleContinuationField hγ s).sub_const _).congr_deriv ?_
  rw [hs, show 2 * ((γ s).1 - r₀) = 2 * ((γ s).1 - (r₀ + π / 2 + j * π)) + π + j * (2 * π) by
    ring, sin_add_int_mul_two_pi, sin_add_pi]
  ring

variable {a b r₀ r₁ c : ℝ}

/-- The time coordinate is monotone on the window `[a, b] ⊆ (0, 1)`. -/
private theorem intervalBaseTimeCoordinate_le (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    intervalBaseTimeCoordinate a ≤ intervalBaseTimeCoordinate b :=
  strictMonoOn_intervalBaseTimeCoordinate.monotoneOn ⟨ha, hab.trans_lt hb⟩
    ⟨ha.trans_le hab, hb⟩ hab

/-- **A trajectory into a target maximum arrives along the invariant line.** If the angle tends
to the maximum `r₁ + k π` of the target slice, then it equals `r₁ + k π` from the time `U b - c` on:
for `δ > 0` the maximum repels every other solution, and for `δ = 0` the angle is constant. -/
private theorem fst_eq_of_tendsto_atTop_int_mul_pi (hδ : 0 ≤ δ) (hb : b ∈ Ioo 0 1)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c)) {k : ℤ}
    (h : Tendsto (fun s ↦ (γ s).1) atTop (𝓝 (r₁ + k * π))) :
    (γ (intervalBaseTimeCoordinate b - c)).1 = r₁ + k * π := by
  have := eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul (by positivity)
    (fun s hs ↦ hasDerivAt_fst_sub_int_mul_pi hγ (apply_snd_eq_of_ge hc hb hr₁ hs) k)
    (by simpa using h.sub_const (r₁ + k * π)) self_mem_Ici
  simpa [sub_eq_zero] using this

/-- Conversely, an angle equal to the maximum `r₁ + k π` of the target slice at the time `U b - c`
stays there. -/
private theorem tendsto_atTop_of_fst_eq_int_mul_pi (hb : b ∈ Ioo 0 1)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c)) {k : ℤ}
    (h : (γ (intervalBaseTimeCoordinate b - c)).1 = r₁ + k * π) :
    Tendsto (fun s ↦ (γ s).1) atTop (𝓝 (r₁ + k * π)) := by
  have hz := eqOn_zero_of_hasDerivAt_sin_two_mul_of_eq_zero isPreconnected_Ici self_mem_Ici
    (fun s hs ↦ hasDerivAt_fst_sub_int_mul_pi hγ (apply_snd_eq_of_ge hc hb hr₁ hs) k)
    (by simp [h])
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (intervalBaseTimeCoordinate b - c)] with s hs
  have := hz hs
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact this.symm

/-- **The basin of a source maximum.** If the angle at the time `U a - c` is within `π / 2` of the
maximum `r₀ + j π` of the source slice, then it tends to `r₀ + j π` at `-∞`. The angle is read at
the later time `U b - c`, the drift `2 δ (U b - U a)` across the window being allowed for. -/
private theorem tendsto_atBot_int_mul_pi (hδ : 0 < δ) (ha : a ∈ Ioo 0 1)
    (hr₀ : ∀ t ≤ a, r t = r₀) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c))
    (hab : intervalBaseTimeCoordinate a ≤ intervalBaseTimeCoordinate b) {j : ℤ}
    (h : |(γ (intervalBaseTimeCoordinate b - c)).1 - (r₀ + j * π)| +
      2 * δ * (intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a) < π / 2) :
    Tendsto (fun s ↦ (γ s).1) atBot (𝓝 (r₀ + j * π)) := by
  have hdrift := abs_fst_sub_fst_le_of_hasDerivAt_circleContinuationField hγ
    (intervalBaseTimeCoordinate a - c) (intervalBaseTimeCoordinate b - c)
  rw [abs_of_pos hδ, show intervalBaseTimeCoordinate a - c - (intervalBaseTimeCoordinate b - c) =
    -(intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a) by ring, abs_neg,
    abs_of_nonneg (sub_nonneg.2 hab)] at hdrift
  have h₀ : |(γ (intervalBaseTimeCoordinate a - c)).1 - (r₀ + j * π)| < π / 2 :=
    (abs_sub_le _ (γ (intervalBaseTimeCoordinate b - c)).1 _).trans_lt (by linarith)
  have := tendsto_atBot_of_hasDerivAt_sin_two_mul (by positivity)
    (fun s hs ↦ hasDerivAt_fst_sub_int_mul_pi hγ (apply_snd_eq_of_le hc ha hr₀ hs) j) h₀
  simpa using this.add_const (r₀ + j * π)

/-- **A trajectory out of a source minimum leaves along the invariant line.** If the angle tends to
the minimum `r₀ + π / 2 + j π` of the source slice at `-∞`, then it equals `r₀ + π / 2 + j π` up to
the time `U a - c`: for `δ > 0` the minimum attracts every nearby solution in forward time, and for
`δ = 0` the angle is constant. -/
private theorem fst_eq_of_tendsto_atBot_pi_div_two (hδ : 0 ≤ δ) (ha : a ∈ Ioo 0 1)
    (hr₀ : ∀ t ≤ a, r t = r₀) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c)) {j : ℤ}
    (h : Tendsto (fun s ↦ (γ s).1) atBot (𝓝 (r₀ + π / 2 + j * π))) :
    (γ (intervalBaseTimeCoordinate a - c)).1 = r₀ + π / 2 + j * π := by
  have := eqOn_zero_of_tendsto_atBot_of_hasDerivAt_sin_two_mul (by linarith)
    (fun s hs ↦ hasDerivAt_fst_sub_pi_div_two hγ (apply_snd_eq_of_le hc ha hr₀ hs) j)
    (by simpa using h.sub_const (r₀ + π / 2 + j * π)) self_mem_Iic
  simpa [sub_eq_zero] using this

/-- Conversely, an angle equal to the minimum `r₀ + π / 2 + j π` of the source slice at the time
`U a - c` has been there since `-∞`. -/
private theorem tendsto_atBot_of_fst_eq_pi_div_two (ha : a ∈ Ioo 0 1)
    (hr₀ : ∀ t ≤ a, r t = r₀) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c)) {j : ℤ}
    (h : (γ (intervalBaseTimeCoordinate a - c)).1 = r₀ + π / 2 + j * π) :
    Tendsto (fun s ↦ (γ s).1) atBot (𝓝 (r₀ + π / 2 + j * π)) := by
  have hz := eqOn_zero_of_hasDerivAt_sin_two_mul_of_eq_zero isPreconnected_Iic self_mem_Iic
    (fun s hs ↦ hasDerivAt_fst_sub_pi_div_two hγ (apply_snd_eq_of_le hc ha hr₀ hs) j)
    (by simp [h])
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_le_atBot (intervalBaseTimeCoordinate a - c)] with s hs
  have := hz hs
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact this.symm

/-- **The basin of a target minimum.** If the angle at the time `U a - c` is within
`π / 2 - 2 δ (U b - U a)` of the minimum `r₁ + π / 2 + k π` of the target slice, then it tends to
`r₁ + π / 2 + k π` at `+∞`. -/
private theorem tendsto_atTop_pi_div_two (hδ : 0 < δ) (hb : b ∈ Ioo 0 1)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c))
    (hab : intervalBaseTimeCoordinate a ≤ intervalBaseTimeCoordinate b) {k : ℤ}
    (h : |(γ (intervalBaseTimeCoordinate a - c)).1 - (r₁ + π / 2 + k * π)| +
      2 * δ * (intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a) < π / 2) :
    Tendsto (fun s ↦ (γ s).1) atTop (𝓝 (r₁ + π / 2 + k * π)) := by
  have hdrift := abs_fst_sub_fst_le_of_hasDerivAt_circleContinuationField hγ
    (intervalBaseTimeCoordinate b - c) (intervalBaseTimeCoordinate a - c)
  rw [abs_of_pos hδ, show intervalBaseTimeCoordinate b - c - (intervalBaseTimeCoordinate a - c) =
    intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a by ring,
    abs_of_nonneg (sub_nonneg.2 hab)] at hdrift
  have h₀ : |(γ (intervalBaseTimeCoordinate b - c)).1 - (r₁ + π / 2 + k * π)| < π / 2 :=
    (abs_sub_le _ (γ (intervalBaseTimeCoordinate a - c)).1 _).trans_lt (by linarith)
  have := tendsto_atTop_of_hasDerivAt_sin_two_mul (by linarith)
    (fun s hs ↦ hasDerivAt_fst_sub_pi_div_two hγ (apply_snd_eq_of_ge hc hb hr₁ hs) k) h₀
  simpa using this.add_const (r₁ + π / 2 + k * π)

/-! ### The invariant lines -/

/-- **A trajectory into a target maximum arrives along the invariant line.** For `δ ≥ 0`, let the
path `r` be constant equal to `r₁` for `t ≥ b`. A trajectory from the source level `t = 0` into the
maximum `(r₁ + k π, 1)` of the target slice has angle `r₁ + k π` wherever its parameter is at least
`b`. -/
theorem fst_eq_of_mem_circleContinuationTrajectories_int_mul_pi (hδ : 0 ≤ δ)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) {k : ℤ} {x : ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ r (x, 0) (r₁ + k * π, 1)) {s : ℝ}
    (hs : b ≤ (γ s).2) : (γ s).1 = r₁ + k * π := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  have hs' : (γ s).2 ∈ Ioo 0 1 := by rw [hc]; exact intervalBaseOrbit_mem_Ioo 1 _
  have h := fst_eq_of_tendsto_atTop_int_mul_pi hδ hs' (fun t ht ↦ hr₁ t (hs.trans ht)) hγ.1 hc
    hγ.2.2.fst_nhds
  rwa [hc s, intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul, add_sub_cancel_right] at h

/-- **A trajectory out of a source minimum leaves along the invariant line.** For `δ ≥ 0`, let the
path `r` be constant equal to `r₀` for `t ≤ a`. A trajectory from the minimum
`(r₀ + π / 2 + j π, 0)` of the source slice to the target level `t = 1` has angle
`r₀ + π / 2 + j π` wherever its parameter is at most `a`. -/
theorem fst_eq_of_mem_circleContinuationTrajectories_pi_div_two (hδ : 0 ≤ δ)
    (hr₀ : ∀ t ≤ a, r t = r₀) {j : ℤ} {y : ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (y, 1)) {s : ℝ}
    (hs : (γ s).2 ≤ a) : (γ s).1 = r₀ + π / 2 + j * π := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  have hs' : (γ s).2 ∈ Ioo 0 1 := by rw [hc]; exact intervalBaseOrbit_mem_Ioo 1 _
  have h := fst_eq_of_tendsto_atBot_pi_div_two hδ hs' (fun t ht ↦ hr₀ t (ht.trans hs)) hγ.1 hc
    hγ.2.1.fst_nhds
  rwa [hc s, intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul, add_sub_cancel_right] at h

/-! ### The trajectories between maxima -/

/-- **At most one trajectory into a target maximum.** For `δ ≥ 0`, let the path `r` be constant
equal to `r₁` for `t ≥ b`, where `b < 1`. The maximum `(r₁ + k π, 1)` of the target slice repels in
the angle, so any two trajectories from the source level `t = 0` into it are time translates of
each other. -/
theorem exists_eq_comp_add_of_mem_circleContinuationTrajectories_int_mul_pi (hδ : 0 ≤ δ)
    (hb : b < 1) (hr₁ : ∀ t, b ≤ t → r t = r₁) {k : ℤ} {x x' : ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ r (x, 0) (r₁ + k * π, 1))
    (hγ' : γ' ∈ circleContinuationTrajectories δ r (x', 0) (r₁ + k * π, 1)) :
    ∃ c, γ' = fun s ↦ γ (s + c) := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  obtain ⟨c', hc'⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ'
  rw [mem_circleContinuationTrajectories] at hγ'
  -- Work on the window `t ≥ max b (1 / 2)`, which lies in the open slab.
  set b' := max b (1 / 2)
  have hb' : b' ∈ Ioo 0 1 := ⟨lt_max_of_lt_right (by norm_num), max_lt hb (by norm_num)⟩
  have hr₁' : ∀ t, b' ≤ t → r t = r₁ := fun t ht ↦ hr₁ t ((le_max_left _ _).trans ht)
  have h₁ := fst_eq_of_tendsto_atTop_int_mul_pi hδ hb' hr₁' hγ.1 hc hγ.2.2.fst_nhds
  have h₂ := fst_eq_of_tendsto_atTop_int_mul_pi hδ hb' hr₁' hγ'.1 hc' hγ'.2.2.fst_nhds
  have hτ : ∀ c'', intervalBaseOrbit 1 (intervalBaseTimeCoordinate b' - c'' + c'') = b' :=
    fun _ ↦ by rw [sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate hb']
  exact ⟨_, eq_comp_add_of_hasDerivAt_circleContinuationField hγ.1 hγ'.1
    (Prod.ext (h₂.trans h₁.symm) (by rw [hc, hc', hτ, hτ]))⟩

/-- **The source of a trajectory into a target maximum.** For `δ > 0`, let the path `r` be `r₀`
for `t ≤ a` and `r₁` for `t ≥ b`, where `0 < a ≤ b < 1`, and let the target maximum `r₁ + k π` be
within `π / 2 - 2 δ T` of the source maximum `r₀ + j π`, where `T = ∫_a^b (t (1 - t²))⁻¹ dt` is the
flow time across the window `[a, b]`. Then every trajectory from the source level `t = 0` to the
target maximum `(r₁ + k π, 1)` starts at the source maximum `(r₀ + j π, 0)`. -/
theorem eq_of_mem_circleContinuationTrajectories_int_mul_pi (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {j k : ℤ} (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    {x : ℝ} (hγ : γ ∈ circleContinuationTrajectories δ r (x, 0) (r₁ + k * π, 1)) :
    x = r₀ + j * π := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  have h₁ := fst_eq_of_tendsto_atTop_int_mul_pi hδ.le ⟨ha.trans_le hab, hb⟩ hr₁ hγ.1 hc
    hγ.2.2.fst_nhds
  rw [integral_inv_mul_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩, ← h₁] at hjk
  exact tendsto_nhds_unique hγ.2.1.fst_nhds (tendsto_atBot_int_mul_pi hδ ⟨ha, hab.trans_lt hb⟩
    hr₀ hγ.1 hc (intervalBaseTimeCoordinate_le ha hab hb) hjk)

/-- **A trajectory between maxima.** Under the hypotheses of
`TauCeti.eq_of_mem_circleContinuationTrajectories_int_mul_pi`, with the path `r` Lipschitz, there
is a trajectory from the source maximum `(r₀ + j π, 0)` to the target maximum `(r₁ + k π, 1)`. -/
theorem nonempty_circleContinuationTrajectories_int_mul_pi (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {L : ℝ≥0} (hr : LipschitzWith L r) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    (circleContinuationTrajectories δ r (r₀ + j * π, 0) (r₁ + k * π, 1)).Nonempty := by
  obtain ⟨γ, hγ, hsnd, hfst⟩ :=
    exists_circleContinuationField_fst_eq (δ := δ) hr (intervalBaseTimeCoordinate b) (r₁ + k * π)
  have hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + 0) := fun s ↦ by rw [add_zero, hsnd]
  have hq : (fun s ↦ (γ s).2) = intervalBaseOrbit 1 := funext hsnd
  rw [integral_inv_mul_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩] at hjk
  refine ⟨γ, mem_circleContinuationTrajectories.2 ⟨hγ, ?_, ?_⟩⟩
  · refine (tendsto_atBot_int_mul_pi hδ ⟨ha, hab.trans_lt hb⟩ hr₀ hγ hc
      (intervalBaseTimeCoordinate_le ha hab hb) (by rwa [sub_zero, hfst])).prodMk_nhds ?_
    rw [hq]
    exact tendsto_intervalBaseOrbit_atBot one_pos
  · refine (tendsto_atTop_of_fst_eq_int_mul_pi ⟨ha.trans_le hab, hb⟩ hr₁ hγ hc
      (by rwa [sub_zero])).prodMk_nhds ?_
    rw [hq]
    exact tendsto_intervalBaseOrbit_atTop one_pos

/-- **Exactly one trajectory between maxima.** Under the hypotheses of
`TauCeti.nonempty_circleContinuationTrajectories_int_mul_pi`, the trajectories from the source
maximum `(r₀ + j π, 0)` to the target maximum `(r₁ + k π, 1)` are the time translates of a single
one. So the continuation counts one unparametrized trajectory from `r₀ + j π` to `r₁ + k π`, and
none into `r₁ + k π` from any other source
(`TauCeti.eq_of_mem_circleContinuationTrajectories_int_mul_pi`). -/
theorem exists_circleContinuationTrajectories_int_mul_pi_eq_range (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {L : ℝ≥0} (hr : LipschitzWith L r) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    ∃ γ : ℝ → ℝ × ℝ, circleContinuationTrajectories δ r (r₀ + j * π, 0) (r₁ + k * π, 1) =
      range fun c s ↦ γ (s + c) := by
  obtain ⟨γ, hγ⟩ := nonempty_circleContinuationTrajectories_int_mul_pi hδ ha hab hb hr₀ hr₁ hr hjk
  refine ⟨γ, Subset.antisymm (fun γ' hγ' ↦ ?_) ?_⟩
  · obtain ⟨c, hc⟩ := exists_eq_comp_add_of_mem_circleContinuationTrajectories_int_mul_pi hδ.le
      hb hr₁ hγ hγ'
    exact ⟨c, hc.symm⟩
  · rintro _ ⟨c, rfl⟩
    exact comp_add_mem_circleContinuationTrajectories hγ c

/-! ### The trajectories between minima -/

/-- **At most one trajectory out of a source minimum.** For `δ ≥ 0`, let the path `r` be constant
equal to `r₀` for `t ≤ a`, where `0 < a`. The minimum `(r₀ + π / 2 + j π, 0)` of the source slice
attracts in the angle, so any two trajectories from it to the target level `t = 1` are time
translates of each other. -/
theorem exists_eq_comp_add_of_mem_circleContinuationTrajectories_pi_div_two (hδ : 0 ≤ δ)
    (ha : 0 < a) (hr₀ : ∀ t ≤ a, r t = r₀) {j : ℤ} {y y' : ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (y, 1))
    (hγ' : γ' ∈ circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (y', 1)) :
    ∃ c, γ' = fun s ↦ γ (s + c) := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  obtain ⟨c', hc'⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ'
  rw [mem_circleContinuationTrajectories] at hγ'
  -- Work on the window `t ≤ min a (1 / 2)`, whose upper end lies in the open slab.
  set a' := min a (1 / 2)
  have ha' : a' ∈ Ioo 0 1 := ⟨lt_min ha (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  have hr₀' : ∀ t ≤ a', r t = r₀ := fun t ht ↦ hr₀ t (ht.trans (min_le_left _ _))
  have h₁ := fst_eq_of_tendsto_atBot_pi_div_two hδ ha' hr₀' hγ.1 hc hγ.2.1.fst_nhds
  have h₂ := fst_eq_of_tendsto_atBot_pi_div_two hδ ha' hr₀' hγ'.1 hc' hγ'.2.1.fst_nhds
  have hτ : ∀ c'', intervalBaseOrbit 1 (intervalBaseTimeCoordinate a' - c'' + c'') = a' :=
    fun _ ↦ by rw [sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate ha']
  exact ⟨_, eq_comp_add_of_hasDerivAt_circleContinuationField hγ.1 hγ'.1
    (Prod.ext (h₂.trans h₁.symm) (by rw [hc, hc', hτ, hτ]))⟩

/-- **The target of a trajectory out of a source minimum.** For `δ > 0`, let the path `r` be `r₀`
for `t ≤ a` and `r₁` for `t ≥ b`, where `0 < a ≤ b < 1`, and let `r₁ + k π` be within
`π / 2 - 2 δ T` of `r₀ + j π`, where `T = ∫_a^b (t (1 - t²))⁻¹ dt`. Then every trajectory from the
source minimum `(r₀ + π / 2 + j π, 0)` to the target level `t = 1` ends at the target minimum
`(r₁ + π / 2 + k π, 1)`. -/
theorem eq_of_mem_circleContinuationTrajectories_pi_div_two (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {j k : ℤ} (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    {y : ℝ} (hγ : γ ∈ circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (y, 1)) :
    y = r₁ + π / 2 + k * π := by
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  have h₁ := fst_eq_of_tendsto_atBot_pi_div_two hδ.le ⟨ha, hab.trans_lt hb⟩ hr₀ hγ.1 hc
    hγ.2.1.fst_nhds
  rw [integral_inv_mul_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩] at hjk
  refine tendsto_nhds_unique hγ.2.2.fst_nhds (tendsto_atTop_pi_div_two hδ ⟨ha.trans_le hab, hb⟩
    hr₁ hγ.1 hc (intervalBaseTimeCoordinate_le ha hab hb) ?_)
  rwa [h₁, abs_sub_comm, show r₁ + π / 2 + k * π - (r₀ + π / 2 + j * π) =
    r₁ + k * π - (r₀ + j * π) by ring]

/-- **A trajectory between minima.** Under the hypotheses of
`TauCeti.eq_of_mem_circleContinuationTrajectories_pi_div_two`, with the path `r` Lipschitz, there is
a trajectory from the source minimum `(r₀ + π / 2 + j π, 0)` to the target minimum
`(r₁ + π / 2 + k π, 1)`. -/
theorem nonempty_circleContinuationTrajectories_pi_div_two (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {L : ℝ≥0} (hr : LipschitzWith L r) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    (circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0)
      (r₁ + π / 2 + k * π, 1)).Nonempty := by
  obtain ⟨γ, hγ, hsnd, hfst⟩ := exists_circleContinuationField_fst_eq (δ := δ) hr
    (intervalBaseTimeCoordinate a) (r₀ + π / 2 + j * π)
  have hc : ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + 0) := fun s ↦ by rw [add_zero, hsnd]
  have hq : (fun s ↦ (γ s).2) = intervalBaseOrbit 1 := funext hsnd
  rw [integral_inv_mul_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩] at hjk
  refine ⟨γ, mem_circleContinuationTrajectories.2 ⟨hγ, ?_, ?_⟩⟩
  · refine (tendsto_atBot_of_fst_eq_pi_div_two ⟨ha, hab.trans_lt hb⟩ hr₀ hγ hc
      (by rwa [sub_zero])).prodMk_nhds ?_
    rw [hq]
    exact tendsto_intervalBaseOrbit_atBot one_pos
  · refine (tendsto_atTop_pi_div_two hδ ⟨ha.trans_le hab, hb⟩ hr₁ hγ hc
      (intervalBaseTimeCoordinate_le ha hab hb) ?_).prodMk_nhds ?_
    · rwa [sub_zero, hfst, abs_sub_comm, show r₁ + π / 2 + k * π - (r₀ + π / 2 + j * π) =
        r₁ + k * π - (r₀ + j * π) by ring]
    rw [hq]
    exact tendsto_intervalBaseOrbit_atTop one_pos

/-- **Exactly one trajectory between minima.** Under the hypotheses of
`TauCeti.nonempty_circleContinuationTrajectories_pi_div_two`, the trajectories from the source
minimum `(r₀ + π / 2 + j π, 0)` to the target minimum `(r₁ + π / 2 + k π, 1)` are the time
translates of a single one, and there are none from that source to any other point of the target
level (`TauCeti.eq_of_mem_circleContinuationTrajectories_pi_div_two`). -/
theorem exists_circleContinuationTrajectories_pi_div_two_eq_range (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {L : ℝ≥0} (hr : LipschitzWith L r) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    ∃ γ : ℝ → ℝ × ℝ,
      circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (r₁ + π / 2 + k * π, 1) =
        range fun c s ↦ γ (s + c) := by
  obtain ⟨γ, hγ⟩ :=
    nonempty_circleContinuationTrajectories_pi_div_two hδ ha hab hb hr₀ hr₁ hr hjk
  refine ⟨γ, Subset.antisymm (fun γ' hγ' ↦ ?_) ?_⟩
  · obtain ⟨c, hc⟩ := exists_eq_comp_add_of_mem_circleContinuationTrajectories_pi_div_two hδ.le
      ha hr₀ hγ hγ'
    exact ⟨c, hc.symm⟩
  · rintro _ ⟨c, rfl⟩
    exact comp_add_mem_circleContinuationTrajectories hγ c

/-- **No trajectory from a source minimum to a target maximum when the drift is small.** For
`δ ≥ 0`, let the path `r` be `r₀` for `t ≤ a` and `r₁` for `t ≥ b`, where `0 < a ≤ b < 1`. If the
drift `2 δ T` across the window, with `T = ∫_a^b (t (1 - t²))⁻¹ dt`, is less than the distance from
the source minimum `r₀ + π / 2 + j π` to the target maximum `r₁ + m π`, there is no trajectory
between them: the trajectory out of the minimum leaves along the angle `r₀ + π / 2 + j π`, and a
trajectory into the maximum arrives along the angle `r₁ + m π`. -/
theorem circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty_of_lt (hδ : 0 ≤ δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) {j m : ℤ}
    (hjm : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < |r₁ + m * π - (r₀ + π / 2 + j * π)|) :
    circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (r₁ + m * π, 1) = ∅ := by
  refine eq_empty_of_forall_notMem fun γ hγ ↦ ?_
  obtain ⟨c, hc⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ
  rw [mem_circleContinuationTrajectories] at hγ
  have h₀ := fst_eq_of_tendsto_atBot_pi_div_two hδ ⟨ha, hab.trans_lt hb⟩ hr₀ hγ.1 hc
    hγ.2.1.fst_nhds
  have h₁ := fst_eq_of_tendsto_atTop_int_mul_pi hδ ⟨ha.trans_le hab, hb⟩ hr₁ hγ.1 hc
    hγ.2.2.fst_nhds
  have hdrift := abs_fst_sub_fst_le_of_hasDerivAt_circleContinuationField hγ.1
    (intervalBaseTimeCoordinate b - c) (intervalBaseTimeCoordinate a - c)
  rw [h₀, h₁, abs_of_nonneg hδ, show intervalBaseTimeCoordinate b - c -
    (intervalBaseTimeCoordinate a - c) = intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a
    by ring, abs_of_nonneg (sub_nonneg.2 (intervalBaseTimeCoordinate_le ha hab hb))] at hdrift
  rw [integral_inv_mul_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩] at hjm
  linarith

/-- **No trajectory from a source minimum to a target maximum.** For `δ ≥ 0`, let the path `r` be
`r₀` for `t ≤ a` and `r₁` for `t ≥ b`, where `0 < a ≤ b < 1`, and let
`|r₁ + k π - (r₀ + j π)| + 2 δ T < π / 2`, where `T = ∫_a^b (t (1 - t²))⁻¹ dt`. Then there is no
trajectory from the source minimum `(r₀ + π / 2 + j π, 0)`, of index one, to any target maximum
`(r₁ + m π, 1)`, also of index one. Such a connection would have expected dimension `-1`, so its
absence is part of the transversality of the parameter field. -/
theorem circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty (hδ : 0 ≤ δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {j k : ℤ} (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (m : ℤ) :
    circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (r₁ + m * π, 1) = ∅ := by
  refine circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty_of_lt hδ ha hab hb hr₀ hr₁ ?_
  -- The angle `(m - k) π - π / 2` between a maximum and a minimum is at least `π / 2`.
  have hn : π / 2 ≤ |((m - k : ℤ) : ℝ) * π - π / 2| := by
    rcases le_or_gt (m - k) 0 with h | h
    · have : ((m - k : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith [pi_pos])]
      nlinarith [pi_pos]
    · have : (1 : ℝ) ≤ ((m - k : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m - k)
      rw [abs_of_nonneg (by nlinarith [pi_pos])]
      nlinarith [pi_pos]
  have h := abs_sub_abs_le_abs_sub (((m - k : ℤ) : ℝ) * π - π / 2) (-(r₁ + k * π - (r₀ + j * π)))
  rw [abs_neg, sub_neg_eq_add, show ((m - k : ℤ) : ℝ) * π - π / 2 + (r₁ + k * π - (r₀ + j * π)) =
    r₁ + m * π - (r₀ + π / 2 + j * π) by push_cast; ring] at h
  linarith

end Trajectory

/-! ### The half-turn: trajectories join equal lifted angles -/

section HalfTurn

variable {δ a b : ℝ} {ρ : ℝ → ℝ} {L : ℝ≥0}

/-- With the source label `j = k` and the target label `k - 1`, the two maxima of the half-turn are
the same lifted angle `k π`, and the window condition reduces to the drift bound. -/
private theorem pi_mul_hjk (k : ℤ) (hT : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    |π + ((k - 1 : ℤ) : ℝ) * π - (0 + k * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ <
      π / 2 := by
  rwa [show π + ((k - 1 : ℤ) : ℝ) * π - (0 + k * π) = 0 by push_cast; ring, abs_zero, zero_add]

/-- **The half-turn trajectories between maxima.** Let `ρ` be Lipschitz, `0` for `t ≤ a` and `1`
for `t ≥ b`, where `0 < a ≤ b < 1`, so that the half-turn path `π ρ` goes from `δ cos (2 θ)` to the
same function `δ cos (2 (θ - π))`, and let `δ > 0` satisfy `2 δ T < π / 2` with
`T = ∫_a^b (t (1 - t²))⁻¹ dt`. Then the trajectories from the maximum `(k π, 0)` to the maximum
`(k π, 1)` at the same lifted angle are the time translates of a single one, and no trajectory
from any other point of the source level ends at `(k π, 1)`
(`TauCeti.eq_of_mem_circleContinuationTrajectories_pi_mul_int_mul_pi`). Following the maximum
`k π` of `δ cos (2 (θ - π ρ(t)))` along `t` instead ends at `k π + π`, the other maximum. -/
theorem exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (h0 : ∀ t ≤ a, ρ t = 0) (h1 : ∀ t, b ≤ t → ρ t = 1)
    (hρ : LipschitzWith L ρ) (hT : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) (k : ℤ) :
    ∃ γ : ℝ → ℝ × ℝ, circleContinuationTrajectories δ (fun t ↦ π * ρ t) (k * π, 0) (k * π, 1) =
      range fun c s ↦ γ (s + c) := by
  have h := exists_circleContinuationTrajectories_int_mul_pi_eq_range (r := fun t ↦ π * ρ t) hδ
    ha hab hb (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one])
    ((lipschitzWith_smul π).comp hρ) (pi_mul_hjk k hT)
  rwa [show π + ((k - 1 : ℤ) : ℝ) * π = k * π by push_cast; ring, zero_add] at h

/-- For the half-turn continuation, every trajectory from the source level into the maximum
`(k π, 1)` starts at the maximum `(k π, 0)` at the same lifted angle. -/
theorem eq_of_mem_circleContinuationTrajectories_pi_mul_int_mul_pi (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (h0 : ∀ t ≤ a, ρ t = 0) (h1 : ∀ t, b ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) {k : ℤ} {x : ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ (fun t ↦ π * ρ t) (x, 0) (k * π, 1)) :
    x = k * π := by
  rw [show k * π = π + ((k - 1 : ℤ) : ℝ) * π by push_cast; ring] at hγ
  have := eq_of_mem_circleContinuationTrajectories_int_mul_pi hδ ha hab hb
    (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one]) (pi_mul_hjk k hT)
    hγ
  rw [this, zero_add]

/-- **The half-turn trajectories between minima.** Under the hypotheses of
`TauCeti.exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range`, the trajectories from
the minimum `(π / 2 + k π, 0)` to the minimum `(π / 2 + k π, 1)` at the same lifted angle are the
time translates of a single one, and no trajectory from `(π / 2 + k π, 0)` ends at any other point
of the target level (`TauCeti.eq_of_mem_circleContinuationTrajectories_pi_mul_pi_div_two`).
Following the minimum along the path instead ends at the other minimum `π / 2 + k π + π`. -/
theorem exists_circleContinuationTrajectories_pi_mul_pi_div_two_eq_range (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (h0 : ∀ t ≤ a, ρ t = 0) (h1 : ∀ t, b ≤ t → ρ t = 1)
    (hρ : LipschitzWith L ρ) (hT : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) (k : ℤ) :
    ∃ γ : ℝ → ℝ × ℝ, circleContinuationTrajectories δ (fun t ↦ π * ρ t) (π / 2 + k * π, 0)
      (π / 2 + k * π, 1) = range fun c s ↦ γ (s + c) := by
  have h := exists_circleContinuationTrajectories_pi_div_two_eq_range (r := fun t ↦ π * ρ t) hδ
    ha hab hb (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one])
    ((lipschitzWith_smul π).comp hρ) (pi_mul_hjk k hT)
  rwa [show π + π / 2 + ((k - 1 : ℤ) : ℝ) * π = π / 2 + k * π by push_cast; ring,
    zero_add] at h

/-- For the half-turn continuation, every trajectory from the minimum `(π / 2 + k π, 0)` to the
target level ends at the minimum `(π / 2 + k π, 1)` at the same lifted angle; in particular it
does not end at a maximum. -/
theorem eq_of_mem_circleContinuationTrajectories_pi_mul_pi_div_two (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (h0 : ∀ t ≤ a, ρ t = 0) (h1 : ∀ t, b ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) {k : ℤ} {y : ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ (fun t ↦ π * ρ t) (π / 2 + k * π, 0) (y, 1)) :
    y = π / 2 + k * π := by
  rw [show π / 2 + k * π = 0 + π / 2 + k * π by ring] at hγ
  have := eq_of_mem_circleContinuationTrajectories_pi_div_two hδ ha hab hb
    (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one]) (pi_mul_hjk k hT)
    hγ
  rw [this]
  push_cast
  ring

end HalfTurn

end TauCeti
