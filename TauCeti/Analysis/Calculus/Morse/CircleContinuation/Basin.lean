/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
public import TauCeti.Analysis.Calculus.Morse.IntervalBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The index-preserving trajectories of the circle continuation, by basins

The continuation of `δ cos (2 (θ - r))` on the circle along a path `t ↦ r t` counts trajectories of
the parameter field `TauCeti.circleContinuationField` between its zeros at `t = 0` and `t = 1`.
In the open slab `0 < t < 1` these trajectories are the graphs of the solutions of
`Θ' = circleContinuationSlope δ r t (Θ t)` (`TauCeti.hasDerivAt_circleContinuationField`). This
file classifies the ones that preserve the Morse index of the end functions, for `δ > 0` and a path
that is constant near the two ends: `r = r₀` on `(0, a]` and `r = r₁` on `[b, 1)`, with
`0 < a ≤ b < 1`. The zeros of the field at `t = 0` are the maxima `r₀ + j π` and the minima
`r₀ + π / 2 + j π` of the source function, of index `2` and `1` for the field; at `t = 1` they are
the maxima `r₁ + k π` and the minima `r₁ + π / 2 + k π` of the target function, of index `1` and
`0`. The trajectories preserving the Morse index of the end functions run from a source minimum to a
target minimum, or from a source maximum to a target maximum; along them the index for the field
drops by one.

**The end windows.** While the path is constant, the time coordinate
`U(t) = log t - (1 / 2) log (1 - t²)` of the base flow (`TauCeti.intervalBaseTimeCoordinate`)
turns the equation into the negative gradient flow of `δ cos (2 (θ - r₀))` on the line of lifted
angles, which is solved explicitly: near a zero `c` of the slope,
`tan (Θ t - c) = tan (Θ s - c) e^{± 4 δ (U t - U s)}`. Since `U` tends to `-∞` at `0` and to `+∞`
at `1`, this gives the four end behaviours.

* The only solution tending at `0` to a source minimum is constant on `(0, a]`
  (`TauCeti.eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope`), and the only
  one tending at `1` to a target maximum is constant on `[b, 1)`
  (`TauCeti.eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope`).
* A solution within `π / 2` of a target minimum at time `b` tends to it at `1`
  (`TauCeti.tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope`), and one within
  `π / 2` of a source maximum at time `a` tends to it at `0`
  (`TauCeti.tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope`).

These four statements only use the equation on the end interval, with one-sided derivatives at its
inner endpoint.

**Classification.** Solutions on windows `[a, b] ⊆ (0, 1)` are unique
(`TauCeti.eqOn_of_hasDerivWithinAt_circleContinuationSlope`), and exist through every point when
the path is continuous on the window
(`TauCeti.exists_eq_forall_mem_Icc_hasDerivWithinAt_circleContinuationSlope`); the explicit
solutions on the ends extend them to solutions on all of `(0, 1)`
(`TauCeti.exists_hasDerivAt_circleContinuationSlope`). Across the window
`[a, b]` the angle moves by at most
`D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt`
(`TauCeti.abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope`). So if
`|r₀ + j π - (r₁ + k π)| + D < π / 2`, the trajectory leaving the source minimum `r₀ + π / 2 + j π`
ends at the target minimum `r₁ + π / 2 + k π`
(`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`), and the
trajectory arriving at the target maximum `r₁ + k π` starts at the source maximum `r₀ + j π`
(`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`). Each of
these trajectories is unique, and exists when the path is continuous on `[a, b]`. So there is
exactly one trajectory from that source minimum to that target minimum and none from it to any other
target minimum, and exactly one trajectory to that target maximum from that source maximum and none
to it from any other source maximum. A source minimum is joined to no target maximum more than `D`
away from it
(`TauCeti.not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`),
since the trajectory would be constant on both ends: both are zeros of index `1` for the field, and
such a connection is the failure of transversality exhibited by
`TauCeti.exists_circleContinuationField_connection` for large `δ`. Under the condition above on
`j` and `k`, every target maximum is more than `D` away from the source minimum
`r₀ + π / 2 + j π`, so that minimum is joined to no target maximum at all.

For the circle continuation counterexamples, take `a = 1/6` and `b = 5/6`, and `δ` small enough
that `D < π / 12`. For the half-turn `r₁ = r₀ + π`, the trajectory from `r₀ + π / 2 + j π` ends at
`r₁ + π / 2 + (j - 1) π`, the same point of the circle: in fixed spatial bases the unsigned
trajectory counts between the minima form the identity matrix, while tracking the critical points
along the path exchanges the two minima, and likewise the two maxima. For a rotation by `π / 3` it
ends at `r₁ + π / 2 + j π`, the tracked minimum, while for the rotation by `2 π / 3` concatenating
two of them it ends at `r₁ + π / 2 + (j - 1) π`: for each rotation by `π / 3` the unsigned counts
match the tracked labels identically, but for their concatenation they exchange them. Orientations,
signs and the continuation chain map itself are not treated here.

## Main results

* `TauCeti.eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope`,
  `TauCeti.eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope`: the ends of the
  trajectories.
* `TauCeti.exists_hasDerivAt_circleContinuationSlope`: a trajectory through every point of the
  window.
* `TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`: the
  classification by basins.
* `TauCeti.not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`: no
  source minimum is joined to a target maximum farther than the drift bound.
* `TauCeti.eqOn_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.eqOn_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.exists_hasDerivAt_circleContinuationSlope_tendsto_add_pi_div_two`,
  `TauCeti.exists_hasDerivAt_circleContinuationSlope_tendsto_add_int_mul_pi`: uniqueness and
  existence of the index-preserving trajectories.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology

namespace TauCeti

/-! ### Explicit trajectories while the path is constant -/

/-- The trajectory `c + arctan (tan (θ - c) e^{4 κ (U t - U s)})`, where `U` is the time coordinate
of the base flow. It solves `Θ' = 2 κ sin (2 (Θ - c)) / (t (1 - t²))` on `(0, 1)` and passes
through `θ` at time `s` when `|θ - c| < π / 2`. -/
private noncomputable def endTrajectory (κ c s θ t : ℝ) : ℝ :=
  c + arctan (tan (θ - c) *
    exp (4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s)))

private theorem endTrajectory_self {κ c s θ : ℝ} (h : |θ - c| < π / 2) :
    endTrajectory κ c s θ s = θ := by
  simp [endTrajectory, arctan_tan (neg_lt_of_abs_lt h) (lt_of_abs_lt h)]

private theorem hasDerivAt_endTrajectory (κ c s θ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (endTrajectory κ c s θ)
      (2 * κ * sin (2 * (endTrajectory κ c s θ t - c)) / (t * (1 - t ^ 2))) t := by
  have hm : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
  have hg := ((((hasDerivAt_intervalBaseTimeCoordinate ht).sub_const
    (intervalBaseTimeCoordinate s)).const_mul (4 * κ)).exp).const_mul (tan (θ - c))
  convert (hg.arctan).const_add c using 1
  · funext τ
    simp only [endTrajectory]
  · simp only [endTrajectory]
    rw [← mul_assoc (tan (θ - c))]
    set x := tan (θ - c) *
      exp (4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))
    have hx : 0 < 1 + x ^ 2 := by positivity
    have hsc : x / √(1 + x ^ 2) * (1 / √(1 + x ^ 2)) = x / (1 + x ^ 2) := by
      rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt hx.le]
    rw [add_sub_cancel_left, sin_two_mul, sin_arctan, cos_arctan,
      mul_assoc (2 : ℝ) (x / √(1 + x ^ 2)), hsc]
    field_simp [hm.ne']
    ring

/-- Near a critical point `c` of `δ cos (2 (θ - r₀))`, a zero of `sin (2 (c - r₀))`, the slope is
`2 κ sin (2 (θ - c)) / (t (1 - t²))` with `κ = δ cos (2 (c - r₀)) = ± δ`. -/
private theorem circleContinuationSlope_eq_of_sin_eq_zero {δ r₀ c t θ : ℝ} {r : ℝ → ℝ}
    (hr : r t = r₀) (hc : sin (2 * (c - r₀)) = 0) :
    circleContinuationSlope δ r t θ =
      2 * (δ * cos (2 * (c - r₀))) * sin (2 * (θ - c)) / (t * (1 - t ^ 2)) := by
  rw [circleContinuationSlope_def, hr, show 2 * (θ - r₀) = 2 * (θ - c) + 2 * (c - r₀) by ring,
    sin_add, hc, mul_zero, add_zero]
  ring

/-- The points `r + n π / 2` are the critical points of `cos (2 (θ - r))`. -/
private theorem sin_two_mul_add_pi_div_two_mul_int_sub (r : ℝ) (n : ℤ) :
    sin (2 * (r + π / 2 * n - r)) = 0 := by
  rw [show 2 * (r + π / 2 * n - r) = n * π by ring]
  exact sin_int_mul_pi n

/-- The maxima `r + j π` of `cos (2 (θ - r))` are critical points. -/
private theorem sin_two_mul_add_int_mul_pi_sub (r : ℝ) (j : ℤ) : sin (2 * (r + j * π - r)) = 0 := by
  convert sin_two_mul_add_pi_div_two_mul_int_sub r (2 * j) using 2
  push_cast
  ring

/-- The minima `r + π / 2 + j π` of `cos (2 (θ - r))` are critical points. -/
private theorem sin_two_mul_add_pi_div_two_add_int_mul_pi_sub (r : ℝ) (j : ℤ) :
    sin (2 * (r + π / 2 + j * π - r)) = 0 := by
  convert sin_two_mul_add_pi_div_two_mul_int_sub r (2 * j + 1) using 2
  push_cast
  ring

/-- On an interval `[s, u] ⊆ (0, 1)` where the path is constant, `r = r₀`, a solution taking the
value of a critical point `c` of `δ cos (2 (θ - r₀))` at one parameter is constantly `c`. -/
private theorem eqOn_const_of_hasDerivWithinAt_circleContinuationSlope {δ r₀ c s u t₁ : ℝ}
    {r Θ : ℝ → ℝ} (hs : 0 < s) (hu : u < 1) (ht₁ : t₁ ∈ Icc s u) (hr : ∀ t ∈ Icc s u, r t = r₀)
    (hc : sin (2 * (c - r₀)) = 0)
    (hΘ : ∀ t ∈ Icc s u, HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Icc s u) t)
    (hΘc : Θ t₁ = c) : EqOn Θ (fun _ ↦ c) (Icc s u) :=
  eqOn_of_hasDerivWithinAt_circleContinuationSlope hs hu hΘ
    (fun t ht ↦
      (hasDerivAt_const_circleContinuationSlope (by rw [hr t ht]; exact hc)).hasDerivWithinAt)
    ht₁ hΘc

/-- Near a maximum `c = r₀ + j π` of `δ cos (2 (θ - r₀))` the slope is
`2 δ sin (2 (θ - c)) / (t (1 - t²))`. -/
private theorem circleContinuationSlope_eq_of_add_int_mul_pi {δ r₀ t θ : ℝ} {r : ℝ → ℝ}
    (hr : r t = r₀) (j : ℤ) :
    circleContinuationSlope δ r t θ =
      2 * δ * sin (2 * (θ - (r₀ + j * π))) / (t * (1 - t ^ 2)) := by
  have h : 2 * (r₀ + j * π - r₀) = j * (2 * π) := by ring
  rw [circleContinuationSlope_eq_of_sin_eq_zero hr (sin_two_mul_add_int_mul_pi_sub r₀ j), h,
    cos_int_mul_two_pi, mul_one]

/-- Near a minimum `c = r₀ + π / 2 + j π` of `δ cos (2 (θ - r₀))` the slope is
`2 (-δ) sin (2 (θ - c)) / (t (1 - t²))`. -/
private theorem circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi {δ r₀ t θ : ℝ}
    {r : ℝ → ℝ} (hr : r t = r₀) (j : ℤ) :
    circleContinuationSlope δ r t θ =
      2 * (-δ) * sin (2 * (θ - (r₀ + π / 2 + j * π))) / (t * (1 - t ^ 2)) := by
  have h : 2 * (r₀ + π / 2 + j * π - r₀) = j * (2 * π) + π := by ring
  rw [circleContinuationSlope_eq_of_sin_eq_zero hr
    (sin_two_mul_add_pi_div_two_add_int_mul_pi_sub r₀ j), h, cos_add_pi, cos_int_mul_two_pi,
    mul_neg_one]

/-- Through every angle `v` at every parameter `s` passes an explicit solution on `(0, 1)` of the
equation for a path which is `r₀` wherever the solution is used: the explicit trajectory around the
critical point of `δ cos (2 (θ - r₀))` nearest to `v`, which is within `π / 4` of `v`. -/
private theorem exists_endTrajectory {δ r₀ : ℝ} {r : ℝ → ℝ} (v s : ℝ) :
    ∃ E : ℝ → ℝ, E s = v ∧
      ∀ t ∈ Ioo 0 1, r t = r₀ → HasDerivAt E (circleContinuationSlope δ r t (E t)) t := by
  set n := round ((v - r₀) / (π / 2))
  set c := r₀ + π / 2 * n
  have hπ : 0 < π / 2 := by positivity
  have hc : sin (2 * (c - r₀)) = 0 := sin_two_mul_add_pi_div_two_mul_int_sub r₀ n
  have hv : |v - c| < π / 2 := by
    have h : |(v - r₀) / (π / 2) - n| ≤ 1 / 2 := abs_sub_round _
    rw [show v - c = π / 2 * ((v - r₀) / (π / 2) - n) by simp only [c]; field_simp; ring, abs_mul,
      abs_of_pos hπ]
    linarith [mul_le_mul_of_nonneg_left h hπ.le]
  refine ⟨endTrajectory (δ * cos (2 * (c - r₀))) c s v, endTrajectory_self hv, fun t ht hrt ↦ ?_⟩
  rw [circleContinuationSlope_eq_of_sin_eq_zero hrt hc]
  exact hasDerivAt_endTrajectory _ _ _ _ ht

/-- The explicit trajectory tends to `c` along a filter on which `4 κ (U t - U s) → -∞`. -/
private theorem tendsto_endTrajectory {l : Filter ℝ} {κ c s θ : ℝ}
    (h : Tendsto (fun t ↦ 4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))
      l atBot) :
    Tendsto (endTrajectory κ c s θ) l (𝓝 c) := by
  have h₀ : Tendsto (fun t ↦ tan (θ - c) *
      exp (4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))) l (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp h).const_mul (tan (θ - c))
  have h₁ := ((continuous_arctan.tendsto 0).comp h₀).const_add c
  rw [arctan_zero, add_zero] at h₁
  exact h₁

/-- Off its centre, the explicit trajectory stays at distance at least `π / 4` from `c` along a
filter on which `4 κ (U t - U s) → +∞`. -/
private theorem eventually_pi_div_four_le_abs_endTrajectory_sub {l : Filter ℝ} {κ c s θ : ℝ}
    (hθ : θ ≠ c) (hθc : |θ - c| < π / 2)
    (h : Tendsto (fun t ↦ 4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))
      l atTop) :
    ∀ᶠ t in l, π / 4 ≤ |endTrajectory κ c s θ t - c| := by
  have hA : tan (θ - c) ≠ 0 := by
    intro h0
    have := arctan_tan (neg_lt_of_abs_lt hθc) (lt_of_abs_lt hθc)
    rw [h0, arctan_zero] at this
    exact hθ (sub_eq_zero.1 this.symm)
  filter_upwards [(tendsto_exp_atTop.comp h).eventually_ge_atTop |tan (θ - c)|⁻¹] with t ht
  simp only [Function.comp_apply] at ht
  have h1 : 1 ≤ |tan (θ - c) *
      exp (4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))| := by
    rw [abs_mul, abs_of_pos (exp_pos _), ← mul_inv_cancel₀ (abs_ne_zero.2 hA)]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  simp only [endTrajectory, add_sub_cancel_left]
  rw [← arctan_one]
  rcases le_or_gt 0 (tan (θ - c) *
      exp (4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s))) with hx | hx
  · rw [abs_of_nonneg hx] at h1
    rw [abs_of_nonneg (arctan_nonneg.2 hx)]
    exact arctan_mono h1
  · rw [abs_of_neg hx] at h1
    rw [abs_of_neg (arctan_lt_zero.2 hx), ← arctan_neg]
    exact arctan_mono h1

/-- While the slope is `2 κ sin (2 (θ - c)) / (t (1 - t²))`, a solution which is within `π / 2`
of `c` at some time `s` is the explicit trajectory through `Θ s`. -/
private theorem eqOn_endTrajectory {δ κ c t₁ t₂ s : ℝ} {r Θ : ℝ → ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < 1)
    (hslope : ∀ t ∈ Icc t₁ t₂, ∀ θ,
      circleContinuationSlope δ r t θ = 2 * κ * sin (2 * (θ - c)) / (t * (1 - t ^ 2)))
    (hΘ : ∀ t ∈ Icc t₁ t₂,
      HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Icc t₁ t₂) t)
    (hs : s ∈ Icc t₁ t₂) (hΘs : |Θ s - c| < π / 2) :
    EqOn Θ (endTrajectory κ c s (Θ s)) (Icc t₁ t₂) :=
  eqOn_of_hasDerivWithinAt_circleContinuationSlope ht₁ ht₂ hΘ
    (fun t ht ↦ by
      rw [hslope t ht]
      exact (hasDerivAt_endTrajectory κ c s (Θ s)
        ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩).hasDerivWithinAt)
    hs (endTrajectory_self hΘs).symm

/-- `U t - U s` tends to `-∞` at `0`. -/
private theorem tendsto_intervalBaseTimeCoordinate_sub_nhdsGT_zero (s : ℝ) :
    Tendsto (fun t ↦ intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s) (𝓝[>] 0)
      atBot := by
  simpa [sub_eq_add_neg] using
    tendsto_intervalBaseTimeCoordinate_nhdsGT_zero.atBot_add
      (tendsto_const_nhds (x := -intervalBaseTimeCoordinate s))

/-- `U t - U s` tends to `+∞` at `1`. -/
private theorem tendsto_intervalBaseTimeCoordinate_sub_nhdsLT_one (s : ℝ) :
    Tendsto (fun t ↦ intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s) (𝓝[<] 1)
      atTop := by
  simpa [sub_eq_add_neg] using
    tendsto_intervalBaseTimeCoordinate_nhdsLT_one.atTop_add
      (tendsto_const_nhds (x := -intervalBaseTimeCoordinate s))

/-- While the slope is `2 κ sin (2 (θ - c)) / (t (1 - t²))` on an interval `S ⊆ (0, 1)` belonging
to a filter `l`, and either `κ = 0` or `4 κ (U t - U s) → +∞` along `l`, the only solution on `S`
tending to `c` along `l` is that constant: for `κ = 0` every solution is constant, and otherwise `c`
repels every other solution of the explicit flow. -/
private theorem eq_of_tendsto_of_circleContinuationSlope_eq {l : Filter ℝ} [l.NeBot] {S : Set ℝ}
    {δ κ c : ℝ} {r Θ : ℝ → ℝ} (hS : S ⊆ Ioo 0 1) (hSc : S.OrdConnected) (hSl : S ∈ l)
    (hslope : ∀ t ∈ S, ∀ θ,
      circleContinuationSlope δ r t θ = 2 * κ * sin (2 * (θ - c)) / (t * (1 - t ^ 2)))
    (hκ : κ = 0 ∨ ∀ s, Tendsto
      (fun t ↦ 4 * κ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate s)) l atTop)
    (hΘ : ∀ t ∈ S, HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) S t)
    (hlim : Tendsto Θ l (𝓝 c)) :
    ∀ t ∈ S, Θ t = c := by
  have hEq : ∀ s ∈ S, |Θ s - c| < π / 2 → EqOn Θ (endTrajectory κ c s (Θ s)) S :=
    fun s hs hΘs t ht ↦ eqOn_endTrajectory (lt_min (hS ht).1 (hS hs).1)
      (max_lt (hS ht).2 (hS hs).2) (fun u hu ↦ hslope u (hSc.uIcc_subset ht hs hu))
      (fun u hu ↦ (hΘ u (hSc.uIcc_subset ht hs hu)).mono (hSc.uIcc_subset ht hs))
      right_mem_uIcc hΘs left_mem_uIcc
  obtain ⟨s, hΘs, hs⟩ := ((hlim.eventually
    (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < π / 2))).and hSl).exists
  rw [Real.dist_eq] at hΘs
  have hΘsc : Θ s = c := by
    by_contra hne
    rcases hκ with rfl | hκ
    · have hconst : Tendsto Θ l (𝓝 (Θ s)) :=
        tendsto_const_nhds.congr' (eventuallyEq_of_mem hSl fun t ht ↦ by
          rw [hEq s hs hΘs ht]
          exact (endTrajectory_self (κ := 0) (s := s) hΘs).symm.trans (by simp [endTrajectory]))
      exact hne (tendsto_nhds_unique hconst hlim)
    have hfar := eventually_pi_div_four_le_abs_endTrajectory_sub hne hΘs (hκ s)
    have hnear := hlim.eventually (Metric.ball_mem_nhds c (by positivity : 0 < π / 4))
    obtain ⟨t, h₁, h₂, h₃⟩ := (hfar.and (hnear.and hSl)).exists
    rw [Real.dist_eq, hEq s hs hΘs h₃] at h₂
    linarith
  intro t ht
  rw [hEq s hs hΘs ht, hΘsc]
  simp [endTrajectory]

/-! ### The ends of the trajectories -/

/-- **Leaving a source minimum.** While the path is constant, `r = r₀` on `(0, a]`, the only
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` that tends at `t = 0` to the minimum
`r₀ + π / 2 + j π` of `δ cos (2 (θ - r₀))` is that constant. For `δ > 0` the minima of the source
function repel the solutions of the explicit flow as `t` decreases to `0`; for `δ = 0` every
solution is constant. -/
theorem eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope {δ r₀ a : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 ≤ δ) (ha : a < 1) (hr : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ : ∀ t ∈ Ioc 0 a,
      HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Ioc 0 a) t) {j : ℤ}
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    ∀ t ∈ Ioc 0 a, Θ t = r₀ + π / 2 + j * π := by
  rcases le_or_gt a 0 with ha0 | ha0
  · exact fun t ht ↦ absurd (ht.1.trans_le ht.2) ha0.not_gt
  exact eq_of_tendsto_of_circleContinuationSlope_eq (fun t ht ↦ ⟨ht.1, ht.2.trans_lt ha⟩)
    ordConnected_Ioc (Ioc_mem_nhdsGT ha0)
    (fun t ht _ ↦ circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi (hr t ht) j)
    (hδ.eq_or_lt.imp (fun h ↦ by rw [← h, neg_zero]) fun h s ↦
      (tendsto_intervalBaseTimeCoordinate_sub_nhdsGT_zero s).const_mul_atBot_of_neg (by linarith))
    hΘ hlim

/-- **Arriving at a target maximum.** While the path is constant, `r = r₁` on `[b, 1)`, the only
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` that tends at `t = 1` to the maximum
`r₁ + k π` of `δ cos (2 (θ - r₁))` is that constant. For `δ > 0` the maxima of the target function
repel the solutions of the explicit flow as `t` increases to `1`; for `δ = 0` every solution is
constant. -/
theorem eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope {δ r₁ b : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 ≤ δ) (hb : 0 < b) (hr : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ico b 1,
      HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Ico b 1) t) {k : ℤ}
    (hlim : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    ∀ t ∈ Ico b 1, Θ t = r₁ + k * π := by
  rcases le_or_gt 1 b with hb1 | hb1
  · exact fun t ht ↦ absurd (hb1.trans ht.1) ht.2.not_ge
  exact eq_of_tendsto_of_circleContinuationSlope_eq (fun t ht ↦ ⟨hb.trans_le ht.1, ht.2⟩)
    ordConnected_Ico (Ico_mem_nhdsLT hb1)
    (fun t ht _ ↦ circleContinuationSlope_eq_of_add_int_mul_pi (hr t ht) k)
    (hδ.eq_or_lt.imp Eq.symm fun h s ↦
      (tendsto_intervalBaseTimeCoordinate_sub_nhdsLT_one s).const_mul_atTop (by linarith))
    hΘ hlim

/-- **Into the basin of a target minimum.** While the path is constant, `r = r₁` on `[b, 1)`, a
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` which at time `b` lies within `π / 2` of
the minimum `r₁ + π / 2 + k π` of `δ cos (2 (θ - r₁))` tends to it at `t = 1`. -/
theorem tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope {δ r₁ b : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b < 1) (hr : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ico b 1,
      HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Ico b 1) t) {k : ℤ}
    (hΘb : |Θ b - (r₁ + π / 2 + k * π)| < π / 2) :
    Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + π / 2 + k * π)) := by
  have hEq : EqOn Θ (endTrajectory (-δ) (r₁ + π / 2 + k * π) b (Θ b)) (Ico b 1) := fun t ht ↦
    eqOn_endTrajectory hb ht.2
      (fun s hs _ ↦ circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi
        (hr s ⟨hs.1, hs.2.trans_lt ht.2⟩) k)
      (fun s hs ↦ (hΘ s ⟨hs.1, hs.2.trans_lt ht.2⟩).mono fun u hu ↦ ⟨hu.1, hu.2.trans_lt ht.2⟩)
      (left_mem_Icc.2 ht.1) hΘb
      (right_mem_Icc.2 ht.1)
  refine (tendsto_endTrajectory ?_).congr' (eventuallyEq_of_mem (Ico_mem_nhdsLT hb1) hEq).symm
  exact (tendsto_intervalBaseTimeCoordinate_sub_nhdsLT_one b).const_mul_atTop_of_neg
    (by linarith)

/-- **Out of the basin of a source maximum.** While the path is constant, `r = r₀` on `(0, a]`, a
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` which at time `a` lies within `π / 2` of
the maximum `r₀ + j π` of `δ cos (2 (θ - r₀))` tends to it at `t = 0`. -/
theorem tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope {δ r₀ a : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (ha1 : a < 1) (hr : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ : ∀ t ∈ Ioc 0 a,
      HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Ioc 0 a) t) {j : ℤ}
    (hΘa : |Θ a - (r₀ + j * π)| < π / 2) :
    Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + j * π)) := by
  have hEq : EqOn Θ (endTrajectory δ (r₀ + j * π) a (Θ a)) (Ioc 0 a) := fun t ht ↦
    eqOn_endTrajectory ht.1 ha1
      (fun s hs _ ↦ circleContinuationSlope_eq_of_add_int_mul_pi
        (hr s ⟨ht.1.trans_le hs.1, hs.2⟩) j)
      (fun s hs ↦ (hΘ s ⟨ht.1.trans_le hs.1, hs.2⟩).mono fun u hu ↦ ⟨ht.1.trans_le hu.1, hu.2⟩)
      (right_mem_Icc.2 ht.2) hΘa
      (left_mem_Icc.2 ht.2)
  refine (tendsto_endTrajectory ?_).congr' (eventuallyEq_of_mem (Ioc_mem_nhdsGT ha) hEq).symm
  exact (tendsto_intervalBaseTimeCoordinate_sub_nhdsGT_zero a).const_mul_atBot (by linarith)

/-! ### Classification of the index-preserving trajectories -/

section Classification

variable {δ r₀ r₁ a b : ℝ} {r Θ Θ₁ Θ₂ : ℝ → ℝ}

/-- A solution on `[a, b]` within `π / 2 - D` of `y` at time `a`, where
`D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bounds the drift across the window, is within `π / 2` of `y` at
time `b`. -/
private theorem abs_sub_lt_pi_div_two_right (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hΘ : ∀ t ∈ Icc a b, HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Icc a b) t)
    {y : ℝ} (hy : |Θ a - y| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    |Θ b - y| < π / 2 := by
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb hΘ
  rw [abs_of_pos hδ] at hdrift
  exact (abs_sub_le _ (Θ a) _).trans_lt (by linarith)

/-- A solution on `[a, b]` within `π / 2 - D` of `y` at time `b`, where
`D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bounds the drift across the window, is within `π / 2` of `y` at
time `a`. -/
private theorem abs_sub_lt_pi_div_two_left (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hΘ : ∀ t ∈ Icc a b, HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Icc a b) t)
    {y : ℝ} (hy : |Θ b - y| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    |Θ a - y| < π / 2 := by
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb hΘ
  rw [abs_of_pos hδ, abs_sub_comm] at hdrift
  exact (abs_sub_le _ (Θ b) _).trans_lt (by linarith)

/-- **The trajectory leaving a source minimum ends at a target minimum.** Let the path `r` be
constant, `r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the
drift of the angle across the window `[a, b]`. If the target minimum `r₁ + π / 2 + k π` is within
`π / 2 - D` of the source minimum `r₀ + π / 2 + j π`, then the trajectory leaving that source
minimum ends at it. -/
theorem tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope
    (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j k : ℤ}
    (hjk : |r₀ + j * π - (r₁ + k * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + π / 2 + k * π)) := by
  have hΘa : Θ a = r₀ + π / 2 + j * π :=
    eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope hδ.le (hab.trans_lt hb)
      hr₀ (fun t ht ↦ (hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩).hasDerivWithinAt) hlim a
      ⟨ha, le_rfl⟩
  refine tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope hδ (ha.trans_le hab) hb hr₁
    (fun t ht ↦ (hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩).hasDerivWithinAt) ?_
  refine abs_sub_lt_pi_div_two_right hδ ha hab hb
    (fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt) ?_
  rwa [hΘa, show r₀ + π / 2 + j * π - (r₁ + π / 2 + k * π) = r₀ + j * π - (r₁ + k * π) by ring]

/-- **The trajectory arriving at a target maximum starts at a source maximum.** Let the path `r`
be constant, `r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt`
bound the drift of the angle across the window `[a, b]`. If the source maximum `r₀ + j π` is within
`π / 2 - D` of the target maximum `r₁ + k π`, then the trajectory arriving at that target maximum
starts at it. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope
    (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hlim : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + j * π)) := by
  have hΘb : Θ b = r₁ + k * π :=
    eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope hδ.le (ha.trans_le hab)
      hr₁ (fun t ht ↦ (hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩).hasDerivWithinAt) hlim b
      ⟨le_rfl, hb⟩
  refine tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope hδ ha (hab.trans_lt hb) hr₀
    (fun t ht ↦ (hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩).hasDerivWithinAt) ?_
  exact abs_sub_lt_pi_div_two_left hδ ha hab hb
    (fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt) (by rwa [hΘb])

/-- **No connection from a source minimum to a target maximum.** Let the path `r` be constant,
`r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the drift of
the angle across the window `[a, b]`. A trajectory leaving the source minimum `r₀ + π / 2 + j π`
is constant on `(0, a]`, and one arriving at the target maximum `r₁ + k π` is constant on
`[b, 1)`, so no trajectory joins them when they are more than `D` apart. Both are zeros of index
`1` for the parameter field, and such a connection would be the failure of transversality
exhibited by `TauCeti.exists_circleContinuationField_connection` for large `δ`. -/
theorem not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope
    (hδ : 0 ≤ δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j k : ℤ}
    (hjk : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < |r₁ + k * π - (r₀ + π / 2 + j * π)|)
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    ¬Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) := by
  intro h
  have hΘa : Θ a = r₀ + π / 2 + j * π :=
    eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope hδ (hab.trans_lt hb)
      hr₀ (fun t ht ↦ (hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩).hasDerivWithinAt) hlim a
      ⟨ha, le_rfl⟩
  have hΘb : Θ b = r₁ + k * π :=
    eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope hδ (ha.trans_le hab)
      hr₁ (fun t ht ↦ (hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩).hasDerivWithinAt) h b
      ⟨le_rfl, hb⟩
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb
    fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt
  rw [abs_of_nonneg hδ, hΘa, hΘb] at hdrift
  exact hdrift.not_gt hjk

/-- **There is at most one trajectory leaving a source minimum.** -/
theorem eqOn_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {j : ℤ}
    (h₁ : Tendsto Θ₁ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)))
    (h₂ : Tendsto Θ₂ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hend : ∀ {Θ : ℝ → ℝ}, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) →
      Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)) → Θ a = r₀ + π / 2 + j * π :=
    fun hΘ hlim ↦ eq_of_tendsto_nhdsGT_zero_of_hasDerivWithinAt_circleContinuationSlope hδ ha1 hr₀
      (fun t ht ↦ (hΘ t ⟨ht.1, ht.2.trans_lt ha1⟩).hasDerivWithinAt) hlim a ⟨ha, le_rfl⟩
  exact eqOn_Ioo_of_hasDerivAt_circleContinuationSlope ⟨ha, ha1⟩ hΘ₁ hΘ₂
    ((hend hΘ₁ h₁).trans (hend hΘ₂ h₂).symm)

/-- **There is at most one trajectory arriving at a target maximum.** -/
theorem eqOn_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope (hδ : 0 ≤ δ)
    (hb : 0 < b) (hb1 : b < 1) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {k : ℤ}
    (h₁ : Tendsto Θ₁ (𝓝[<] 1) (𝓝 (r₁ + k * π))) (h₂ : Tendsto Θ₂ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hend : ∀ {Θ : ℝ → ℝ}, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) →
      Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) → Θ b = r₁ + k * π :=
    fun hΘ hlim ↦ eq_of_tendsto_nhdsLT_one_of_hasDerivWithinAt_circleContinuationSlope hδ hb hr₁
      (fun t ht ↦ (hΘ t ⟨hb.trans_le ht.1, ht.2⟩).hasDerivWithinAt) hlim b ⟨le_rfl, hb1⟩
  exact eqOn_Ioo_of_hasDerivAt_circleContinuationSlope ⟨hb, hb1⟩ hΘ₁ hΘ₂
    ((hend hΘ₁ h₁).trans (hend hΘ₂ h₂).symm)

/-! ### Existence -/

/-- **Existence of trajectories.** If the path `r` is continuous on the window `[a, b] ⊆ (0, 1)`
and constant on either side of it, then through every point `(θ₀, t₀)` with `t₀` in the window
passes a solution of `Θ' = circleContinuationSlope δ r t (Θ t)` on the whole of `0 < t < 1`. It is
unique, by `TauCeti.eqOn_Ioo_of_hasDerivAt_circleContinuationSlope`. -/
theorem exists_hasDerivAt_circleContinuationSlope (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (θ₀ : ℝ) :
    ∃ Θ : ℝ → ℝ, Θ t₀ = θ₀ ∧
      ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t := by
  obtain ⟨W, hW₀, hW⟩ :=
    exists_eq_forall_mem_Icc_hasDerivWithinAt_circleContinuationSlope (δ := δ) θ₀ ha hb hr ht₀
  obtain ⟨E₀, hE₀, hE₀'⟩ := exists_endTrajectory (δ := δ) (r₀ := r₀) (r := r) (W a) a
  obtain ⟨E₁, hE₁, hE₁'⟩ := exists_endTrajectory (δ := δ) (r₀ := r₁) (r := r) (W b) b
  obtain ⟨Θ, -, hΘW, -, hΘ⟩ := exists_eq_hasDerivAt_of_hasDerivWithinAt_Icc (I := Ioo 0 1) hab
    hE₀ hE₁.symm (fun t ht hta ↦ (hE₀' t ht (hr₀ t ⟨ht.1, hta⟩)).hasDerivWithinAt) hW
    (fun t ht htb ↦ (hE₁' t ht (hr₁ t ⟨htb, ht.2⟩)).hasDerivWithinAt)
  exact ⟨Θ, by rw [hΘW t₀ ht₀, hW₀], hΘ⟩

/-- **Existence of the trajectory leaving a source minimum.** Let the path `r` be continuous on
`[a, b]`, constant, `r₀` on `(0, a]` and `r₁` on `[b, 1)`. Under the drift hypothesis of
`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`, there is
a trajectory from the source minimum `r₀ + π / 2 + j π` to the target minimum
`r₁ + π / 2 + k π`. It is unique, by
`TauCeti.eqOn_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`. -/
theorem exists_hasDerivAt_circleContinuationSlope_tendsto_add_pi_div_two (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) {j k : ℤ}
    (hjk : |r₀ + j * π - (r₁ + k * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)) ∧
      Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + π / 2 + k * π)) := by
  obtain ⟨Θ, hΘa, hΘ⟩ := exists_hasDerivAt_circleContinuationSlope (δ := δ) ha hab hb hr hr₀ hr₁
    ⟨le_rfl, hab⟩ (r₀ + π / 2 + j * π)
  have hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)) :=
    tendsto_const_nhds.congr' (eventuallyEq_of_mem (Ioc_mem_nhdsGT ha) fun t ht ↦
      (eqOn_const_of_hasDerivWithinAt_circleContinuationSlope ht.1 (hab.trans_lt hb)
        (right_mem_Icc.2 ht.2) (fun u hu ↦ hr₀ u ⟨ht.1.trans_le hu.1, hu.2⟩)
        (sin_two_mul_add_pi_div_two_add_int_mul_pi_sub r₀ j)
        (fun u hu ↦ (hΘ u ⟨ht.1.trans_le hu.1, hu.2.trans_lt (hab.trans_lt hb)⟩).hasDerivWithinAt)
        hΘa (left_mem_Icc.2 ht.2)).symm)
  exact ⟨Θ, hΘ, hlim,
    tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ hjk hlim⟩

/-- **Existence of the trajectory arriving at a target maximum.** Let the path `r` be continuous
on `[a, b]`, constant, `r₀` on `(0, a]` and `r₁` on `[b, 1)`. Under the drift hypothesis of
`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`, there is
a trajectory from the source maximum `r₀ + j π` to the target maximum `r₁ + k π`. It is unique, by
`TauCeti.eqOn_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`. -/
theorem exists_hasDerivAt_circleContinuationSlope_tendsto_add_int_mul_pi (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) {j k : ℤ}
    (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + j * π)) ∧ Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) := by
  obtain ⟨Θ, hΘb, hΘ⟩ := exists_hasDerivAt_circleContinuationSlope (δ := δ) ha hab hb hr hr₀ hr₁
    ⟨hab, le_rfl⟩ (r₁ + k * π)
  have hlim : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) :=
    tendsto_const_nhds.congr' (eventuallyEq_of_mem (Ico_mem_nhdsLT hb) fun t ht ↦
      (eqOn_const_of_hasDerivWithinAt_circleContinuationSlope (ha.trans_le hab) ht.2
        (left_mem_Icc.2 ht.1) (fun u hu ↦ hr₁ u ⟨hu.1, hu.2.trans_lt ht.2⟩)
        (sin_two_mul_add_int_mul_pi_sub r₁ k)
        (fun u hu ↦ (hΘ u ⟨(ha.trans_le hab).trans_le hu.1, hu.2.trans_lt ht.2⟩).hasDerivWithinAt)
        hΘb (right_mem_Icc.2 ht.1)).symm)
  exact ⟨Θ, hΘ,
    tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ hjk hlim, hlim⟩

end Classification

end TauCeti
