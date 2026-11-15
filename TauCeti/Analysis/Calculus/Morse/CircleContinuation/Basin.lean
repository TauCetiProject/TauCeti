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
file classifies the ones that preserve the index, for `δ > 0` and a path that is constant near the
two ends: `r = r₀` on `(0, a]` and `r = r₁` on `[b, 1)`, with `0 < a ≤ b < 1`. The zeros of the
field at `t = 0` are the maxima `r₀ + j π` and the minima `r₀ + π / 2 + j π` of the source function,
of index `2` and `1` for the field; at `t = 1` they are the maxima `r₁ + k π` and the minima
`r₁ + π / 2 + k π` of the target function, of index `1` and `0`. The index-preserving trajectories
run from a source minimum to a target minimum, or from a source maximum to a target maximum.

**The end windows.** While the path is constant, the time coordinate
`U(t) = log t - (1 / 2) log (1 - t²)` of the base flow (`TauCeti.intervalBaseTimeCoordinate`)
turns the equation into the negative gradient flow of `δ cos (2 (θ - r₀))` on the line of lifted
angles, which is solved explicitly: near a zero `c` of the slope,
`tan (Θ t - c) = tan (Θ s - c) e^{± 4 δ (U t - U s)}`. Since `U` tends to `-∞` at `0` and to `+∞`
at `1`, this gives the four end behaviours.

* The only solution tending at `0` to a source minimum is constant on `(0, a]`
  (`TauCeti.eq_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`), and the only one
  tending at `1` to a target maximum is constant on `[b, 1)`
  (`TauCeti.eq_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`).
* A solution within `π / 2` of a target minimum at time `b` tends to it at `1`
  (`TauCeti.tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`), and one within `π / 2` of a
  source maximum at time `a` tends to it at `0`
  (`TauCeti.tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`).

**Classification.** Solutions on windows `[a, b] ⊆ (0, 1)` are unique and exist through every
point (`TauCeti.eqOn_of_hasDerivAt_circleContinuationSlope`,
`TauCeti.exists_eq_forall_mem_Icc_hasDerivWithinAt_circleContinuationSlope`). Across the window
`[a, b]` the angle moves by at most
`D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt`
(`TauCeti.abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope`). So if
`|r₀ + j π - (r₁ + k π)| + D < π / 2`, the trajectory leaving the source minimum `r₀ + π / 2 + j π`
ends at the target minimum `r₁ + π / 2 + k π`
(`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`), and the
trajectory arriving at the target maximum `r₁ + k π` starts at the source maximum `r₀ + j π`
(`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`). Each of
these trajectories is unique, and exists when the path is continuous on `[a, b]`; so the count of
trajectories between these two zeros is `1`, and between the first and any other zero of the same
index it is `0`. A source
minimum is joined to no target maximum
(`TauCeti.not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`):
such a connection between zeros of the same index is the failure of transversality exhibited by
`TauCeti.exists_circleContinuationField_connection` for large `δ`.

For the circle continuation counterexamples, take `a = 1/6` and `b = 5/6`, and `δ` small enough
that `D < π / 12`. For the half-turn `r₁ = r₀ + π`, the trajectory from `r₀ + π / 2 + j π` ends at
`r₁ + π / 2 + (j - 1) π`, the same point of the circle: the continuation map is the identity in
fixed spatial bases, while tracking the critical points along the path exchanges the two minima, and
likewise the two maxima. For a rotation by `π / 3` it ends at `r₁ + π / 2 + j π`, the tracked
minimum, while for the rotation by `2 π / 3` concatenating two of them it ends at
`r₁ + π / 2 + (j - 1) π`: each rotation by `π / 3` continues the tracked labels identically, but
their concatenation exchanges them.

## Main results

* `TauCeti.eq_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.eq_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`: the ends of the trajectories.
* `TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope`: the
  classification by basins.
* `TauCeti.not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`: no
  source minimum is joined to a target maximum.
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
  simp only [endTrajectory]
  rw [sub_self, mul_zero, exp_zero, mul_one,
    arctan_tan (neg_lt_of_abs_lt h) (lt_of_abs_lt h), add_sub_cancel]

private theorem hasDerivAt_endTrajectory (κ c s θ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (endTrajectory κ c s θ)
      (2 * κ * sin (2 * (endTrajectory κ c s θ t - c)) / (t * (1 - t ^ 2))) t := by
  have hm : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
  have hg := ((((hasDerivAt_intervalBaseTimeCoordinate ht).sub_const
    (intervalBaseTimeCoordinate s)).const_mul (4 * κ)).exp).const_mul (tan (θ - c))
  convert (hg.arctan).const_add c using 1
  · rfl
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

/-- Near a maximum `c = r₀ + j π` of `δ cos (2 (θ - r₀))` the slope is
`2 δ sin (2 (θ - c)) / (t (1 - t²))`. -/
private theorem circleContinuationSlope_eq_of_add_int_mul_pi {δ r₀ t θ : ℝ} {r : ℝ → ℝ}
    (hr : r t = r₀) (j : ℤ) :
    circleContinuationSlope δ r t θ =
      2 * δ * sin (2 * (θ - (r₀ + j * π))) / (t * (1 - t ^ 2)) := by
  rw [circleContinuationSlope_def, hr,
    show 2 * (θ - r₀) = 2 * (θ - (r₀ + j * π)) + j * (2 * π) by ring, sin_add_int_mul_two_pi]

/-- Near a minimum `c = r₀ + π / 2 + j π` of `δ cos (2 (θ - r₀))` the slope is
`2 (-δ) sin (2 (θ - c)) / (t (1 - t²))`. -/
private theorem circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi {δ r₀ t θ : ℝ}
    {r : ℝ → ℝ} (hr : r t = r₀) (j : ℤ) :
    circleContinuationSlope δ r t θ =
      2 * (-δ) * sin (2 * (θ - (r₀ + π / 2 + j * π))) / (t * (1 - t ^ 2)) := by
  rw [circleContinuationSlope_def, hr,
    show 2 * (θ - r₀) = 2 * (θ - (r₀ + π / 2 + j * π)) + π + j * (2 * π) by ring,
    sin_add_int_mul_two_pi, sin_add_pi]
  ring

/-- The maxima `r₀ + j π` of `δ cos (2 (θ - r₀))` are stationary while the path is `r₀`. -/
private theorem hasDerivAt_const_add_int_mul_pi {δ r₀ t : ℝ} {r : ℝ → ℝ} (hr : r t = r₀) (j : ℤ) :
    HasDerivAt (fun _ ↦ r₀ + j * π) (circleContinuationSlope δ r t (r₀ + j * π)) t := by
  rw [circleContinuationSlope_eq_of_add_int_mul_pi hr j, sub_self, mul_zero, sin_zero, mul_zero,
    zero_div]
  exact hasDerivAt_const t _

/-- The minima `r₀ + π / 2 + j π` of `δ cos (2 (θ - r₀))` are stationary while the path is
`r₀`. -/
private theorem hasDerivAt_const_add_pi_div_two_add_int_mul_pi {δ r₀ t : ℝ} {r : ℝ → ℝ}
    (hr : r t = r₀) (j : ℤ) :
    HasDerivAt (fun _ ↦ r₀ + π / 2 + j * π)
      (circleContinuationSlope δ r t (r₀ + π / 2 + j * π)) t := by
  rw [circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi hr j, sub_self, mul_zero,
    sin_zero, mul_zero, zero_div]
  exact hasDerivAt_const t _

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
    (hΘ : ∀ t ∈ Icc t₁ t₂, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hs : s ∈ Icc t₁ t₂) (hΘs : |Θ s - c| < π / 2) :
    EqOn Θ (endTrajectory κ c s (Θ s)) (Icc t₁ t₂) :=
  eqOn_of_hasDerivAt_circleContinuationSlope ht₁ ht₂ hΘ
    (fun t ht ↦ by
      rw [hslope t ht]
      exact hasDerivAt_endTrajectory κ c s (Θ s) ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩)
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

/-! ### The ends of the trajectories -/

/-- **Leaving a source minimum.** While the path is constant, `r = r₀` on `(0, a]`, the only
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` that tends at `t = 0` to the minimum
`r₀ + π / 2 + j π` of `δ cos (2 (θ - r₀))` is that constant. For `δ > 0` the minima of the source
function repel the solutions of the explicit flow as `t` decreases to `0`; for `δ = 0` every
solution is constant. -/
theorem eq_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope {δ r₀ a : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 ≤ δ) (ha : a < 1) (hr : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ : ∀ t ∈ Ioc 0 a, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j : ℤ}
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    ∀ t ∈ Ioc 0 a, Θ t = r₀ + π / 2 + j * π := by
  set c := r₀ + π / 2 + j * π
  rcases hδ.eq_or_lt with rfl | hδ
  · -- For `δ = 0` every solution is constant.
    intro t ht
    have hΘt : ∀ s ∈ Ioc 0 t, Θ t = Θ s := fun s hs ↦
      (eqOn_of_hasDerivAt_circleContinuationSlope (Θ₂ := fun _ ↦ Θ t) hs.1 (ht.2.trans_lt ha)
        (fun u hu ↦ hΘ u ⟨hs.1.trans_le hu.1, hu.2.trans ht.2⟩)
        (fun u _ ↦ by simpa [circleContinuationSlope_def] using hasDerivAt_const u (Θ t))
        (right_mem_Icc.2 hs.2) rfl (left_mem_Icc.2 hs.2)).symm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr'
      (eventuallyEq_of_mem (Ioc_mem_nhdsGT ht.1) hΘt)) hlim
  rcases le_or_gt a 0 with ha0 | ha0
  · exact fun t ht ↦ absurd (ht.1.trans_le ht.2) ha0.not_gt
  have hslope : ∀ t ∈ Ioc 0 a, ∀ θ,
      circleContinuationSlope δ r t θ = 2 * (-δ) * sin (2 * (θ - c)) / (t * (1 - t ^ 2)) :=
    fun t ht θ ↦ circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi (hr t ht) j
  have hconst : ∀ t ∈ Ioc 0 a, HasDerivAt (fun _ ↦ c) (circleContinuationSlope δ r t c) t :=
    fun t ht ↦ hasDerivAt_const_add_pi_div_two_add_int_mul_pi (hr t ht) j
  obtain ⟨t₂, ht₂a, hΘt₂⟩ : ∃ t₂ ∈ Ioc 0 a, Θ t₂ = c := by
    obtain ⟨t₂, hΘt₂, ht₂⟩ := ((hlim.eventually
      (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < π / 2))).and (Ioc_mem_nhdsGT ha0)).exists
    rw [Real.dist_eq] at hΘt₂
    refine ⟨t₂, ht₂, ?_⟩
    by_contra hne
    have hEq : EqOn Θ (endTrajectory (-δ) c t₂ (Θ t₂)) (Ioc 0 t₂) := fun t ht ↦
      eqOn_endTrajectory ht.1 (ht₂.2.trans_lt ha)
        (fun s hs ↦ hslope s ⟨ht.1.trans_le hs.1, hs.2.trans ht₂.2⟩)
        (fun s hs ↦ hΘ s ⟨ht.1.trans_le hs.1, hs.2.trans ht₂.2⟩) (right_mem_Icc.2 ht.2)
        hΘt₂ (left_mem_Icc.2 ht.2)
    have hfar := eventually_pi_div_four_le_abs_endTrajectory_sub (l := 𝓝[>] 0) (κ := -δ) (s := t₂)
      hne hΘt₂ (((tendsto_intervalBaseTimeCoordinate_sub_nhdsGT_zero t₂).const_mul_atBot_of_neg
        (by linarith)))
    have hnear := hlim.eventually (Metric.ball_mem_nhds c (by positivity : 0 < π / 4))
    obtain ⟨t, h₁, h₂, h₃⟩ := (hfar.and (hnear.and (Ioc_mem_nhdsGT ht₂.1))).exists
    rw [Real.dist_eq, hEq h₃] at h₂
    linarith
  intro t ht
  have hm : 0 < min t t₂ := lt_min ht.1 ht₂a.1
  exact eqOn_of_hasDerivAt_circleContinuationSlope hm ha
    (fun s hs ↦ hΘ s ⟨hm.trans_le hs.1, hs.2⟩) (fun s hs ↦ hconst s ⟨hm.trans_le hs.1, hs.2⟩)
    ⟨min_le_right _ _, ht₂a.2⟩ hΘt₂ ⟨min_le_left _ _, ht.2⟩

/-- **Arriving at a target maximum.** While the path is constant, `r = r₁` on `[b, 1)`, the only
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` that tends at `t = 1` to the maximum
`r₁ + k π` of `δ cos (2 (θ - r₁))` is that constant. For `δ > 0` the maxima of the target function
repel the solutions of the explicit flow as `t` increases to `1`; for `δ = 0` every solution is
constant. -/
theorem eq_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope {δ r₁ b : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 ≤ δ) (hb : 0 < b) (hr : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ico b 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {k : ℤ}
    (hlim : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    ∀ t ∈ Ico b 1, Θ t = r₁ + k * π := by
  set c := r₁ + k * π
  rcases hδ.eq_or_lt with rfl | hδ
  · -- For `δ = 0` every solution is constant.
    intro t ht
    have hΘt : ∀ s ∈ Ico t 1, Θ t = Θ s := fun s hs ↦
      (eqOn_of_hasDerivAt_circleContinuationSlope (Θ₂ := fun _ ↦ Θ t) (hb.trans_le ht.1) hs.2
        (fun u hu ↦ hΘ u ⟨ht.1.trans hu.1, hu.2.trans_lt hs.2⟩)
        (fun u _ ↦ by simpa [circleContinuationSlope_def] using hasDerivAt_const u (Θ t))
        (left_mem_Icc.2 hs.1) rfl (right_mem_Icc.2 hs.1)).symm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr'
      (eventuallyEq_of_mem (Ico_mem_nhdsLT ht.2) hΘt)) hlim
  rcases le_or_gt 1 b with hb1 | hb1
  · exact fun t ht ↦ absurd (hb1.trans ht.1) ht.2.not_ge
  have hslope : ∀ t ∈ Ico b 1, ∀ θ,
      circleContinuationSlope δ r t θ = 2 * δ * sin (2 * (θ - c)) / (t * (1 - t ^ 2)) :=
    fun t ht θ ↦ circleContinuationSlope_eq_of_add_int_mul_pi (hr t ht) k
  have hconst : ∀ t ∈ Ico b 1, HasDerivAt (fun _ ↦ c) (circleContinuationSlope δ r t c) t :=
    fun t ht ↦ hasDerivAt_const_add_int_mul_pi (hr t ht) k
  obtain ⟨t₂, ht₂b, hΘt₂⟩ : ∃ t₂ ∈ Ico b 1, Θ t₂ = c := by
    obtain ⟨t₂, hΘt₂, ht₂⟩ := ((hlim.eventually
      (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < π / 2))).and (Ico_mem_nhdsLT hb1)).exists
    rw [Real.dist_eq] at hΘt₂
    refine ⟨t₂, ht₂, ?_⟩
    by_contra hne
    have hEq : EqOn Θ (endTrajectory δ c t₂ (Θ t₂)) (Ico t₂ 1) := fun t ht ↦
      eqOn_endTrajectory (hb.trans_le ht₂.1) ht.2
        (fun s hs ↦ hslope s ⟨ht₂.1.trans hs.1, hs.2.trans_lt ht.2⟩)
        (fun s hs ↦ hΘ s ⟨ht₂.1.trans hs.1, hs.2.trans_lt ht.2⟩) (left_mem_Icc.2 ht.1)
        hΘt₂ (right_mem_Icc.2 ht.1)
    have hfar := eventually_pi_div_four_le_abs_endTrajectory_sub (l := 𝓝[<] 1) (κ := δ) (s := t₂)
      hne hΘt₂ (((tendsto_intervalBaseTimeCoordinate_sub_nhdsLT_one t₂).const_mul_atTop
        (by linarith)))
    have hnear := hlim.eventually (Metric.ball_mem_nhds c (by positivity : 0 < π / 4))
    obtain ⟨t, h₁, h₂, h₃⟩ := (hfar.and (hnear.and (Ico_mem_nhdsLT ht₂.2))).exists
    rw [Real.dist_eq, hEq h₃] at h₂
    linarith
  intro t ht
  have hm : max t t₂ < 1 := max_lt ht.2 ht₂b.2
  exact eqOn_of_hasDerivAt_circleContinuationSlope hb hm
    (fun s hs ↦ hΘ s ⟨hs.1, hs.2.trans_lt hm⟩) (fun s hs ↦ hconst s ⟨hs.1, hs.2.trans_lt hm⟩)
    ⟨ht₂b.1, le_max_right _ _⟩ hΘt₂ ⟨ht.1, le_max_left _ _⟩

/-- **Into the basin of a target minimum.** While the path is constant, `r = r₁` on `[b, 1)`, a
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` which at time `b` lies within `π / 2` of
the minimum `r₁ + π / 2 + k π` of `δ cos (2 (θ - r₁))` tends to it at `t = 1`. -/
theorem tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope {δ r₁ b : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b < 1) (hr : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ico b 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {k : ℤ}
    (hΘb : |Θ b - (r₁ + π / 2 + k * π)| < π / 2) :
    Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + π / 2 + k * π)) := by
  have hEq : EqOn Θ (endTrajectory (-δ) (r₁ + π / 2 + k * π) b (Θ b)) (Ico b 1) := fun t ht ↦
    eqOn_endTrajectory hb ht.2
      (fun s hs _ ↦ circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi
        (hr s ⟨hs.1, hs.2.trans_lt ht.2⟩) k)
      (fun s hs ↦ hΘ s ⟨hs.1, hs.2.trans_lt ht.2⟩) (left_mem_Icc.2 ht.1) hΘb
      (right_mem_Icc.2 ht.1)
  refine (tendsto_endTrajectory ?_).congr' (eventuallyEq_of_mem (Ico_mem_nhdsLT hb1) hEq).symm
  exact (tendsto_intervalBaseTimeCoordinate_sub_nhdsLT_one b).const_mul_atTop_of_neg
    (by linarith)

/-- **Out of the basin of a source maximum.** While the path is constant, `r = r₀` on `(0, a]`, a
solution of `Θ' = circleContinuationSlope δ r t (Θ t)` which at time `a` lies within `π / 2` of
the maximum `r₀ + j π` of `δ cos (2 (θ - r₀))` tends to it at `t = 0`. -/
theorem tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope {δ r₀ a : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (ha1 : a < 1) (hr : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ : ∀ t ∈ Ioc 0 a, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j : ℤ}
    (hΘa : |Θ a - (r₀ + j * π)| < π / 2) :
    Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + j * π)) := by
  have hEq : EqOn Θ (endTrajectory δ (r₀ + j * π) a (Θ a)) (Ioc 0 a) := fun t ht ↦
    eqOn_endTrajectory ht.1 ha1
      (fun s hs _ ↦ circleContinuationSlope_eq_of_add_int_mul_pi
        (hr s ⟨ht.1.trans_le hs.1, hs.2⟩) j)
      (fun s hs ↦ hΘ s ⟨ht.1.trans_le hs.1, hs.2⟩) (right_mem_Icc.2 ht.2) hΘa
      (left_mem_Icc.2 ht.2)
  refine (tendsto_endTrajectory ?_).congr' (eventuallyEq_of_mem (Ioc_mem_nhdsGT ha) hEq).symm
  exact (tendsto_intervalBaseTimeCoordinate_sub_nhdsGT_zero a).const_mul_atBot (by linarith)

/-! ### Classification of the index-preserving trajectories -/

section Classification

variable {δ r₀ r₁ a b : ℝ} {r Θ Θ₁ Θ₂ : ℝ → ℝ}

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
    eq_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ.le (hab.trans_lt hb) hr₀
      (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) hlim a ⟨ha, le_rfl⟩
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb
    (fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt)
  rw [abs_of_pos hδ] at hdrift
  refine tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ (ha.trans_le hab) hb hr₁
    (fun t ht ↦ hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩) ?_
  calc |Θ b - (r₁ + π / 2 + k * π)| = |(Θ b - Θ a) + (r₀ + j * π - (r₁ + k * π))| := by
        rw [hΘa]; ring_nf
    _ ≤ |Θ b - Θ a| + |r₀ + j * π - (r₁ + k * π)| := abs_add_le _ _
    _ < π / 2 := by linarith

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
    eq_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ.le (ha.trans_le hab) hr₁
      (fun t ht ↦ hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩) hlim b ⟨le_rfl, hb⟩
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb
    (fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt)
  rw [abs_of_pos hδ] at hdrift
  refine tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ ha (hab.trans_lt hb) hr₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) ?_
  calc |Θ a - (r₀ + j * π)| = |-(Θ b - Θ a) + (r₁ + k * π - (r₀ + j * π))| := by
        rw [hΘb]; ring_nf
    _ ≤ |-(Θ b - Θ a)| + |r₁ + k * π - (r₀ + j * π)| := abs_add_le _ _
    _ < π / 2 := by rw [abs_neg]; linarith

/-- **No connection from a source minimum to a target maximum.** Under the drift hypothesis of
`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope`, the
trajectory leaving a source minimum ends at a target minimum, so it ends at no target maximum
`r₁ + k' π`. Such a connection would join two zeros of the parameter field of the same index. -/
theorem not_tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope
    (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {j k : ℤ}
    (hjk : |r₀ + j * π - (r₁ + k * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) (k' : ℤ) :
    ¬Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k' * π)) := by
  intro h
  have he := tendsto_nhds_unique
    (tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ hjk hlim) h
  have h2 : ((2 * (k' - k) - 1 : ℤ) : ℝ) * π = 0 := by
    push_cast
    linarith
  have h3 : (2 * (k' - k) - 1 : ℤ) = 0 := by
    exact_mod_cast (mul_eq_zero.1 h2).resolve_right pi_ne_zero
  omega

/-- **There is at most one trajectory leaving a source minimum.** -/
theorem eqOn_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope (hδ : 0 < δ)
    (ha : 0 < a) (ha1 : a < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {j : ℤ}
    (h₁ : Tendsto Θ₁ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)))
    (h₂ : Tendsto Θ₂ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π))) :
    EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hend : ∀ {Θ : ℝ → ℝ}, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) →
      Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)) → Θ a = r₀ + π / 2 + j * π :=
    fun hΘ hlim ↦ eq_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ.le ha1 hr₀
      (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt ha1⟩) hlim a ⟨ha, le_rfl⟩
  intro t ht
  have hm : 0 < min t a := lt_min ht.1 ha
  have hM : max t a < 1 := max_lt ht.2 ha1
  exact eqOn_of_hasDerivAt_circleContinuationSlope hm hM
    (fun s hs ↦ hΘ₁ s ⟨hm.trans_le hs.1, hs.2.trans_lt hM⟩)
    (fun s hs ↦ hΘ₂ s ⟨hm.trans_le hs.1, hs.2.trans_lt hM⟩) ⟨min_le_right _ _, le_max_right _ _⟩
    ((hend hΘ₁ h₁).trans (hend hΘ₂ h₂).symm) ⟨min_le_left _ _, le_max_left _ _⟩

/-- **There is at most one trajectory arriving at a target maximum.** -/
theorem eqOn_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope (hδ : 0 < δ)
    (hb : 0 < b) (hb1 : b < 1) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {k : ℤ}
    (h₁ : Tendsto Θ₁ (𝓝[<] 1) (𝓝 (r₁ + k * π))) (h₂ : Tendsto Θ₂ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hend : ∀ {Θ : ℝ → ℝ}, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) →
      Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) → Θ b = r₁ + k * π :=
    fun hΘ hlim ↦ eq_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ.le hb hr₁
      (fun t ht ↦ hΘ t ⟨hb.trans_le ht.1, ht.2⟩) hlim b ⟨le_rfl, hb1⟩
  intro t ht
  have hm : 0 < min t b := lt_min ht.1 hb
  have hM : max t b < 1 := max_lt ht.2 hb1
  exact eqOn_of_hasDerivAt_circleContinuationSlope hm hM
    (fun s hs ↦ hΘ₁ s ⟨hm.trans_le hs.1, hs.2.trans_lt hM⟩)
    (fun s hs ↦ hΘ₂ s ⟨hm.trans_le hs.1, hs.2.trans_lt hM⟩) ⟨min_le_right _ _, le_max_right _ _⟩
    ((hend hΘ₁ h₁).trans (hend hΘ₂ h₂).symm) ⟨min_le_left _ _, le_max_left _ _⟩

/-! ### Existence -/

/-- Two continuation trajectories on adjacent closed intervals which agree at the common end glue
to a trajectory on their union. -/
private theorem hasDerivWithinAt_Icc_ite {f g : ℝ → ℝ} {l m u : ℝ} (hlm : l ≤ m) (hmu : m ≤ u)
    (hf : ∀ t ∈ Icc l m, HasDerivWithinAt f (circleContinuationSlope δ r t (f t)) (Icc l m) t)
    (hg : ∀ t ∈ Icc m u, HasDerivWithinAt g (circleContinuationSlope δ r t (g t)) (Icc m u) t)
    (hfg : f m = g m) :
    ∀ t ∈ Icc l u, HasDerivWithinAt (fun t ↦ if t ≤ m then f t else g t)
      (circleContinuationSlope δ r t (if t ≤ m then f t else g t)) (Icc l u) t := by
  intro t ht
  have hhf : EqOn (fun t ↦ if t ≤ m then f t else g t) f (Icc l m) := fun s hs ↦ ite_eq_left hs.2
  have hhg : EqOn (fun t ↦ if t ≤ m then f t else g t) g (Icc m u) := fun s hs ↦ by
    rcases hs.1.eq_or_lt with rfl | hs'
    · exact (ite_eq_left le_rfl).trans hfg
    · exact ite_eq_right (not_le.2 hs')
  rw [← Icc_union_Icc_eq_Icc hlm hmu]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases htm : t ≤ m
    · rw [show (if t ≤ m then f t else g t) = f t from hhf ⟨ht.1, htm⟩]
      exact (hf t ⟨ht.1, htm⟩).congr hhf (hhf ⟨ht.1, htm⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.2
  · by_cases htm : m ≤ t
    · rw [show (if t ≤ m then f t else g t) = g t from hhg ⟨htm, ht.2⟩]
      exact (hg t ⟨htm, ht.2⟩).congr hhg (hhg ⟨htm, ht.2⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.1

/-- Three solutions on `[l, a]`, `[a, b]` and `[b, u]` agreeing at `a` and `b` glue to a solution
on `(0, 1)`, once `l` and `u` can be taken arbitrarily close to `0` and `1`. -/
private theorem hasDerivAt_ite_ite {f g h : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hf : ∀ l ∈ Ioo 0 a, ∀ t ∈ Icc l a,
      HasDerivWithinAt f (circleContinuationSlope δ r t (f t)) (Icc l a) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (circleContinuationSlope δ r t (g t)) (Icc a b) t)
    (hh : ∀ u ∈ Ioo b 1, ∀ t ∈ Icc b u,
      HasDerivWithinAt h (circleContinuationSlope δ r t (h t)) (Icc b u) t)
    (hfg : f a = g a) (hgh : g b = h b) :
    ∀ t ∈ Ioo 0 1, HasDerivAt (fun t ↦ if t ≤ b then (if t ≤ a then f t else g t) else h t)
      (circleContinuationSlope δ r t
        (if t ≤ b then (if t ≤ a then f t else g t) else h t)) t := by
  intro t ht
  set l := min t a / 2
  set u := (max t b + 1) / 2
  have hl : l ∈ Ioo 0 a := ⟨half_pos (lt_min ht.1 ha), by
    have := min_le_right t a; simp only [l]; linarith⟩
  have hlt : l < t := by have := min_le_left t a; have := lt_min ht.1 ha; simp only [l]; linarith
  have hu : u ∈ Ioo b 1 := ⟨by have := le_max_right t b; simp only [u]; linarith, by
    have := max_lt ht.2 hb; simp only [u]; linarith⟩
  have htu : t < u := by have := le_max_left t b; have := max_lt ht.2 hb; simp only [u]; linarith
  have h₁ := hasDerivWithinAt_Icc_ite hl.2.le hab (hf l hl) hg hfg
  have hgh' : (if b ≤ a then f b else g b) = h b := by
    split_ifs with hba
    · obtain rfl := le_antisymm hba hab
      rw [hfg, hgh]
    · exact hgh
  exact (hasDerivWithinAt_Icc_ite (hl.2.le.trans hab) hu.1.le h₁ (hh u hu) hgh' t
    ⟨hlt.le, htu.le⟩).hasDerivAt (Icc_mem_nhds hlt htu)

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
  obtain ⟨Φ, hΦa, hΦ⟩ := exists_eq_forall_mem_Icc_hasDerivWithinAt_circleContinuationSlope (δ := δ)
    (r₀ + π / 2 + j * π) ha hb hr (left_mem_Icc.2 hab)
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb hΦ
  rw [abs_of_pos hδ] at hdrift
  have hΦb : |Φ b - (r₁ + π / 2 + k * π)| < π / 2 :=
    calc |Φ b - (r₁ + π / 2 + k * π)| = |(Φ b - Φ a) + (r₀ + j * π - (r₁ + k * π))| := by
          rw [hΦa]; ring_nf
      _ ≤ |Φ b - Φ a| + |r₀ + j * π - (r₁ + k * π)| := abs_add_le _ _
      _ < π / 2 := by linarith
  have hΘ := hasDerivAt_ite_ite (f := fun _ ↦ r₀ + π / 2 + j * π)
    (h := endTrajectory (-δ) (r₁ + π / 2 + k * π) b (Φ b)) ha hab hb
    (fun l hl t ht ↦ (hasDerivAt_const_add_pi_div_two_add_int_mul_pi
      (hr₀ t ⟨hl.1.trans_le ht.1, ht.2⟩) j).hasDerivWithinAt) hΦ
    (fun u hu t ht ↦ by
      rw [circleContinuationSlope_eq_of_add_pi_div_two_add_int_mul_pi
        (hr₁ t ⟨ht.1, ht.2.trans_lt hu.2⟩) k]
      exact (hasDerivAt_endTrajectory _ _ _ _ ⟨(ha.trans_le hab).trans_le ht.1,
        ht.2.trans_lt hu.2⟩).hasDerivWithinAt) hΦa.symm (endTrajectory_self hΦb).symm
  have hlim : Tendsto (fun t ↦ if t ≤ b then (if t ≤ a then r₀ + π / 2 + j * π else Φ t)
      else endTrajectory (-δ) (r₁ + π / 2 + k * π) b (Φ b) t) (𝓝[>] 0)
      (𝓝 (r₀ + π / 2 + j * π)) :=
    tendsto_const_nhds.congr' (eventuallyEq_of_mem (Ioc_mem_nhdsGT ha) fun t ht ↦ by
      simp only [ite_eq_left ht.2, ite_eq_left (ht.2.trans hab)])
  exact ⟨_, hΘ, hlim,
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
  obtain ⟨Φ, hΦb, hΦ⟩ := exists_eq_forall_mem_Icc_hasDerivWithinAt_circleContinuationSlope (δ := δ)
    (r₁ + k * π) ha hb hr (right_mem_Icc.2 hab)
  have hdrift := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb hΦ
  rw [abs_of_pos hδ] at hdrift
  have hΦa : |Φ a - (r₀ + j * π)| < π / 2 :=
    calc |Φ a - (r₀ + j * π)| = |-(Φ b - Φ a) + (r₁ + k * π - (r₀ + j * π))| := by
          rw [hΦb]; ring_nf
      _ ≤ |-(Φ b - Φ a)| + |r₁ + k * π - (r₀ + j * π)| := abs_add_le _ _
      _ < π / 2 := by rw [abs_neg]; linarith
  have hΘ := hasDerivAt_ite_ite (f := endTrajectory δ (r₀ + j * π) a (Φ a))
    (h := fun _ ↦ r₁ + k * π) ha hab hb
    (fun l hl t ht ↦ by
      rw [circleContinuationSlope_eq_of_add_int_mul_pi (hr₀ t ⟨hl.1.trans_le ht.1, ht.2⟩) j]
      exact (hasDerivAt_endTrajectory _ _ _ _ ⟨hl.1.trans_le ht.1,
        ht.2.trans_lt (hab.trans_lt hb)⟩).hasDerivWithinAt) hΦ
    (fun u hu t ht ↦ (hasDerivAt_const_add_int_mul_pi
      (hr₁ t ⟨ht.1, ht.2.trans_lt hu.2⟩) k).hasDerivWithinAt) (endTrajectory_self hΦa) hΦb
  have hlim : Tendsto (fun t ↦ if t ≤ b then (if t ≤ a then endTrajectory δ (r₀ + j * π) a (Φ a) t
      else Φ t) else r₁ + k * π) (𝓝[<] 1) (𝓝 (r₁ + k * π)) :=
    tendsto_const_nhds.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsLT hb) fun t ht ↦ by
      simp only [ite_eq_right (not_le.2 ht.1)])
  exact ⟨_, hΘ,
    tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ hjk hlim, hlim⟩

end Classification

end TauCeti
