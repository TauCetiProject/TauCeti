/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The index-preserving trajectories of a small-amplitude circle continuation

Let `r` be a path of rotations which is constant, `r = r₀`, for `t ≤ a`, and constant,
`r = r₁`, for `t ≥ b`, where `0 < a ≤ b < 1`, and consider the parameter field
`W = 2 δ sin (2 (θ - r t)) ∂_θ + t (1 - t²) ∂_t` of the continuation family
`f_{r(t)} = δ cos (2 (θ - r t))` on the circle (`TauCeti.circleContinuationField`), with `δ > 0`.
Its zeros on the two ends are the critical points of `f_{r₀}` at `t = 0` and of `f_{r₁}` at
`t = 1`: the maxima `r + j π` and the minima `r + π / 2 + j π`. As in
`TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic`, the trajectories of `W` in `0 < t < 1`
are the graphs of the solutions `Θ` of `Θ' = circleContinuationSlope δ r t (Θ t)`, and a
trajectory runs from the zero `(m₀, 0)` to the zero `(m₁, 1)` when `Θ t → m₀` as `t → 0` and
`Θ t → m₁` as `t → 1`.

The continuation map counts the trajectories preserving the Morse index of the end functions:
from a source maximum to a target maximum, and from a source minimum to a target minimum. For the
total field `W` a zero `(m₀, 0)` has index one more than `m₀` has for `f_{r₀}`, and a zero
`(m₁, 1)` has the index of `m₁` for `f_{r₁}`, so these are the trajectories of expected dimension
zero. A trajectory from a source minimum to a target maximum joins two zeros of index one and has
expected dimension `-1`; a transverse parameter field has none. This file classifies these
trajectories when the amplitude is small, in the sense that the drift bound
`2 δ ∫_a^b (t (1 - t²))⁻¹ dt ≤ ε` of `W` across the window `a ≤ t ≤ b` is small.

* **On the ends the equation is solved explicitly.** Where `r = r₀` is constant, `ψ = Θ - m`
  around a critical point `m` of `f_{r₀}` solves `ψ' = ± 2 δ sin (2 ψ) U'` with
  `U t = log t - log (1 - t²) / 2`, so `tan ψ = c e^{± 4 δ U}`. Hence near `t = 0` every
  trajectory within `π / 2` of a maximum converges to it, and only the constant trajectory
  converges to a minimum; near `t = 1`, symmetrically, every trajectory within `π / 2` of a minimum
  converges to it, and only the constant one converges to a maximum.
* **Across the window** the angle moves by at most `ε`
  (`TauCeti.abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope`).

So if a target maximum `m₁` and a source maximum `m₀` satisfy `|m₁ - m₀| + ε < π / 2`, every
trajectory converging to `m₁` is constant on `t ≥ b` and converges at `t = 0` to `m₀`
(`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_circleContinuationSlope`); if a source
minimum `m₀` and a target minimum `m₁` satisfy `|m₁ - m₀| + ε < π / 2`, every trajectory leaving
`m₀` is constant on `t ≤ a` and converges to `m₁`
(`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_circleContinuationSlope`). The separation
bound is a hypothesis of these statements: a small drift alone does not provide such a partner,
but the rotations below do. Given such a pairing, the trajectory exists, and it is unique since a
trajectory is determined by one of its points
(`TauCeti.eqOn_Ioo_of_hasDerivAt_circleContinuationSlope`), so the count of trajectories into
`m₁`, respectively out of `m₀`, is `1` for this pairing and `0` for every other end. No trajectory
runs from a source minimum `m₀` to a target maximum `m₁` with `ε < |m₁ - m₀|`
(`TauCeti.not_tendsto_nhdsGT_zero_and_tendsto_nhdsLT_one_circleContinuationSlope`): when every
source minimum is farther than `ε` from every target maximum, the parameter field has no
connection of expected dimension `-1`, which is what fails for large amplitude in
`TauCeti.exists_circleContinuationField_connection`.

These statements compute the continuations of small amplitude along rotations. For the
half-turn `r₁ = r₀ + π` the end functions agree, and with `ε < π / 2` the trajectory into the
maximum `r₀ + π + j π` comes from the maximum at the same angle, which carries the label `j + 1`
at the source: the continuation map is the identity in the spatial basis of the common end
function, whereas tracking critical points along the path exchanges the two maxima. For a rotation
by `π / 3` and `ε < π / 6`, the trajectory into the maximum `r₀ + π / 3 + j π` comes from
`r₀ + j π`, at distance `π / 3`; for a rotation by `2 π / 3` the one into `r₀ + 2 π / 3 + j π`
comes from `r₀ + (j + 1) π`, again at distance `π / 3`. In the labels `r + j π` that follow the
critical points, each of two successive rotations by `π / 3` therefore has continuation map the
identity, while their concatenation, a single rotation by `2 π / 3` whose variation still lies in
the window, has continuation map the exchange of the two maxima; the same holds for the minima,
and the source minima stay at distance at least `π / 6 > ε` from the target maxima.

## Main results

* `TauCeti.exists_hasDerivAt_circleContinuationSlope`: a trajectory through every point of the
  window.
* `TauCeti.tendsto_nhdsGT_zero_of_abs_sub_lt_pi_div_two_circleContinuationSlope`,
  `TauCeti.tendsto_nhdsLT_one_of_abs_sub_lt_pi_div_two_circleContinuationSlope`: the basins of the
  maxima at `t = 0` and of the minima at `t = 1`.
* `TauCeti.eq_of_tendsto_nhdsGT_zero_circleContinuationSlope`,
  `TauCeti.eq_of_tendsto_nhdsLT_one_circleContinuationSlope`: the trajectories leaving a source
  minimum and entering a target maximum are constant on the ends.
* `TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_circleContinuationSlope`,
  `TauCeti.exists_tendsto_nhdsGT_tendsto_nhdsLT_circleContinuationSlope_of_cos_eq_one`:
  the unique trajectory into a target maximum, given a source maximum `m₀` with
  `|m₁ - m₀| + ε < π / 2`, and its source `m₀`.
* `TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_circleContinuationSlope`,
  `TauCeti.exists_tendsto_nhdsGT_tendsto_nhdsLT_circleContinuationSlope_of_cos_eq_neg_one`:
  the unique trajectory out of a source minimum, given a target minimum `m₁` with
  `|m₁ - m₀| + ε < π / 2`, and its target `m₁`.
* `TauCeti.not_tendsto_nhdsGT_zero_and_tendsto_nhdsLT_one_circleContinuationSlope`: no trajectory
  from a source minimum `m₀` to a target maximum `m₁` with `ε < |m₁ - m₀|`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Real Set Filter Topology

namespace TauCeti

/-! ### The explicit solutions on the ends -/

/-- The time `U t = log t - log (1 - t²) / 2` of the base flow `t' = t (1 - t²)`. -/
private noncomputable def baseTime (t : ℝ) : ℝ := log t - log (1 - t ^ 2) / 2

private theorem hasDerivAt_baseTime {t : ℝ} (h₀ : 0 < t) (h₁ : t < 1) :
    HasDerivAt baseTime (t * (1 - t ^ 2))⁻¹ t := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have h := (hasDerivAt_log h₀.ne').sub
    ((((hasDerivAt_pow 2 t).const_sub 1).log hq.ne').div_const 2)
  refine h.congr_deriv ?_
  field_simp
  ring

private theorem tendsto_baseTime_nhdsGT_zero : Tendsto baseTime (𝓝[>] 0) atBot := by
  have hc : ContinuousAt (fun t : ℝ ↦ log (1 - t ^ 2) / 2) 0 :=
    ((continuousAt_log (by norm_num)).comp (by fun_prop)).div_const 2
  have h : Tendsto (fun t : ℝ ↦ -(log (1 - t ^ 2) / 2)) (𝓝[>] 0) (𝓝 (-(log (1 - 0 ^ 2) / 2))) :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).neg
  exact (tendsto_log_nhdsGT_zero.atBot_add h).congr fun t ↦ by simp [baseTime, sub_eq_add_neg]

private theorem tendsto_baseTime_nhdsLT_one : Tendsto baseTime (𝓝[<] 1) atTop := by
  have hq : Tendsto (fun t : ℝ ↦ 1 - t ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ ↦ 1 - t ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
        (continuous_const.sub (continuous_pow 2)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact show 0 < 1 - t ^ 2 by nlinarith [ht.1, ht.2]
  have h₁ : Tendsto (fun t : ℝ ↦ -(log (1 - t ^ 2) / 2)) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp ((tendsto_log_nhdsGT_zero.comp hq).atBot_div_const two_pos)
  have h₀ : Tendsto log (𝓝[<] 1) (𝓝 (log 1)) :=
    ((continuousAt_log one_ne_zero).tendsto).mono_left nhdsWithin_le_nhds
  exact (h₀.add_atTop h₁).congr fun t ↦ by simp [baseTime, sub_eq_add_neg]

/-- The explicit solution `m + arctan (c e^{4 δ cos (2 (m - r₀)) U t})` of the slope equation
for the constant path `r₀`, around a critical point `m` of `δ cos (2 (θ - r₀))`. -/
private noncomputable def endSolution (δ r₀ m c t : ℝ) : ℝ :=
  m + arctan (c * exp (4 * (δ * cos (2 * (m - r₀))) * baseTime t))

private theorem hasDerivAt_endSolution {δ r₀ m c t : ℝ} (hm : sin (2 * (m - r₀)) = 0)
    (h₀ : 0 < t) (h₁ : t < 1) :
    HasDerivAt (endSolution δ r₀ m c)
      (circleContinuationSlope δ (fun _ ↦ r₀) t (endSolution δ r₀ m c t)) t := by
  set κ := δ * cos (2 * (m - r₀))
  have hy : HasDerivAt (fun t ↦ c * exp (4 * κ * baseTime t))
      (c * (exp (4 * κ * baseTime t) * (4 * κ * (t * (1 - t ^ 2))⁻¹))) t :=
    (((hasDerivAt_baseTime h₀ h₁).const_mul (4 * κ)).exp).const_mul c
  refine (hy.arctan.const_add m).congr_deriv ?_
  set Y := c * exp (4 * κ * baseTime t)
  have hY : 0 < 1 + Y ^ 2 := by positivity
  have hsq := sq_sqrt hY.le
  -- Shift the angle by the critical point `m`, where `sin (2 (m - r₀)) = 0`.
  have hshift : 2 * (endSolution δ r₀ m c t - r₀) = 2 * arctan Y + 2 * (m - r₀) := by
    simp only [endSolution, Y]
    ring
  simp only [circleContinuationSlope_def, hshift, sin_add, hm, mul_zero, add_zero, sin_two_mul,
    sin_arctan, cos_arctan]
  field_simp
  simp only [hsq]
  ring

/-- The explicit solution through the angle `v` at the parameter `t₁`, for `|v - m| < π / 2`. -/
private theorem endSolution_eq {δ r₀ m v t₁ : ℝ} (hv : |v - m| < π / 2) :
    endSolution δ r₀ m
        (tan (v - m) * exp (-(4 * (δ * cos (2 * (m - r₀))) * baseTime t₁))) t₁ = v := by
  have h₁ : -(π / 2) < v - m := by linarith [neg_abs_le (v - m)]
  have h₂ : v - m < π / 2 := by linarith [le_abs_self (v - m)]
  -- The two exponentials cancel, leaving `arctan (tan (v - m)) = v - m`.
  simp [endSolution, mul_assoc, ← exp_add, arctan_tan h₁ h₂]

private theorem tendsto_endSolution {δ r₀ m c : ℝ} {l : Filter ℝ}
    (h : Tendsto (fun t ↦ 4 * (δ * cos (2 * (m - r₀))) * baseTime t) l atBot) :
    Tendsto (endSolution δ r₀ m c) l (𝓝 m) := by
  have h' : Tendsto (fun t ↦ c * exp (4 * (δ * cos (2 * (m - r₀))) * baseTime t)) l (𝓝 (c * 0)) :=
    (tendsto_exp_atBot.comp h).const_mul c
  have h'' := ((continuous_arctan.tendsto _).comp h').const_add m
  rw [mul_zero, arctan_zero, add_zero] at h''
  exact h''

/-- Where the path takes the value `r₀`, its slope is that of the constant path `r₀`. -/
private theorem circleContinuationSlope_of_eq {δ r₀ t θ : ℝ} {r : ℝ → ℝ} (h : r t = r₀) :
    circleContinuationSlope δ r t θ = circleContinuationSlope δ (fun _ ↦ r₀) t θ := by
  simp only [circleContinuationSlope_def, h]

/-! ### Existence of trajectories -/

/-- An explicit solution on the whole of `0 < t < 1` for the constant path `r₀`, through a
prescribed angle at a prescribed parameter. -/
private theorem exists_endSolution (δ r₀ v t₁ : ℝ) :
    ∃ E : ℝ → ℝ, E t₁ = v ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt E (circleContinuationSlope δ (fun _ ↦ r₀) t (E t)) t := by
  -- Use the critical point `m` of `δ cos (2 (θ - r₀))` nearest to `v`, within `π / 4`.
  set m := r₀ + π / 2 * round ((v - r₀) / (π / 2))
  have hπ : 0 < π / 2 := by positivity
  have hm : sin (2 * (m - r₀)) = 0 := by
    rw [show 2 * (m - r₀) = (round ((v - r₀) / (π / 2)) : ℤ) * π by simp only [m]; ring]
    exact sin_int_mul_pi _
  have hv : |v - m| < π / 2 := by
    have h := abs_sub_round ((v - r₀) / (π / 2))
    have : v - m = π / 2 * ((v - r₀) / (π / 2) - round ((v - r₀) / (π / 2))) := by
      simp only [m]; field_simp; ring
    rw [this, abs_mul, abs_of_pos hπ]
    nlinarith
  exact ⟨_, endSolution_eq hv, fun t ht ↦ hasDerivAt_endSolution hm ht.1 ht.2⟩

/-- **Existence of trajectories.** If the path `r` is continuous on a window `[a, b] ⊆ (0, 1)`
and constant on either side of it, then through every point `(θ₀, t₀)` with `t₀` in the window
passes a solution of `Θ' = circleContinuationSlope δ r t (Θ t)` on the whole of `0 < t < 1`. -/
theorem exists_hasDerivAt_circleContinuationSlope {δ r₀ r₁ a b : ℝ} {r : ℝ → ℝ} (ha : 0 < a)
    (hab : a < b) (hb : b < 1) (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ≤ a, r t = r₀)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (θ₀ : ℝ) :
    ∃ Θ : ℝ → ℝ, Θ t₀ = θ₀ ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t := by
  obtain ⟨W, hW₀, hW⟩ := (isPicardLindelof_circleContinuationSlope δ ha hab.le hb hr
    ⟨t₀, ht₀⟩ θ₀).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  obtain ⟨E₀, hE₀, hE₀'⟩ := exists_endSolution δ r₀ (W a) a
  obtain ⟨E₁, hE₁, hE₁'⟩ := exists_endSolution δ r₁ (W b) b
  obtain ⟨Θ, -, hΘW, -, hΘ⟩ := exists_hasDerivAt_circleContinuationSlope_of_window
    (I := Ioo 0 1) hab hE₀ hE₁.symm
    (fun t ht hta ↦ by rw [circleContinuationSlope_of_eq (hr₀ t hta)]; exact hE₀' t ht) hW
    (fun t ht htb ↦ by rw [circleContinuationSlope_of_eq (hr₁ t htb)]; exact hE₁' t ht)
  exact ⟨Θ, by rw [hΘW t₀ ht₀, hW₀], hΘ⟩

/-! ### The ends: basins of the zeros -/

/-- On an interval where the path is constant, a solution through an angle within `π / 2` of a
critical point `m` of `δ cos (2 (θ - r₀))` is the explicit solution around `m`. -/
private theorem eqOn_endSolution {δ r₀ m a b t₁ : ℝ} {r Θ : ℝ → ℝ} (ha : 0 < a) (hb : b < 1)
    (ht₁ : t₁ ∈ Icc a b) (hr : ∀ t ∈ Icc a b, r t = r₀) (hm : sin (2 * (m - r₀)) = 0)
    (hΘ : ∀ t ∈ Icc a b, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hΘm : |Θ t₁ - m| < π / 2) :
    EqOn Θ (endSolution δ r₀ m
      (tan (Θ t₁ - m) * exp (-(4 * (δ * cos (2 * (m - r₀))) * baseTime t₁)))) (Icc a b) := by
  refine eqOn_Icc_of_hasDerivAt_circleContinuationSlope ha hb ht₁ hΘ (fun t ht ↦ ?_)
    (endSolution_eq hΘm).symm
  rw [circleContinuationSlope_of_eq (hr t ht)]
  exact hasDerivAt_endSolution hm (ha.trans_le ht.1) (ht.2.trans_lt hb)

/-- **The basin of a maximum at `t = 0`.** On an interval `0 < t ≤ b₀` where the path is
constant, `r = r₀`, a solution whose angle at `b₀` lies within `π / 2` of a maximum `m` of
`δ cos (2 (θ - r₀))`, `δ > 0`, converges to `m` as `t → 0`. -/
theorem tendsto_nhdsGT_zero_of_abs_sub_lt_pi_div_two_circleContinuationSlope {δ r₀ m b₀ : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 < δ) (hb₀ : 0 < b₀) (hb₀' : b₀ < 1)
    (hr : ∀ t ∈ Ioc 0 b₀, r t = r₀) (hm : cos (2 * (m - r₀)) = 1)
    (hΘ : ∀ t ∈ Ioc 0 b₀, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hΘm : |Θ b₀ - m| < π / 2) : Tendsto Θ (𝓝[>] 0) (𝓝 m) := by
  have hs : sin (2 * (m - r₀)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inl hm)
  have heq : ∀ t ∈ Ioc 0 b₀, Θ t = endSolution δ r₀ m
      (tan (Θ b₀ - m) * exp (-(4 * (δ * cos (2 * (m - r₀))) * baseTime b₀))) t := by
    intro t ht
    have hsub : Icc t b₀ ⊆ Ioc 0 b₀ := fun s hs ↦ ⟨ht.1.trans_le hs.1, hs.2⟩
    exact eqOn_endSolution ht.1 hb₀' ⟨ht.2, le_rfl⟩ (fun s hs' ↦ hr s (hsub hs')) hs
      (fun s hs' ↦ hΘ s (hsub hs')) hΘm ⟨le_rfl, ht.2⟩
  refine (tendsto_endSolution (δ := δ) (r₀ := r₀) (c := tan (Θ b₀ - m) *
    exp (-(4 * (δ * cos (2 * (m - r₀))) * baseTime b₀))) ?_).congr' ?_
  · rw [hm, mul_one]
    exact tendsto_baseTime_nhdsGT_zero.const_mul_atBot (by positivity)
  · filter_upwards [Ioc_mem_nhdsGT hb₀] with t ht
    exact (heq t ht).symm

/-- **The basin of a minimum at `t = 1`.** On an interval `a₀ ≤ t < 1` where the path is
constant, `r = r₁`, a solution whose angle at `a₀` lies within `π / 2` of a minimum `m` of
`δ cos (2 (θ - r₁))`, `δ > 0`, converges to `m` as `t → 1`. -/
theorem tendsto_nhdsLT_one_of_abs_sub_lt_pi_div_two_circleContinuationSlope {δ r₁ m a₀ : ℝ}
    {r Θ : ℝ → ℝ} (hδ : 0 < δ) (ha₀ : 0 < a₀) (ha₀' : a₀ < 1)
    (hr : ∀ t ∈ Ico a₀ 1, r t = r₁) (hm : cos (2 * (m - r₁)) = -1)
    (hΘ : ∀ t ∈ Ico a₀ 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hΘm : |Θ a₀ - m| < π / 2) : Tendsto Θ (𝓝[<] 1) (𝓝 m) := by
  have hs : sin (2 * (m - r₁)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inr hm)
  have heq : ∀ t ∈ Ico a₀ 1, Θ t = endSolution δ r₁ m
      (tan (Θ a₀ - m) * exp (-(4 * (δ * cos (2 * (m - r₁))) * baseTime a₀))) t := by
    intro t ht
    have hsub : Icc a₀ t ⊆ Ico a₀ 1 := fun s hs ↦ ⟨hs.1, hs.2.trans_lt ht.2⟩
    exact eqOn_endSolution ha₀ ht.2 ⟨le_rfl, ht.1⟩ (fun s hs' ↦ hr s (hsub hs')) hs
      (fun s hs' ↦ hΘ s (hsub hs')) hΘm ⟨ht.1, le_rfl⟩
  refine (tendsto_endSolution (δ := δ) (r₀ := r₁) (c := tan (Θ a₀ - m) *
    exp (-(4 * (δ * cos (2 * (m - r₁))) * baseTime a₀))) ?_).congr' ?_
  · rw [hm, show 4 * (δ * -1) = -(4 * δ) by ring]
    exact tendsto_baseTime_nhdsLT_one.const_mul_atTop_of_neg (by linarith)
  · filter_upwards [Ico_mem_nhdsLT ha₀'] with t ht
    exact (heq t ht).symm

/-- The constant angle `m` at a critical point of `δ cos (2 (θ - r₀))` solves the slope
equation wherever the path takes the value `r₀`. -/
private theorem hasDerivAt_const_circleContinuationSlope {δ r₀ m t : ℝ} {r : ℝ → ℝ}
    (hr : r t = r₀) (hm : sin (2 * (m - r₀)) = 0) :
    HasDerivAt (fun _ ↦ m) (circleContinuationSlope δ r t m) t := by
  rw [circleContinuationSlope_eq_zero (by rw [hr]; exact hm)]
  exact hasDerivAt_const t m

/-- **Only the constant trajectory leaves a source minimum.** On an interval `0 < t ≤ b₀` where
the path is constant, `r = r₀`, a solution converging as `t → 0` to a minimum `m` of
`δ cos (2 (θ - r₀))`, `δ > 0`, is constantly `m`. Indeed, a solution which differs from `m` close
to `t = 0` lies there within `π / 2` of one of the neighbouring maxima `m ± π / 2`, and so converges
to it. -/
theorem eq_of_tendsto_nhdsGT_zero_circleContinuationSlope {δ r₀ m b₀ : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hb₀' : b₀ < 1) (hr : ∀ t ∈ Ioc 0 b₀, r t = r₀)
    (hm : cos (2 * (m - r₀)) = -1)
    (hΘ : ∀ t ∈ Ioc 0 b₀, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 m)) : ∀ t ∈ Ioc 0 b₀, Θ t = m := by
  intro t ht
  have hπ : 0 < π / 2 := by positivity
  obtain ⟨s, hs, hsm⟩ := Filter.nonempty_of_mem (inter_mem (Ioc_mem_nhdsGT ht.1)
    (hlim (Ioo_mem_nhds (show m - π / 2 < m by linarith) (show m < m + π / 2 by linarith))))
  have hsub : Ioc 0 s ⊆ Ioc 0 b₀ := fun u hu ↦ ⟨hu.1, hu.2.trans (hs.2.trans ht.2)⟩
  have hsb : s < 1 := hs.2.trans_lt (ht.2.trans_lt hb₀')
  -- A neighbouring maximum `m'` with `Θ s` in its basin would be the limit instead.
  have hne : ∀ m', cos (2 * (m' - r₀)) = 1 → |Θ s - m'| < π / 2 → False := fun m' hm' hsm' ↦ by
    have h := tendsto_nhdsGT_zero_of_abs_sub_lt_pi_div_two_circleContinuationSlope hδ hs.1 hsb
      (fun u hu ↦ hr u (hsub hu)) hm' (fun u hu ↦ hΘ u (hsub hu)) hsm'
    have hmm := tendsto_nhds_unique hlim h
    rw [hmm] at hm
    linarith
  have hΘs : Θ s = m := by
    rcases lt_trichotomy (Θ s) m with h | h | h
    · refine (hne (m - π / 2) ?_ ?_).elim
      · rw [show 2 * (m - π / 2 - r₀) = 2 * (m - r₀) - π by ring, cos_sub_pi, hm, neg_neg]
      · rw [abs_lt]; constructor <;> linarith [hsm.1]
    · exact h
    · refine (hne (m + π / 2) ?_ ?_).elim
      · rw [show 2 * (m + π / 2 - r₀) = 2 * (m - r₀) + π by ring, cos_add_pi, hm, neg_neg]
      · rw [abs_lt]; constructor <;> linarith [hsm.2]
  have hsq : sin (2 * (m - r₀)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inr hm)
  have hIcc : Icc s t ⊆ Ioc 0 b₀ := fun u hu ↦ ⟨hs.1.trans_le hu.1, hu.2.trans ht.2⟩
  exact eqOn_Icc_of_hasDerivAt_circleContinuationSlope hs.1 (ht.2.trans_lt hb₀')
    ⟨le_rfl, hs.2⟩ (fun u hu ↦ hΘ u (hIcc hu))
    (fun u hu ↦ hasDerivAt_const_circleContinuationSlope (hr u (hIcc hu)) hsq) hΘs ⟨hs.2, le_rfl⟩

/-- **Only the constant trajectory enters a target maximum.** On an interval `a₀ ≤ t < 1` where
the path is constant, `r = r₁`, a solution converging as `t → 1` to a maximum `m` of
`δ cos (2 (θ - r₁))`, `δ > 0`, is constantly `m`. -/
theorem eq_of_tendsto_nhdsLT_one_circleContinuationSlope {δ r₁ m a₀ : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (ha₀ : 0 < a₀) (hr : ∀ t ∈ Ico a₀ 1, r t = r₁)
    (hm : cos (2 * (m - r₁)) = 1)
    (hΘ : ∀ t ∈ Ico a₀ 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hlim : Tendsto Θ (𝓝[<] 1) (𝓝 m)) : ∀ t ∈ Ico a₀ 1, Θ t = m := by
  intro t ht
  have hπ : 0 < π / 2 := by positivity
  obtain ⟨s, hs, hsm⟩ := Filter.nonempty_of_mem (inter_mem (Ico_mem_nhdsLT ht.2)
    (hlim (Ioo_mem_nhds (show m - π / 2 < m by linarith) (show m < m + π / 2 by linarith))))
  have hsub : Ico s 1 ⊆ Ico a₀ 1 := fun u hu ↦ ⟨ht.1.trans (hs.1.trans hu.1), hu.2⟩
  have hs₀' : 0 < s := ha₀.trans_le (ht.1.trans hs.1)
  -- A neighbouring minimum `m'` with `Θ s` in its basin would be the limit instead.
  have hne : ∀ m', cos (2 * (m' - r₁)) = -1 → |Θ s - m'| < π / 2 → False := fun m' hm' hsm' ↦ by
    have h := tendsto_nhdsLT_one_of_abs_sub_lt_pi_div_two_circleContinuationSlope hδ hs₀' hs.2
      (fun u hu ↦ hr u (hsub hu)) hm' (fun u hu ↦ hΘ u (hsub hu)) hsm'
    have hmm := tendsto_nhds_unique hlim h
    rw [hmm] at hm
    linarith
  have hΘs : Θ s = m := by
    rcases lt_trichotomy (Θ s) m with h | h | h
    · refine (hne (m - π / 2) ?_ ?_).elim
      · rw [show 2 * (m - π / 2 - r₁) = 2 * (m - r₁) - π by ring, cos_sub_pi, hm]
      · rw [abs_lt]; constructor <;> linarith [hsm.1]
    · exact h
    · refine (hne (m + π / 2) ?_ ?_).elim
      · rw [show 2 * (m + π / 2 - r₁) = 2 * (m - r₁) + π by ring, cos_add_pi, hm]
      · rw [abs_lt]; constructor <;> linarith [hsm.2]
  have hsq : sin (2 * (m - r₁)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inl hm)
  have hIcc : Icc t s ⊆ Ico a₀ 1 := fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.trans_lt hs.2⟩
  exact eqOn_Icc_of_hasDerivAt_circleContinuationSlope (ha₀.trans_le ht.1) hs.2
    ⟨hs.1, le_rfl⟩ (fun u hu ↦ hΘ u (hIcc hu))
    (fun u hu ↦ hasDerivAt_const_circleContinuationSlope (hr u (hIcc hu)) hsq) hΘs ⟨le_rfl, hs.1⟩

/-! ### The trajectories preserving the Morse index -/

section Classification

variable {δ ε r₀ r₁ m₀ m₁ a b : ℝ} {r Θ : ℝ → ℝ}

/-- Across the window `[a, b]` the angle of a trajectory moves by at most the drift bound `ε`. -/
private theorem abs_sub_le_of_hasDerivAt_circleContinuationSlope (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hΘ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) :
    |Θ b - Θ a| ≤ ε := by
  refine (abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb
    fun t ht ↦ (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt).trans ?_
  rwa [abs_of_pos hδ]

/-- **The source of the trajectory into a target maximum.** Let the path be `r₀` for `t ≤ a` and
`r₁` for `t ≥ b`, with `0 < a ≤ b < 1`, and let the drift of the angle across the window `[a, b]`
be at most `ε`. Let `m₁` be a maximum of the target function `δ cos (2 (θ - r₁))`, and let `m₀`
be a maximum of the source function `δ cos (2 (θ - r₀))` with `|m₁ - m₀| + ε < π / 2`; this
separation is assumed, not provided by the drift bound. If a trajectory converges as `t → 1` to
`m₁`, then it converges as `t → 0` to `m₀`. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_circleContinuationSlope (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hm₀ : cos (2 * (m₀ - r₀)) = 1) (hm₁ : cos (2 * (m₁ - r₁)) = 1)
    (hd : |m₁ - m₀| + ε < π / 2)
    (hΘ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hlim : Tendsto Θ (𝓝[<] 1) (𝓝 m₁)) : Tendsto Θ (𝓝[>] 0) (𝓝 m₀) := by
  have h₁ := eq_of_tendsto_nhdsLT_one_circleContinuationSlope hδ (ha.trans_le hab)
    (fun t ht ↦ hr₁ t ht.1) hm₁ (fun t ht ↦ hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩) hlim b
    ⟨le_rfl, hb⟩
  have hw := abs_sub_le_of_hasDerivAt_circleContinuationSlope hδ ha hab hb hε hΘ
  refine tendsto_nhdsGT_zero_of_abs_sub_lt_pi_div_two_circleContinuationSlope hδ ha
    (hab.trans_lt hb) (fun t ht ↦ hr₀ t ht.2) hm₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) ?_
  rw [h₁] at hw
  have h := abs_sub_le (Θ a) m₁ m₀
  rw [abs_sub_comm (Θ a) m₁] at h
  linarith

/-- **The target of the trajectory out of a source minimum.** Let the path be `r₀` for `t ≤ a`
and `r₁` for `t ≥ b`, with `0 < a ≤ b < 1`, and let the drift of the angle across the window
`[a, b]` be at most `ε`. Let `m₀` be a minimum of the source function `δ cos (2 (θ - r₀))`, and
let `m₁` be a minimum of the target function `δ cos (2 (θ - r₁))` with `|m₁ - m₀| + ε < π / 2`;
this separation is assumed, not provided by the drift bound. If a trajectory converges as `t → 0`
to `m₀`, then it converges as `t → 1` to `m₁`. -/
theorem tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_circleContinuationSlope (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hm₀ : cos (2 * (m₀ - r₀)) = -1) (hm₁ : cos (2 * (m₁ - r₁)) = -1)
    (hd : |m₁ - m₀| + ε < π / 2)
    (hΘ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hlim : Tendsto Θ (𝓝[>] 0) (𝓝 m₀)) : Tendsto Θ (𝓝[<] 1) (𝓝 m₁) := by
  have h₀ := eq_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ (hab.trans_lt hb)
    (fun t ht ↦ hr₀ t ht.2) hm₀ (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) hlim a
    ⟨ha, le_rfl⟩
  have hw := abs_sub_le_of_hasDerivAt_circleContinuationSlope hδ ha hab hb hε hΘ
  refine tendsto_nhdsLT_one_of_abs_sub_lt_pi_div_two_circleContinuationSlope hδ
    (ha.trans_le hab) hb (fun t ht ↦ hr₁ t ht.1) hm₁
    (fun t ht ↦ hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩) ?_
  rw [h₀] at hw
  have h := abs_sub_le (Θ b) m₀ m₁
  rw [abs_sub_comm m₀ m₁] at h
  linarith

/-- **No trajectory from a source minimum to a target maximum.** Let the path be `r₀` for `t ≤ a`
and `r₁` for `t ≥ b`, with `0 < a ≤ b < 1`, and let the drift of the angle across the window
`[a, b]` be at most `ε`. Then no trajectory runs from a minimum `m₀` of the source function to a
maximum `m₁` of the target function with `ε < |m₁ - m₀|`: it would be constantly `m₀` on `t ≤ a`
and constantly `m₁` on `t ≥ b`. Both zeros have index one for the total field, so such a
trajectory would have expected dimension `-1`. -/
theorem not_tendsto_nhdsGT_zero_and_tendsto_nhdsLT_one_circleContinuationSlope (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀)
    (hr₁ : ∀ t, b ≤ t → r t = r₁) (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hm₀ : cos (2 * (m₀ - r₀)) = -1) (hm₁ : cos (2 * (m₁ - r₁)) = 1) (hd : ε < |m₁ - m₀|)
    (hΘ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) :
    ¬ (Tendsto Θ (𝓝[>] 0) (𝓝 m₀) ∧ Tendsto Θ (𝓝[<] 1) (𝓝 m₁)) := by
  rintro ⟨hlim₀, hlim₁⟩
  have h₀ := eq_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ (hab.trans_lt hb)
    (fun t ht ↦ hr₀ t ht.2) hm₀ (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) hlim₀ a
    ⟨ha, le_rfl⟩
  have h₁ := eq_of_tendsto_nhdsLT_one_circleContinuationSlope hδ (ha.trans_le hab)
    (fun t ht ↦ hr₁ t ht.1) hm₁ (fun t ht ↦ hΘ t ⟨(ha.trans_le hab).trans_le ht.1, ht.2⟩) hlim₁ b
    ⟨le_rfl, hb⟩
  have hw := abs_sub_le_of_hasDerivAt_circleContinuationSlope hδ ha hab hb hε hΘ
  rw [h₀, h₁] at hw
  linarith

/-- **The trajectory into a target maximum exists.** Under the hypotheses of
`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_circleContinuationSlope`, with `a < b` and a
path continuous on the window, some trajectory runs from the source maximum `m₀` to the target
maximum `m₁`. By `TauCeti.eqOn_Ioo_of_hasDerivAt_circleContinuationSlope` it is unique on
`0 < t < 1`, since every trajectory into `m₁` takes the value `m₁` at `t = b`
(`TauCeti.eq_of_tendsto_nhdsLT_one_circleContinuationSlope`). -/
theorem exists_tendsto_nhdsGT_tendsto_nhdsLT_circleContinuationSlope_of_cos_eq_one
    (hδ : 0 < δ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hm₀ : cos (2 * (m₀ - r₀)) = 1) (hm₁ : cos (2 * (m₁ - r₁)) = 1)
    (hd : |m₁ - m₀| + ε < π / 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[>] 0) (𝓝 m₀) ∧ Tendsto Θ (𝓝[<] 1) (𝓝 m₁) := by
  obtain ⟨Θ, hΘ₀, hΘ⟩ :=
    exists_hasDerivAt_circleContinuationSlope ha hab hb hr hr₀ hr₁ ⟨hab.le, le_rfl⟩ m₁
  have hsq : sin (2 * (m₁ - r₁)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inl hm₁)
  -- On `t ≥ b` the trajectory through `m₁` at `t = b` is constantly `m₁`.
  have hconst : ∀ t ∈ Ico b 1, Θ t = m₁ := fun t ht ↦ by
    have hIcc : Icc b t ⊆ Ico b 1 := fun u hu ↦ ⟨hu.1, hu.2.trans_lt ht.2⟩
    exact eqOn_Icc_of_hasDerivAt_circleContinuationSlope (ha.trans hab) ht.2 ⟨le_rfl, ht.1⟩
      (fun u hu ↦ hΘ u ⟨(ha.trans hab).trans_le (hIcc hu).1, (hIcc hu).2⟩)
      (fun u hu ↦ hasDerivAt_const_circleContinuationSlope (δ := δ) (hr₁ u (hIcc hu).1) hsq) hΘ₀
      ⟨ht.1, le_rfl⟩
  have hlim : Tendsto Θ (𝓝[<] 1) (𝓝 m₁) := tendsto_const_nhds.congr' <| by
    filter_upwards [Ico_mem_nhdsLT hb] with t ht
    exact (hconst t ht).symm
  exact ⟨Θ, hΘ, tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_circleContinuationSlope hδ ha hab.le hb
    hr₀ hr₁ hε hm₀ hm₁ hd hΘ hlim, hlim⟩

/-- **The trajectory out of a source minimum exists.** Under the hypotheses of
`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_circleContinuationSlope`, with `a < b` and a
path continuous on the window, some trajectory runs from the source minimum `m₀` to the target
minimum `m₁`. By `TauCeti.eqOn_Ioo_of_hasDerivAt_circleContinuationSlope` it is unique on
`0 < t < 1`, since every trajectory out of `m₀` takes the value `m₀` at `t = a`
(`TauCeti.eq_of_tendsto_nhdsGT_zero_circleContinuationSlope`). -/
theorem exists_tendsto_nhdsGT_tendsto_nhdsLT_circleContinuationSlope_of_cos_eq_neg_one
    (hδ : 0 < δ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    (hε : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ ≤ ε)
    (hm₀ : cos (2 * (m₀ - r₀)) = -1) (hm₁ : cos (2 * (m₁ - r₁)) = -1)
    (hd : |m₁ - m₀| + ε < π / 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[>] 0) (𝓝 m₀) ∧ Tendsto Θ (𝓝[<] 1) (𝓝 m₁) := by
  obtain ⟨Θ, hΘ₀, hΘ⟩ :=
    exists_hasDerivAt_circleContinuationSlope ha hab hb hr hr₀ hr₁ ⟨le_rfl, hab.le⟩ m₀
  have hsq : sin (2 * (m₀ - r₀)) = 0 := sin_eq_zero_iff_cos_eq.2 (.inr hm₀)
  -- On `t ≤ a` the trajectory through `m₀` at `t = a` is constantly `m₀`.
  have hconst : ∀ t ∈ Ioc 0 a, Θ t = m₀ := fun t ht ↦ by
    have hIcc : Icc t a ⊆ Ioc 0 a := fun u hu ↦ ⟨ht.1.trans_le hu.1, hu.2⟩
    exact eqOn_Icc_of_hasDerivAt_circleContinuationSlope ht.1 (hab.trans hb) ⟨ht.2, le_rfl⟩
      (fun u hu ↦ hΘ u ⟨(hIcc hu).1, (hIcc hu).2.trans_lt (hab.trans hb)⟩)
      (fun u hu ↦ hasDerivAt_const_circleContinuationSlope (δ := δ) (hr₀ u (hIcc hu).2) hsq) hΘ₀
      ⟨le_rfl, ht.2⟩
  have hlim : Tendsto Θ (𝓝[>] 0) (𝓝 m₀) := tendsto_const_nhds.congr' <| by
    filter_upwards [Ioc_mem_nhdsGT ha] with t ht
    exact (hconst t ht).symm
  exact ⟨Θ, hΘ, hlim, tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ ha hab.le
    hb hr₀ hr₁ hε hm₀ hm₁ hd hΘ hlim⟩

end Classification

end TauCeti
