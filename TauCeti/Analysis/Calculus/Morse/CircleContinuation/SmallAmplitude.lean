/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
public import TauCeti.Analysis.Calculus.Morse.ContinuationPotential
public import TauCeti.Dynamics.Flow.TimeDependent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.ODE.ExistUnique

/-!
# Trajectories of small-amplitude circle continuations

A path `t ↦ r(t)` of rotations gives the continuation family `δ cos (2 (θ - r(t)))` on the circle,
with positive parameter field `W = 2 δ sin (2 (θ - r(t))) ∂_θ + t (1 - t²) ∂_t`
(`TauCeti.circleContinuationField`). Let `δ > 0`, and let the path be `r₀` for `t ≤ a` and `r₁` for
`t ≥ b`, where `0 < a ≤ b < 1`. The zeros of `W` at `t = 0` are the maxima `(r₀ + j π, 0)`, of
index `2` for `W`, and the minima `(r₀ + π / 2 + j π, 0)`, of index `1`; at `t = 1` the maxima
`(r₁ + k π, 1)` have index `1` and the minima `(r₁ + π / 2 + k π, 1)` index `0`. The continuation
map counts the unparametrized trajectories of `W` between zeros of the same index: from maxima to
maxima in degree one, and from minima to minima in degree zero. This file computes these counts
when `δ` is small, by the basin of the source or target slice in which a trajectory ends up.

Trajectories are taken in the plane, with lifted angle `θ`
(`TauCeti.circleContinuationTrajectories`). The parameter component of a trajectory from the level
`t = 0` to the level `t = 1` is a time translate of the trajectory `TauCeti.intervalBaseOrbit 1` of
`t' = t (1 - t²)`, so it crosses the window `a ≤ t ≤ b` in the time
`T = ∫_a^b (t (1 - t²))⁻¹ dt`, during which the angle moves by at most `2 δ T`. Outside the window
the slice is fixed, and the angle `ψ` relative to one of its critical points solves
`ψ' = ± 2 δ sin (2 ψ)`, whose solutions in `(-π / 2, π / 2)` are `arctan (c e^{± 4 δ s})`
(`TauCeti.eqOn_arctan_mul_exp_of_hasDerivAt`).

* **Into a target maximum.** The maximum `(r₁ + k π, 1)` repels in the angle, so a trajectory into
  it arrives along the invariant line `θ = r₁ + k π`, and two such trajectories are time translates
  of each other. Followed backwards across the window it drifts by at most `2 δ T`. If
  `|r₁ + k π - (r₀ + j π)| + 2 δ T < π / 2`, it enters the basin of the source maximum `r₀ + j π`
  and converges to it.
* **Out of a source minimum.** Symmetrically, the minimum `(r₀ + π / 2 + j π, 0)` attracts in the
  angle, so the trajectory out of it leaves along `θ = r₀ + π / 2 + j π`, and under the same
  condition it ends at the target minimum `(r₁ + π / 2 + k π, 1)`. In particular no trajectory runs
  from a source minimum to a target maximum, a connection of expected dimension `-1`.

Hence, under the condition, the trajectories from `r₀ + j π` to `r₁ + k π`, and from
`r₀ + π / 2 + j π` to `r₁ + π / 2 + k π`, are the time translates of a single one, and these are
the only trajectories into the target maximum, respectively out of the source minimum. For the
half-turn `r = π ρ` from `δ cos (2 θ)` to the same function, this makes the continuation map the
identity in the fixed bases of critical points, whereas following the critical points along the
path exchanges the two maxima and the two minima.

## Main declarations

* `TauCeti.eqOn_arctan_mul_exp_of_hasDerivAt`, `TauCeti.tendsto_atBot_of_hasDerivAt_sin_two_mul`,
  `TauCeti.eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul` and their mirror images: the
  gradient flow of a slice near a critical point.
* `TauCeti.circleContinuationTrajectories`: the trajectories of `W` between two points.
* `TauCeti.exists_snd_eq_intervalBaseOrbit_of_circleContinuationField` and
  `TauCeti.eq_comp_add_of_circleContinuationField`: trajectories in the open slab follow the base
  orbit, and two of them through the same point are time translates of each other.
* `TauCeti.exists_eq_comp_add_of_mem_circleContinuationTrajectories_int_mul_pi` and
  `TauCeti.eq_of_mem_circleContinuationTrajectories_int_mul_pi`: uniqueness of the trajectory into
  a target maximum, and its source.
* `TauCeti.exists_circleContinuationTrajectories_int_mul_pi_eq_range`: exactly one trajectory
  between paired maxima.
* `TauCeti.exists_eq_comp_add_of_mem_circleContinuationTrajectories_pi_div_two`,
  `TauCeti.eq_of_mem_circleContinuationTrajectories_pi_div_two` and
  `TauCeti.exists_circleContinuationTrajectories_pi_div_two_eq_range`: the same for minima.
* `TauCeti.circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty`: no trajectory from a
  source minimum to a target maximum.
* `TauCeti.exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range` and
  `TauCeti.exists_circleContinuationTrajectories_pi_mul_pi_div_two_eq_range`: the half-turn
  continuation is the identity in the fixed bases.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology
open scoped NNReal

namespace TauCeti

/-! ### The gradient flow of a slice -/

section Slice

variable {κ s₀ : ℝ} {ψ : ℝ → ℝ} {I : Set ℝ}

private theorem sin_two_mul_arctan (x : ℝ) : sin (2 * arctan x) = 2 * x / (1 + x ^ 2) := by
  have h : 0 < 1 + x ^ 2 := by positivity
  rw [sin_two_mul, sin_arctan, cos_arctan]
  field_simp
  rw [sq_sqrt h.le]

/-- **The explicit flow of `ψ' = κ sin (2 ψ)`.** For every `c`, the function
`s ↦ arctan (c e^{2 κ (s - s₀)})` solves `ψ' = κ sin (2 ψ)`: its tangent grows like `e^{2 κ s}`. -/
theorem hasDerivAt_arctan_mul_exp (κ c s₀ s : ℝ) :
    HasDerivAt (fun s ↦ arctan (c * exp (2 * κ * (s - s₀))))
      (κ * sin (2 * arctan (c * exp (2 * κ * (s - s₀))))) s := by
  have he : HasDerivAt (fun s ↦ c * exp (2 * κ * (s - s₀)))
      (c * exp (2 * κ * (s - s₀)) * (2 * κ)) s :=
    ((((hasDerivAt_id' s).sub_const s₀).const_mul (2 * κ)).exp.const_mul c).congr_deriv (by ring)
  refine he.arctan.congr_deriv ?_
  rw [sin_two_mul_arctan]
  field_simp

/-- **The solutions of `ψ' = κ sin (2 ψ)` inside `(-π / 2, π / 2)`.** On a preconnected set `I`,
a solution with `|ψ s₀| < π / 2` at some `s₀ ∈ I` is `arctan (tan (ψ s₀) e^{2 κ (s - s₀)})`. -/
theorem eqOn_arctan_mul_exp_of_hasDerivAt (hI : IsPreconnected I) (hs₀ : s₀ ∈ I)
    (hψ : ∀ s ∈ I, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    EqOn ψ (fun s ↦ arctan (tan (ψ s₀) * exp (2 * κ * (s - s₀)))) I := by
  refine hI.ode_eqOn_of_contDiffAt (V := fun p : ℝ × ℝ ↦ κ * sin (2 * p.2))
    (fun _ _ ↦ by fun_prop) hs₀ ?_ (fun s hs ↦ (hψ s hs).hasDerivWithinAt)
    (fun s _ ↦ (hasDerivAt_arctan_mul_exp κ _ s₀ s).hasDerivWithinAt)
  rw [abs_lt] at h
  simp [arctan_tan h.1 h.2]

/-- A solution of `ψ' = κ sin (2 ψ)` on a preconnected set vanishing at one point vanishes on the
whole set. -/
theorem eqOn_zero_of_hasDerivAt_of_eq_zero (hI : IsPreconnected I) (hs₀ : s₀ ∈ I)
    (hψ : ∀ s ∈ I, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : ψ s₀ = 0) : EqOn ψ 0 I := by
  intro s hs
  rw [eqOn_arctan_mul_exp_of_hasDerivAt hI hs₀ hψ (by rw [h, abs_zero]; positivity) hs]
  simp [h]

/-- **Backward convergence to a maximum.** For `κ > 0`, a solution of `ψ' = κ sin (2 ψ)` for
`s ≤ s₀` with `|ψ s₀| < π / 2` tends to `0` at `-∞`. -/
theorem tendsto_atBot_of_hasDerivAt_sin_two_mul (hκ : 0 < κ)
    (hψ : ∀ s ≤ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    Tendsto ψ atBot (𝓝 0) := by
  have hlin : Tendsto (fun s ↦ 2 * κ * (s - s₀)) atBot atBot := by
    simpa [sub_eq_add_neg] using
      (tendsto_atBot_add_const_right _ (-s₀) tendsto_id).const_mul_atBot (by positivity : 0 < 2 * κ)
  have hlim : Tendsto (fun s ↦ arctan (tan (ψ s₀) * exp (2 * κ * (s - s₀)))) atBot (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_arctan.tendsto _).comp
      ((tendsto_exp_atBot.comp hlin).const_mul (tan (ψ s₀)))
  refine hlim.congr' ?_
  filter_upwards [eventually_le_atBot s₀] with s hs
  exact (eqOn_arctan_mul_exp_of_hasDerivAt isPreconnected_Iic self_mem_Iic hψ h hs).symm

/-- **Forward convergence to a minimum.** For `κ < 0`, a solution of `ψ' = κ sin (2 ψ)` for
`s ≥ s₀` with `|ψ s₀| < π / 2` tends to `0` at `+∞`. -/
theorem tendsto_atTop_of_hasDerivAt_sin_two_mul (hκ : κ < 0)
    (hψ : ∀ s ≥ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    Tendsto ψ atTop (𝓝 0) := by
  have hlin : Tendsto (fun s ↦ 2 * κ * (s - s₀)) atTop atBot := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right _ (-s₀) tendsto_id).const_mul_atTop_of_neg
        (by linarith : 2 * κ < 0)
  have hlim : Tendsto (fun s ↦ arctan (tan (ψ s₀) * exp (2 * κ * (s - s₀)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_arctan.tendsto _).comp
      ((tendsto_exp_atBot.comp hlin).const_mul (tan (ψ s₀)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop s₀] with s hs
  exact (eqOn_arctan_mul_exp_of_hasDerivAt isPreconnected_Ici self_mem_Ici hψ h hs).symm

/-- If `arctan (c e^{2 κ (s - s₁)}) → 0` along a filter on which `κ (s - s₁) ≥ 0` eventually,
then `c = 0`: applying `tan` gives `c e^{2 κ (s - s₁)} → 0`, while `|c| ≤ |c e^{2 κ (s - s₁)}|`. -/
private theorem eq_zero_of_tendsto_arctan_mul_exp {l : Filter ℝ} [l.NeBot] {c s₁ : ℝ}
    (hl : ∀ᶠ s in l, 0 ≤ κ * (s - s₁))
    (h : Tendsto (fun s ↦ arctan (c * exp (2 * κ * (s - s₁)))) l (𝓝 0)) : c = 0 := by
  have ht : Tendsto (fun s ↦ c * exp (2 * κ * (s - s₁))) l (𝓝 0) := by
    have := ((continuousAt_tan.2 (by simp : cos 0 ≠ 0)).tendsto.comp h)
    simpa [Function.comp_def, tan_arctan] using this
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg c))
  refine ge_of_tendsto (by simpa using ht.abs) ?_
  filter_upwards [hl] with s hs
  refine le_mul_of_one_le_right (abs_nonneg c) (one_le_exp ?_)
  rw [mul_assoc]
  positivity

/-- A solution of `ψ' = κ sin (2 ψ)` on a preconnected set `I`, tending to `0` along a filter
eventually in `I` on which `κ (s - s₁) ≥ 0`, vanishes at `s₁` if `|ψ s₁| < π / 2`. -/
private theorem eq_zero_of_tendsto_of_hasDerivAt {l : Filter ℝ} [l.NeBot] {s₁ : ℝ}
    (hI : IsPreconnected I) (hs₁ : s₁ ∈ I) (hψ : ∀ s ∈ I, HasDerivAt ψ (κ * sin (2 * ψ s)) s)
    (hψ₁ : |ψ s₁| < π / 2) (hl : ∀ᶠ s in l, s ∈ I ∧ 0 ≤ κ * (s - s₁))
    (h : Tendsto ψ l (𝓝 0)) : ψ s₁ = 0 := by
  have hc : tan (ψ s₁) = 0 := by
    refine eq_zero_of_tendsto_arctan_mul_exp (hl.mono fun _ hs ↦ hs.2) (h.congr' ?_)
    filter_upwards [hl] with s hs
    exact eqOn_arctan_mul_exp_of_hasDerivAt hI hs₁ hψ hψ₁ hs.1
  rw [abs_lt] at hψ₁
  rw [← arctan_tan hψ₁.1 hψ₁.2, hc, arctan_zero]

/-- A function tending to `0` along `l` takes a value in `(-π / 2, π / 2)` at some point with an
eventual property `P`. -/
private theorem exists_abs_lt_of_tendsto {l : Filter ℝ} [l.NeBot] {P : ℝ → Prop}
    (hP : ∀ᶠ s in l, P s) (h : Tendsto ψ l (𝓝 0)) : ∃ s₁, P s₁ ∧ |ψ s₁| < π / 2 :=
  (hP.and (h.abs.eventually_lt_const (by rw [abs_zero]; positivity))).exists

/-- **Only the constant solution converges forward to a maximum.** For `κ ≥ 0`, a solution of
`ψ' = κ sin (2 ψ)` for `s ≥ s₀` tending to `0` at `+∞` vanishes for `s ≥ s₀`: the maximum `0`
repels every other solution. -/
theorem eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul (hκ : 0 ≤ κ)
    (hψ : ∀ s ≥ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : Tendsto ψ atTop (𝓝 0)) :
    EqOn ψ 0 (Ici s₀) := by
  obtain ⟨s₁, hs₁, hψ₁⟩ := exists_abs_lt_of_tendsto (eventually_ge_atTop s₀) h
  refine eqOn_zero_of_hasDerivAt_of_eq_zero isPreconnected_Ici hs₁ hψ ?_
  refine eq_zero_of_tendsto_of_hasDerivAt isPreconnected_Ici self_mem_Ici
    (fun s hs ↦ hψ s (hs₁.trans hs)) hψ₁ ?_ h
  filter_upwards [eventually_ge_atTop s₁] with s hs
  exact ⟨hs, mul_nonneg hκ (sub_nonneg.2 hs)⟩

/-- **Only the constant solution converges backward to a minimum.** For `κ ≤ 0`, a solution of
`ψ' = κ sin (2 ψ)` for `s ≤ s₀` tending to `0` at `-∞` vanishes for `s ≤ s₀`. -/
theorem eqOn_zero_of_tendsto_atBot_of_hasDerivAt_sin_two_mul (hκ : κ ≤ 0)
    (hψ : ∀ s ≤ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : Tendsto ψ atBot (𝓝 0)) :
    EqOn ψ 0 (Iic s₀) := by
  obtain ⟨s₁, hs₁, hψ₁⟩ := exists_abs_lt_of_tendsto (eventually_le_atBot s₀) h
  refine eqOn_zero_of_hasDerivAt_of_eq_zero isPreconnected_Iic hs₁ hψ ?_
  refine eq_zero_of_tendsto_of_hasDerivAt isPreconnected_Iic self_mem_Iic
    (fun s hs ↦ hψ s (le_trans hs hs₁)) hψ₁ ?_ h
  filter_upwards [eventually_le_atBot s₁] with s hs
  exact ⟨hs, mul_nonneg_of_nonpos_of_nonpos hκ (sub_nonpos.2 hs)⟩

end Slice

/-! ### Trajectories of the parameter field -/

/-- The trajectories of the parameter field `TauCeti.circleContinuationField δ r` from `x` at `-∞`
to `y` at `+∞`, in the coordinates `(θ, t)` with lifted angle `θ`. A trajectory on the cylinder
lifts to the plane; once the lift of its source is fixed, its target lifts to one of the points
`y + (2 π m, 0)`. -/
def circleContinuationTrajectories (δ : ℝ) (r : ℝ → ℝ) (x y : ℝ × ℝ) : Set (ℝ → ℝ × ℝ) :=
  {γ | (∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) ∧ Tendsto γ atBot (𝓝 x) ∧
    Tendsto γ atTop (𝓝 y)}

section Trajectory

variable {δ : ℝ} {r : ℝ → ℝ} {x y : ℝ × ℝ} {γ γ' : ℝ → ℝ × ℝ}

theorem mem_circleContinuationTrajectories :
    γ ∈ circleContinuationTrajectories δ r x y ↔
      (∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) ∧ Tendsto γ atBot (𝓝 x) ∧
        Tendsto γ atTop (𝓝 y) := Iff.rfl

/-- The time translates of a trajectory are trajectories between the same points. -/
theorem comp_add_mem_circleContinuationTrajectories
    (hγ : γ ∈ circleContinuationTrajectories δ r x y) (c : ℝ) :
    (fun s ↦ γ (s + c)) ∈ circleContinuationTrajectories δ r x y :=
  ⟨fun s ↦ (hγ.1 (s + c)).comp_add_const s c,
    hγ.2.1.comp (tendsto_atBot_add_const_right _ c tendsto_id),
    hγ.2.2.comp (tendsto_atTop_add_const_right _ c tendsto_id)⟩

private theorem hasDerivAt_fst_of_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).1) (2 * δ * sin (2 * ((γ s).1 - r (γ s).2))) s := by
  convert ((hγ s).hasFDerivAt.fst).hasDerivAt using 1
  simp

private theorem hasDerivAt_snd_of_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) ((γ s).2 * (1 - (γ s).2 ^ 2)) s := by
  convert ((hγ s).hasFDerivAt.snd).hasDerivAt using 1
  simp

/-- **Trajectories in the open slab follow the base orbit.** If a trajectory of the parameter field
meets the open slab `0 < t < 1`, its parameter component is a time translate of the trajectory
`TauCeti.intervalBaseOrbit 1` of `t' = t (1 - t²)` from `t = 0` to `t = 1`. -/
theorem exists_snd_eq_intervalBaseOrbit_of_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {s₀ : ℝ}
    (hs₀ : (γ s₀).2 ∈ Ioo 0 1) : ∃ c, ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c) := by
  have hτ : ∀ s, HasDerivAt (fun s ↦ (γ s).2) (1 * (γ s).2 * (1 - (γ s).2 ^ 2) - 0) s :=
    fun s ↦ by simpa using hasDerivAt_snd_of_circleContinuationField hγ s
  have hI : ∀ s, (γ s).2 ∈ Ioo 0 1 := fun s ↦
    mapsTo_Ioo_of_hasDerivAt_intervalBase (C := 1) (b := fun _ ↦ 0) one_pos isOpen_univ
      isPreconnected_univ (fun s _ ↦ hτ s) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (mem_univ s₀) hs₀
      (mem_univ s)
  -- The time coordinate advances at unit rate along the parameter component.
  have hU : ∀ s, HasDerivAt (fun s ↦ intervalBaseTimeCoordinate (γ s).2 - s) 0 s := fun s ↦ by
    have := ((hτ s).congr_deriv (sub_zero _)).intervalBaseTimeCoordinate_comp (hI s)
    exact (this.sub (hasDerivAt_id' s)).congr_deriv (sub_self 1)
  refine ⟨intervalBaseTimeCoordinate (γ 0).2, fun s ↦ ?_⟩
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hU s).differentiableAt) (fun s ↦ (hU s).deriv) s 0
  rw [← intervalBaseOrbit_one_intervalBaseTimeCoordinate (hI s)]
  congr 1
  simp only [sub_zero] at hc
  linarith

/-- The angular component `2 δ sin (2 (x - c))` of the field is `4 |δ|`-Lipschitz in the angle. -/
private theorem lipschitzWith_two_mul_sin (δ c : ℝ) :
    LipschitzWith (4 * ‖δ‖₊) fun x ↦ 2 * δ * sin (2 * (x - c)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hs := abs_sin_sub_sin_le (2 * (x - c)) (2 * (y - c))
  rw [show 2 * (x - c) - 2 * (y - c) = 2 * (x - y) by ring, abs_mul, abs_two] at hs
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm, Real.norm_eq_abs]
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_mul, abs_two]
  nlinarith [abs_nonneg δ]

/-- **Uniqueness of trajectories in the open slab.** Two trajectories of the parameter field which
pass through the same point of the open slab `0 < t < 1`, at the times `s₀` and `s₁`, differ by the
time translation `s₁ - s₀`. The path `r` is arbitrary. -/
theorem eq_comp_add_of_circleContinuationField
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s)
    (hγ' : ∀ s, HasDerivAt γ' (circleContinuationField δ r (γ' s)) s) {s₀ s₁ : ℝ}
    (hs₁ : (γ s₁).2 ∈ Ioo 0 1) (h : γ' s₀ = γ s₁) : γ' = fun s ↦ γ (s + (s₁ - s₀)) := by
  set γ₁ : ℝ → ℝ × ℝ := fun s ↦ γ (s + (s₁ - s₀))
  have hγ₁ : ∀ s, HasDerivAt γ₁ (circleContinuationField δ r (γ₁ s)) s := fun s ↦
    (hγ _).comp_add_const s _
  have h₀ : γ₁ s₀ = γ s₁ := by simp [γ₁]
  obtain ⟨c, hc⟩ := exists_snd_eq_intervalBaseOrbit_of_circleContinuationField hγ₁ (s₀ := s₀)
    (by rwa [h₀])
  obtain ⟨c', hc'⟩ := exists_snd_eq_intervalBaseOrbit_of_circleContinuationField hγ' (s₀ := s₀)
    (by rwa [h])
  -- The parameter components are the same translate of the base orbit.
  have hcc : c' = c := by
    have := (strictMono_intervalBaseOrbit one_pos).injective
      (by rw [← hc, ← hc', h, h₀] : intervalBaseOrbit 1 (s₀ + c') = intervalBaseOrbit 1 (s₀ + c))
    linarith
  have hsnd : ∀ s, (γ' s).2 = (γ₁ s).2 := fun s ↦ by rw [hc, hc', hcc]
  -- Along a fixed parameter component the angle solves an equation Lipschitz in the angle.
  have hfst : (fun s ↦ (γ' s).1) = fun s ↦ (γ₁ s).1 :=
    ODE_solution_unique_univ (v := fun s x ↦ 2 * δ * sin (2 * (x - r (γ₁ s).2)))
      (s := fun _ ↦ univ) (fun _ ↦ (lipschitzWith_two_mul_sin δ _).lipschitzOnWith)
      (fun s ↦ ⟨by simpa only [hsnd s] using hasDerivAt_fst_of_circleContinuationField hγ' s,
        mem_univ _⟩)
      (fun s ↦ ⟨hasDerivAt_fst_of_circleContinuationField hγ₁ s, mem_univ _⟩) (t₀ := s₀)
      (by rw [h, h₀])
  funext s
  exact Prod.ext (congrFun hfst s) (hsnd s)

/-- A trajectory from the level `t = 0` to the level `t = 1` follows a translate of the base
orbit. -/
private theorem exists_snd_eq_of_mem_circleContinuationTrajectories {x₀ y₀ : ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ r (x₀, 0) (y₀, 1)) :
    ∃ c, ∀ s, (γ s).2 = intervalBaseOrbit 1 (s + c) := by
  obtain ⟨s₁, hs₁⟩ := (hγ.2.1.snd_nhds.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).exists
  obtain ⟨s₂, hs₂⟩ := (hγ.2.2.snd_nhds.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)).exists
  have hcont : Continuous fun s ↦ (γ s).2 := continuous_iff_continuousAt.2 fun s ↦
    (hasDerivAt_snd_of_circleContinuationField hγ.1 s).continuousAt
  obtain ⟨s₀, hs₀⟩ := intermediate_value_univ s₁ s₂ hcont ⟨hs₁.le, hs₂.le⟩
  refine exists_snd_eq_intervalBaseOrbit_of_circleContinuationField hγ.1 (s₀ := s₀) ?_
  simp only at hs₀
  rw [hs₀]
  norm_num

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
  refine ((hasDerivAt_fst_of_circleContinuationField hγ s).sub_const _).congr_deriv ?_
  rw [hs, show 2 * ((γ s).1 - r₀) = 2 * ((γ s).1 - (r₀ + j * π)) + j * (2 * π) by ring,
    sin_add_int_mul_two_pi]

/-- Where `r = r₀`, the angle relative to the minimum `r₀ + π / 2 + j π` of the slice solves
`ψ' = -2 δ sin (2 ψ)`. -/
private theorem hasDerivAt_fst_sub_pi_div_two
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) {s r₀ : ℝ}
    (hs : r (γ s).2 = r₀) (j : ℤ) :
    HasDerivAt (fun s ↦ (γ s).1 - (r₀ + π / 2 + j * π))
      (-(2 * δ) * sin (2 * ((γ s).1 - (r₀ + π / 2 + j * π)))) s := by
  refine ((hasDerivAt_fst_of_circleContinuationField hγ s).sub_const _).congr_deriv ?_
  rw [hs, show 2 * ((γ s).1 - r₀) = 2 * ((γ s).1 - (r₀ + π / 2 + j * π)) + π + j * (2 * π) by
    ring, sin_add_int_mul_two_pi, sin_add_pi]
  ring

/-- The angle moves at speed at most `2 δ`. -/
private theorem abs_fst_sub_fst_le (hδ : 0 ≤ δ)
    (hγ : ∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) (s s' : ℝ) :
    |(γ s).1 - (γ s').1| ≤ 2 * δ * |s - s'| := by
  have hbound : ∀ u ∈ univ, ‖2 * δ * sin (2 * ((γ u).1 - r (γ u).2))‖ ≤ 2 * δ := fun u _ ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * δ)]
    exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)
  simpa [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ (γ s).1)
    (fun u _ ↦ (hasDerivAt_fst_of_circleContinuationField hγ u).hasDerivWithinAt) hbound
    (mem_univ s') (mem_univ s)

/-- A trajectory of the parameter field through any angle at any time, whose parameter component
is the base orbit `TauCeti.intervalBaseOrbit 1`. It exists for a Lipschitz path `r`, as the
time-dependent flow of the angle equation along the base orbit. -/
private theorem exists_circleContinuationField_fst_eq {L : ℝ≥0} (hr : LipschitzWith L r)
    (s₀ θ₀ : ℝ) : ∃ γ : ℝ → ℝ × ℝ, (∀ s, HasDerivAt γ (circleContinuationField δ r (γ s)) s) ∧
      (∀ s, (γ s).2 = intervalBaseOrbit 1 s) ∧ (γ s₀).1 = θ₀ := by
  set q := intervalBaseOrbit 1
  set v : ℝ → ℝ → ℝ := fun s x ↦ 2 * δ * sin (2 * (x - r (q s)))
  have hR : LipschitzWith L fun s ↦ r (q s) := by
    have := hr.comp (lipschitzWith_intervalBaseOrbit 1)
    rwa [nnNorm_one, mul_one] at this
  -- The suspension `(s, x) ↦ (1, v s x)` is Lipschitz, with constant `4 |δ| (1 + L)`.
  have hv : LipschitzWith (4 * ‖δ‖₊ * (1 + L)) (timeDependentSuspension v) := by
    refine LipschitzWith.of_dist_le_mul fun p p' ↦ ?_
    obtain ⟨t, x⟩ := p
    obtain ⟨t', x'⟩ := p'
    have h1 := hR.dist_le_mul t t'
    have hs := abs_sin_sub_sin_le (2 * (x - r (q t))) (2 * (x' - r (q t')))
    have h2 : |2 * (x - r (q t)) - 2 * (x' - r (q t'))| ≤
        2 * (|x - x'| + |r (q t) - r (q t')|) := by
      rw [show 2 * (x - r (q t)) - 2 * (x' - r (q t')) = 2 * ((x - x') - (r (q t) - r (q t'))) by
        ring, abs_mul, abs_two]
      gcongr
      exact abs_sub _ _
    simp only [timeDependentSuspension_apply, Prod.dist_eq, dist_self, NNReal.coe_mul,
      NNReal.coe_ofNat, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_one, v] at h1 ⊢
    rw [Real.dist_eq, Real.dist_eq] at h1
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_mul, abs_two]
    refine max_le (by positivity) ?_
    have ht : |t - t'| ≤ max |t - t'| |x - x'| := le_max_left _ _
    have hx : |x - x'| ≤ max |t - t'| |x - x'| := le_max_right _ _
    have hL : (L : ℝ) * |t - t'| ≤ L * max |t - t'| |x - x'| := by gcongr
    calc 2 * |δ| * |sin (2 * (x - r (q t))) - sin (2 * (x' - r (q t')))|
        ≤ 2 * |δ| * (2 * (|x - x'| + L * |t - t'|)) := by
          gcongr
          exact hs.trans (h2.trans (by gcongr))
      _ ≤ 2 * |δ| * (2 * (max |t - t'| |x - x'| + L * max |t - t'| |x - x'|)) := by gcongr
      _ = 4 * |δ| * (1 + L) * max |t - t'| |x - x'| := by ring
  refine ⟨fun s ↦ (timeDependentFlow v hv s₀ s θ₀, q s), fun s ↦ ?_, fun _ ↦ rfl,
    timeDependentFlow_self v hv s₀ θ₀⟩
  convert (hasDerivAt_timeDependentFlow v hv s₀ s θ₀).prodMk (hasDerivAt_intervalBaseOrbit 1 s)
    using 1
  simp [v, q]

variable {a b r₀ r₁ c : ℝ}

/-- The length `∫_a^b (t (1 - t²))⁻¹ dt` of the time window in which the parameter runs from `a`
to `b` is `U b - U a`, for the time coordinate `U`. -/
private theorem integral_inv_mul_one_sub_sq (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ =
      intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a := by
  have hmem : ∀ t ∈ uIcc a b, t ∈ Ioo (0 : ℝ) 1 := fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_intervalBaseTimeCoordinate (hmem t ht))
    (ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) fun t ht ↦ ?_))
  exact (mul_pos (hmem t ht).1 (by nlinarith [(hmem t ht).1, (hmem t ht).2])).ne'

private theorem intervalBaseTimeCoordinate_le (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    intervalBaseTimeCoordinate a ≤ intervalBaseTimeCoordinate b :=
  strictMonoOn_intervalBaseTimeCoordinate.monotoneOn ⟨ha, hab.trans_lt hb⟩
    ⟨ha.trans_le hab, hb⟩ hab

/-- **A trajectory into a target maximum arrives along the invariant line.** If the angle tends
to the maximum `r₁ + k π` of the target slice, then it equals `r₁ + k π` from the time `U b - c` on,
since the maximum repels every other solution. -/
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
  have hz := eqOn_zero_of_hasDerivAt_of_eq_zero isPreconnected_Ici self_mem_Ici
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
  have hdrift := abs_fst_sub_fst_le hδ.le hγ (intervalBaseTimeCoordinate a - c)
    (intervalBaseTimeCoordinate b - c)
  rw [show intervalBaseTimeCoordinate a - c - (intervalBaseTimeCoordinate b - c) =
    -(intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a) by ring, abs_neg,
    abs_of_nonneg (sub_nonneg.2 hab)] at hdrift
  have h₀ : |(γ (intervalBaseTimeCoordinate a - c)).1 - (r₀ + j * π)| < π / 2 :=
    (abs_sub_le _ (γ (intervalBaseTimeCoordinate b - c)).1 _).trans_lt (by linarith)
  have := tendsto_atBot_of_hasDerivAt_sin_two_mul (by positivity)
    (fun s hs ↦ hasDerivAt_fst_sub_int_mul_pi hγ (apply_snd_eq_of_le hc ha hr₀ hs) j) h₀
  simpa using this.add_const (r₀ + j * π)

/-- **A trajectory out of a source minimum leaves along the invariant line.** If the angle tends to
the minimum `r₀ + π / 2 + j π` of the source slice at `-∞`, then it equals `r₀ + π / 2 + j π` up to
the time `U a - c`, since the minimum attracts every nearby solution. -/
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
  have hz := eqOn_zero_of_hasDerivAt_of_eq_zero isPreconnected_Iic self_mem_Iic
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
  have hdrift := abs_fst_sub_fst_le hδ.le hγ (intervalBaseTimeCoordinate b - c)
    (intervalBaseTimeCoordinate a - c)
  rw [show intervalBaseTimeCoordinate b - c - (intervalBaseTimeCoordinate a - c) =
    intervalBaseTimeCoordinate b - intervalBaseTimeCoordinate a by ring,
    abs_of_nonneg (sub_nonneg.2 hab)] at hdrift
  have h₀ : |(γ (intervalBaseTimeCoordinate b - c)).1 - (r₁ + π / 2 + k * π)| < π / 2 :=
    (abs_sub_le _ (γ (intervalBaseTimeCoordinate a - c)).1 _).trans_lt (by linarith)
  have := tendsto_atTop_of_hasDerivAt_sin_two_mul (by linarith)
    (fun s hs ↦ hasDerivAt_fst_sub_pi_div_two hγ (apply_snd_eq_of_ge hc hb hr₁ hs) k) h₀
  simpa using this.add_const (r₁ + π / 2 + k * π)

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
  obtain ⟨c', hc'⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ'
  -- Work on the window `t ≥ max b (1 / 2)`, which lies in the open slab.
  set b' := max b (1 / 2)
  have hb' : b' ∈ Ioo 0 1 := ⟨lt_max_of_lt_right (by norm_num), max_lt hb (by norm_num)⟩
  have hr₁' : ∀ t, b' ≤ t → r t = r₁ := fun t ht ↦ hr₁ t ((le_max_left _ _).trans ht)
  have h₁ := fst_eq_of_tendsto_atTop_int_mul_pi hδ hb' hr₁' hγ.1 hc hγ.2.2.fst_nhds
  have h₂ := fst_eq_of_tendsto_atTop_int_mul_pi hδ hb' hr₁' hγ'.1 hc' hγ'.2.2.fst_nhds
  have hτ : ∀ c'', intervalBaseOrbit 1 (intervalBaseTimeCoordinate b' - c'' + c'') = b' :=
    fun _ ↦ by rw [sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate hb']
  exact ⟨_, eq_comp_add_of_circleContinuationField hγ.1 hγ'.1 (by rw [hc, hτ]; exact hb')
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
  have h₁ := fst_eq_of_tendsto_atTop_int_mul_pi hδ.le ⟨ha.trans_le hab, hb⟩ hr₁ hγ.1 hc
    hγ.2.2.fst_nhds
  rw [integral_inv_mul_one_sub_sq ha hab hb, ← h₁] at hjk
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
  rw [integral_inv_mul_one_sub_sq ha hab hb] at hjk
  refine ⟨γ, hγ, ?_, ?_⟩
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
  obtain ⟨c', hc'⟩ := exists_snd_eq_of_mem_circleContinuationTrajectories hγ'
  -- Work on the window `t ≤ min a (1 / 2)`, whose upper end lies in the open slab.
  set a' := min a (1 / 2)
  have ha' : a' ∈ Ioo 0 1 := ⟨lt_min ha (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  have hr₀' : ∀ t ≤ a', r t = r₀ := fun t ht ↦ hr₀ t (ht.trans (min_le_left _ _))
  have h₁ := fst_eq_of_tendsto_atBot_pi_div_two hδ ha' hr₀' hγ.1 hc hγ.2.1.fst_nhds
  have h₂ := fst_eq_of_tendsto_atBot_pi_div_two hδ ha' hr₀' hγ'.1 hc' hγ'.2.1.fst_nhds
  have hτ : ∀ c'', intervalBaseOrbit 1 (intervalBaseTimeCoordinate a' - c'' + c'') = a' :=
    fun _ ↦ by rw [sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate ha']
  exact ⟨_, eq_comp_add_of_circleContinuationField hγ.1 hγ'.1 (by rw [hc, hτ]; exact ha')
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
  have h₁ := fst_eq_of_tendsto_atBot_pi_div_two hδ.le ⟨ha, hab.trans_lt hb⟩ hr₀ hγ.1 hc
    hγ.2.1.fst_nhds
  rw [integral_inv_mul_one_sub_sq ha hab hb] at hjk
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
  rw [integral_inv_mul_one_sub_sq ha hab hb] at hjk
  refine ⟨γ, hγ, ?_, ?_⟩
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

/-- **No trajectory from a source minimum to a target maximum.** Under the hypotheses of
`TauCeti.eq_of_mem_circleContinuationTrajectories_pi_div_two`, there is no trajectory from the
source minimum `(r₀ + π / 2 + j π, 0)`, of index one, to any target maximum `(r₁ + m π, 1)`, also
of index one. Such a connection would have expected dimension `-1`, so its absence is part of the
transversality of the parameter field. -/
theorem circleContinuationTrajectories_pi_div_two_int_mul_pi_eq_empty (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ≤ a, r t = r₀) (hr₁ : ∀ t, b ≤ t → r t = r₁)
    {j k : ℤ} (hjk : |r₁ + k * π - (r₀ + j * π)| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (m : ℤ) :
    circleContinuationTrajectories δ r (r₀ + π / 2 + j * π, 0) (r₁ + m * π, 1) = ∅ := by
  refine eq_empty_of_forall_notMem fun γ hγ ↦ ?_
  have h := eq_of_mem_circleContinuationTrajectories_pi_div_two hδ ha hab hb hr₀ hr₁ hjk hγ
  have h2 : ((2 * (m - k) : ℤ) : ℝ) * π = (1 : ℤ) * π := by push_cast; linarith
  have := Int.cast_injective (α := ℝ) (mul_right_cancel₀ pi_ne_zero h2)
  omega

end Trajectory

/-! ### The half-turn: continuation is not critical-point tracking -/

section HalfTurn

variable {ρ : ℝ → ℝ} {L : ℝ≥0}

/-- The half-turn path `π ρ` is `0` before `1/6`, `π` after `5/6`, and Lipschitz. -/
private theorem pi_mul_hyps (hρ : LipschitzWith L ρ) (h0 : ∀ t ≤ 1 / 6, ρ t = 0)
    (h1 : ∀ t, 5 / 6 ≤ t → ρ t = 1) :
    (∀ t ≤ 1 / 6, π * ρ t = 0) ∧ (∀ t, 5 / 6 ≤ t → π * ρ t = π) ∧
      LipschitzWith (‖π‖₊ * L) fun t ↦ π * ρ t :=
  ⟨fun t ht ↦ by rw [h0 t ht, mul_zero], fun t ht ↦ by rw [h1 t ht, mul_one],
    (lipschitzWith_smul π).comp hρ⟩

/-- With the source label `j = k` and the target label `k - 1`, the two maxima of the half-turn are
the same lifted angle `k π`, and the window condition reduces to the drift bound. -/
private theorem pi_mul_hjk {δ : ℝ} (k : ℤ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2) :
    |π + ((k - 1 : ℤ) : ℝ) * π - (0 + k * π)| +
      2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2 := by
  rwa [show π + ((k - 1 : ℤ) : ℝ) * π - (0 + k * π) = 0 by push_cast; ring, abs_zero, zero_add]

/-- **The half-turn continuation is the identity on maxima.** Let `ρ` be Lipschitz, `0` for
`t ≤ 1/6` and `1` for `t ≥ 5/6`, so that the half-turn path `π ρ` goes from `δ cos (2 θ)` to the
same function `δ cos (2 (θ - π))`, and let `δ > 0` satisfy `2 δ T < π / 2` with
`T = ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt`. Then the trajectories from the maximum `(k π, 0)` to the
maximum `(k π, 1)` at the same lifted angle are the time translates of a single one. So in the
fixed basis of maxima of the common end function the continuation map is the identity, whereas
following the maximum `k π` of `δ cos (2 (θ - π ρ(t)))` along `t` ends at `k π + π`, the other
maximum. -/
theorem exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range {δ : ℝ} (hδ : 0 < δ)
    (hρ : LipschitzWith L ρ) (h0 : ∀ t ≤ 1 / 6, ρ t = 0) (h1 : ∀ t, 5 / 6 ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2) (k : ℤ) :
    ∃ γ : ℝ → ℝ × ℝ, circleContinuationTrajectories δ (fun t ↦ π * ρ t) (k * π, 0) (k * π, 1) =
      range fun c s ↦ γ (s + c) := by
  obtain ⟨hr₀, hr₁, hr⟩ := pi_mul_hyps hρ h0 h1
  have h := exists_circleContinuationTrajectories_int_mul_pi_eq_range hδ (by norm_num)
    (by norm_num) (by norm_num) hr₀ hr₁ hr (pi_mul_hjk k hT)
  rwa [show π + ((k - 1 : ℤ) : ℝ) * π = k * π by push_cast; ring, zero_add] at h

/-- For the half-turn continuation, every trajectory from the source level into the maximum
`(k π, 1)` starts at the maximum `(k π, 0)` at the same lifted angle. -/
theorem eq_of_mem_circleContinuationTrajectories_pi_mul_int_mul_pi {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ t ≤ 1 / 6, ρ t = 0) (h1 : ∀ t, 5 / 6 ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2) {k : ℤ} {x : ℝ}
    {γ : ℝ → ℝ × ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ (fun t ↦ π * ρ t) (x, 0) (k * π, 1)) :
    x = k * π := by
  have e : k * π = π + ((k - 1 : ℤ) : ℝ) * π := by push_cast; ring
  rw [e] at hγ
  have := eq_of_mem_circleContinuationTrajectories_int_mul_pi hδ (by norm_num) (by norm_num)
    (by norm_num) (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one])
    (pi_mul_hjk k hT) hγ
  rw [this, zero_add]

/-- **The half-turn continuation is the identity on minima.** Under the hypotheses of
`TauCeti.exists_circleContinuationTrajectories_pi_mul_int_mul_pi_eq_range`, the trajectories from
the minimum `(π / 2 + k π, 0)` to the minimum `(π / 2 + k π, 1)` at the same lifted angle are the
time translates of a single one, whereas following the minimum along the path ends at the other
minimum `π / 2 + k π + π`. -/
theorem exists_circleContinuationTrajectories_pi_mul_pi_div_two_eq_range {δ : ℝ} (hδ : 0 < δ)
    (hρ : LipschitzWith L ρ) (h0 : ∀ t ≤ 1 / 6, ρ t = 0) (h1 : ∀ t, 5 / 6 ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2) (k : ℤ) :
    ∃ γ : ℝ → ℝ × ℝ, circleContinuationTrajectories δ (fun t ↦ π * ρ t) (π / 2 + k * π, 0)
      (π / 2 + k * π, 1) = range fun c s ↦ γ (s + c) := by
  obtain ⟨hr₀, hr₁, hr⟩ := pi_mul_hyps hρ h0 h1
  have h := exists_circleContinuationTrajectories_pi_div_two_eq_range hδ (by norm_num)
    (by norm_num) (by norm_num) hr₀ hr₁ hr (pi_mul_hjk k hT)
  rwa [show π + π / 2 + ((k - 1 : ℤ) : ℝ) * π = π / 2 + k * π by push_cast; ring,
    zero_add] at h

/-- For the half-turn continuation, every trajectory from the minimum `(π / 2 + k π, 0)` to the
target level ends at the minimum `(π / 2 + k π, 1)` at the same lifted angle; in particular it
does not end at a maximum. -/
theorem eq_of_mem_circleContinuationTrajectories_pi_mul_pi_div_two {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ t ≤ 1 / 6, ρ t = 0) (h1 : ∀ t, 5 / 6 ≤ t → ρ t = 1)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 2) {k : ℤ} {y : ℝ}
    {γ : ℝ → ℝ × ℝ}
    (hγ : γ ∈ circleContinuationTrajectories δ (fun t ↦ π * ρ t) (π / 2 + k * π, 0) (y, 1)) :
    y = π / 2 + k * π := by
  rw [show π / 2 + k * π = 0 + π / 2 + k * π by ring] at hγ
  have := eq_of_mem_circleContinuationTrajectories_pi_div_two hδ (by norm_num) (by norm_num)
    (by norm_num) (fun t ht ↦ by rw [h0 t ht, mul_zero]) (fun t ht ↦ by rw [h1 t ht, mul_one])
    (pi_mul_hjk k hT) hγ
  rw [this]
  push_cast
  ring

end HalfTurn

end TauCeti
