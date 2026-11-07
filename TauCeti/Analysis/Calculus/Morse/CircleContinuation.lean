/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The parameter field of a continuation of `δ cos (2 (θ - r))` on the circle

On the circle with angle `θ`, the functions `f_r(θ) = δ cos (2 (θ - r))` have maxima at
`r + j π` and minima at `r + π / 2 + j π`, and their negative gradient for the metric `dθ²` is
`2 δ sin (2 (θ - r)) ∂_θ`. A path `t ↦ r(t)` of rotations gives the continuation family `f_{r(t)}`,
and its positive parameter field on the cylinder `(θ, t)`, `0 < t < 1`, is

`W = 2 δ sin (2 (θ - r(t))) ∂_θ + t (1 - t²) ∂_t`

(`TauCeti.circleContinuationField`). Its zeros at `t = 0` and `t = 1` are the critical points of
the end functions, and the counts of its trajectories between them define the continuation map.
This family is the source of the circle continuation counterexamples of Morse homology: tracking
critical points along a path need not agree with the continuation map, and a path all of whose
slices are Morse–Smale need not give a transverse parameter field.

Since `t` increases along `W`, its trajectories in `0 < t < 1` are graphs of functions `Θ` of `t`
solving `Θ' = 2 δ sin (2 (Θ - r t)) / (t (1 - t²))` (`TauCeti.circleContinuationSlope`). This
file works with these graphs, and `TauCeti.hasDerivAt_circleContinuationField` turns such a graph
back into a trajectory of `W`. It proves the three dynamical facts about this equation used by the
counterexamples.

* **Drift bound.** Along any trajectory, between the levels `a` and `b` of `t` the angle moves by
  at most `2 δ ∫_a^b (t (1 - t²))⁻¹ dt`, whatever the path `r`
  (`TauCeti.abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope`). On the window
  `1/6 ≤ t ≤ 5/6` containing all variation of the paths, this makes the transition map move every
  lifted angle by less than `π / 12` once `2 δ T < π / 12`.
* **Trapping.** For `r = π ρ` with `ρ` nondecreasing, the relative angle `ψ = θ - π ρ(t)` solves
  `ψ' = 2 δ sin (2 ψ) / (t (1 - t²)) - π ρ'(t)`. When `2 δ > π ρ'(t) t (1 - t²)`, the strip
  `π / 4 ≤ ψ ≤ π / 2` is invariant (`TauCeti.mem_Icc_of_hasDerivWithinAt_circleContinuationSlope`).
* **A non-transverse connection.** For the half-turn `r = π ρ`, where `ρ` is `C¹`,
  nondecreasing, `0` for `t ≤ 1/3` and `1` for `t ≥ 2/3`, some `δ > 0` gives a trajectory of `W`
  from the minimum `(π / 2, 0)` of the source function to the maximum `(π, 1)` of the target
  function (`TauCeti.exists_circleContinuationField_connection`). For `δ = 0` the trajectory
  leaving the source minimum ends at angle `π / 2`, while for large `δ` the trapping keeps its
  relative angle at least `π / 4`, so it ends above `π`; the angle at `t = 5/6` depends
  continuously on `δ`
  (`TauCeti.abs_sub_le_gronwallBound_of_hasDerivWithinAt_circleContinuationSlope`), and the
  intermediate value theorem gives an exact hit. Both ends are zeros of `W` with a
  one-dimensional unstable manifold: the linearization of `W` is `diag(-4 δ, 1)` at the source
  minimum and `diag(4 δ, -2)` at the target maximum
  (`TauCeti.hasFDerivAt_circleContinuationField_pi_div_two_zero`,
  `TauCeti.hasFDerivAt_circleContinuationField_pi_one`). A connection between two zeros of the
  same index has expected dimension `-1`, so `W` is not transverse, although every slice
  `f_{r(t)}` is a Morse function whose gradient flow on the circle is Morse–Smale.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology
open scoped NNReal

namespace TauCeti

/-- The angular velocity per unit of the parameter `t` of the parameter field of the continuation
family `δ cos (2 (θ - r t))`: `2 δ sin (2 (θ - r t)) / (t (1 - t²))`. The graph of a solution of
`Θ' = circleContinuationSlope δ r t (Θ t)` is a trajectory of `TauCeti.circleContinuationField`
(`TauCeti.hasDerivAt_circleContinuationField`). -/
noncomputable def circleContinuationSlope (δ : ℝ) (r : ℝ → ℝ) (t θ : ℝ) : ℝ :=
  2 * δ * sin (2 * (θ - r t)) / (t * (1 - t ^ 2))

/-- The positive parameter field `2 δ sin (2 (θ - r t)) ∂_θ + t (1 - t²) ∂_t` of the continuation
family `δ cos (2 (θ - r t))` on the circle, in the coordinates `(θ, t)` with lifted angle `θ`. -/
noncomputable def circleContinuationField (δ : ℝ) (r : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (2 * δ * sin (2 * (x.1 - r x.2)), x.2 * (1 - x.2 ^ 2))

theorem circleContinuationSlope_def (δ : ℝ) (r : ℝ → ℝ) (t θ : ℝ) :
    circleContinuationSlope δ r t θ = 2 * δ * sin (2 * (θ - r t)) / (t * (1 - t ^ 2)) := (rfl)

@[simp]
theorem circleContinuationField_apply (δ : ℝ) (r : ℝ → ℝ) (θ t : ℝ) :
    circleContinuationField δ r (θ, t) = (2 * δ * sin (2 * (θ - r t)), t * (1 - t ^ 2)) := (rfl)

/-- The coefficient `t (1 - t²)` of `∂_t` is positive for `0 < t < 1`. -/
private theorem baseSpeed_pos {t : ℝ} (h₀ : 0 < t) (h₁ : t < 1) : 0 < t * (1 - t ^ 2) := by
  have : t ^ 2 < 1 := by nlinarith
  positivity

/-- On the window `1/3 ≤ t ≤ 5/6` the coefficient `t (1 - t²)` stays above `1/4`. -/
private theorem quarter_le_baseSpeed {t : ℝ} (h₀ : 1 / 3 ≤ t) (h₁ : t ≤ 5 / 6) :
    1 / 4 ≤ t * (1 - t ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 h₀) (sub_nonneg.2 h₁)]

/-- The graph of a solution of `Θ' = circleContinuationSlope δ r t (Θ t)`, followed along a
solution of `t' = t (1 - t²)` in `0 < t < 1`, is a trajectory of the parameter field. -/
theorem hasDerivAt_circleContinuationField {δ : ℝ} {r Θ τ : ℝ → ℝ} {s : ℝ}
    (hτ : HasDerivAt τ (τ s * (1 - τ s ^ 2)) s) (hτ₀ : 0 < τ s) (hτ₁ : τ s < 1)
    (hΘ : HasDerivAt Θ (circleContinuationSlope δ r (τ s) (Θ (τ s))) (τ s)) :
    HasDerivAt (fun s ↦ (Θ (τ s), τ s))
      (circleContinuationField δ r (Θ (τ s), τ s)) s := by
  have hm := (baseSpeed_pos hτ₀ hτ₁).ne'
  have hv : circleContinuationField δ r (Θ (τ s), τ s) =
      (circleContinuationSlope δ r (τ s) (Θ (τ s)) * (τ s * (1 - τ s ^ 2)),
        τ s * (1 - τ s ^ 2)) := by
    rw [circleContinuationField_apply, circleContinuationSlope_def, div_mul_cancel₀ _ hm]
  rw [hv]
  exact (hΘ.comp s hτ).prodMk hτ

/-- An antiderivative of `(t (1 - t²))⁻¹` on `0 < t < 1`. -/
private noncomputable def baseTime (t : ℝ) : ℝ := log t - log (1 - t ^ 2) / 2

private theorem hasDerivAt_baseTime {t : ℝ} (h₀ : 0 < t) (h₁ : t < 1) :
    HasDerivAt baseTime (t * (1 - t ^ 2))⁻¹ t := by
  have h2 : 0 < 1 - t ^ 2 := by nlinarith
  have hd : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have h := (hasDerivAt_log h₀.ne').sub ((hd.log h2.ne').div_const 2)
  unfold baseTime
  refine h.congr_deriv ?_
  field_simp
  ring

private theorem integral_inv_baseSpeed {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ = baseTime b - baseTime a := by
  have hmem : ∀ t ∈ uIcc a b, 0 < t ∧ t < 1 := fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_baseTime (hmem t ht).1 (hmem t ht).2) ?_
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  have hc : ContinuousAt (fun t : ℝ ↦ t * (1 - t ^ 2)) t := by fun_prop
  exact (hc.inv₀ (baseSpeed_pos (hmem t ht).1 (hmem t ht).2).ne').continuousWithinAt

/-- The slope is bounded by `2 |δ| / (t (1 - t²))`. -/
private theorem abs_circleContinuationSlope_le (δ : ℝ) (r : ℝ → ℝ) {t : ℝ} (h₀ : 0 < t)
    (h₁ : t < 1) (θ : ℝ) :
    |circleContinuationSlope δ r t θ| ≤ 2 * |δ| * (t * (1 - t ^ 2))⁻¹ := by
  have hm := baseSpeed_pos h₀ h₁
  rw [circleContinuationSlope_def, abs_div, abs_of_pos hm, div_eq_mul_inv]
  gcongr
  rw [abs_mul, abs_mul, abs_two]
  exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)

/-- **Drift bound for the continuation trajectories.** Along a solution of
`Θ' = circleContinuationSlope δ r t (Θ t)` on `[a, b] ⊆ (0, 1)`, the angle moves by at most
`2 |δ| ∫_a^b (t (1 - t²))⁻¹ dt`, for every path `r`. -/
theorem abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope {δ : ℝ} {r Θ : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hΘ : ∀ t ∈ Icc a b, HasDerivWithinAt Θ (circleContinuationSlope δ r t (Θ t)) (Icc a b) t) :
    |Θ b - Θ a| ≤ 2 * |δ| * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ := by
  have hmem : ∀ t ∈ Icc a b, 0 < t ∧ t < 1 := fun t ht ↦ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  rw [integral_inv_baseSpeed ha hab hb]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t ↦ Θ t - Θ a) (B := fun t ↦ 2 * |δ| * (baseTime t - baseTime a))
    (f' := fun t ↦ circleContinuationSlope δ r t (Θ t))
    (B' := fun t ↦ 2 * |δ| * (t * (1 - t ^ 2))⁻¹)
    (fun t ht ↦ ((hΘ t ht).continuousWithinAt.sub continuousWithinAt_const))
    (fun t ht ↦ ((hΘ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)).sub_const _)
    (by simp)
    (fun t ht ↦ ((hasDerivAt_baseTime (hmem t ht).1 (hmem t ht).2).continuousAt.sub
      continuousAt_const).const_mul _ |>.continuousWithinAt)
    (fun t ht ↦ (((hasDerivAt_baseTime (hmem t (Ico_subset_Icc_self ht)).1
      (hmem t (Ico_subset_Icc_self ht)).2).sub_const _).const_mul _).hasDerivWithinAt)
    (fun t ht ↦ abs_circleContinuationSlope_le δ r (hmem t (Ico_subset_Icc_self ht)).1
      (hmem t (Ico_subset_Icc_self ht)).2 _)
    (right_mem_Icc.2 hab)
  simpa using key

/-- Along a solution of `Θ' = circleContinuationSlope δ (π ρ) t (Θ t)` on `[a, b] ⊆ (0, 1)`, the
relative angle `ψ = Θ - π ρ` has right derivative `2 δ sin (2 ψ) / (t (1 - t²)) - π ρ'`. -/
private theorem hasDerivWithinAt_sub_of_hasDerivWithinAt_circleContinuationSlope {δ : ℝ}
    {ρ ρ' Θ : ℝ → ℝ} {a b : ℝ} (hρ : ∀ t ∈ Icc a b, HasDerivAt ρ (ρ' t) t)
    (hΘ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) (Icc a b) t) :
    ∀ t ∈ Ico a b, HasDerivWithinAt (fun t ↦ Θ t - π * ρ t)
      (2 * δ * sin (2 * (Θ t - π * ρ t)) / (t * (1 - t ^ 2)) - π * ρ' t) (Ici t) t := by
  intro t ht
  have h := ((hΘ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)).sub
    (((hρ t (Ico_subset_Icc_self ht)).const_mul π).hasDerivWithinAt (s := Ici t))
  exact h.congr_deriv (by simp [circleContinuationSlope_def])

/-- The lower edge of the trapping strip: at `ψ = π / 4` we have `sin (2 ψ) = 1`, and the
hypothesis on `δ` makes the relative angle increase. -/
private theorem pi_div_four_le_sub_of_hasDerivWithinAt_circleContinuationSlope {δ : ℝ}
    {ρ ρ' Θ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hρ : ∀ t ∈ Icc a b, HasDerivAt ρ (ρ' t) t)
    (hδ : ∀ t ∈ Icc a b, π * ρ' t * (t * (1 - t ^ 2)) < 2 * δ)
    (hΘ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) (Icc a b) t)
    (h₀ : π / 4 ≤ Θ a - π * ρ a) :
    ∀ t ∈ Icc a b, π / 4 ≤ Θ t - π * ρ t := by
  have hψ := hasDerivWithinAt_sub_of_hasDerivWithinAt_circleContinuationSlope hρ hΘ
  have hψc : ContinuousOn (fun t ↦ Θ t - π * ρ t) (Icc a b) := fun t ht ↦
    (hΘ t ht).continuousWithinAt.sub ((hρ t ht).continuousAt.continuousWithinAt.const_mul π)
  intro t ht
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun t ↦ -(Θ t - π * ρ t))
    (B := fun _ ↦ -(π / 4)) (B' := fun _ ↦ 0) hψc.neg (fun t ht ↦ (hψ t ht).neg)
    (neg_le_neg h₀) continuousOn_const (fun t _ ↦ hasDerivWithinAt_const _ _ _)
    (fun s hs hseq ↦ ?_) ht
  · linarith [key]
  · have hs' := Ico_subset_Icc_self hs
    have hm := baseSpeed_pos (ha.trans_le hs'.1) (hs'.2.trans_lt hb)
    have hsin : sin (2 * (Θ s - π * ρ s)) = 1 := by
      rw [show Θ s - π * ρ s = π / 4 by linarith [hseq], show 2 * (π / 4) = π / 2 by ring,
        sin_pi_div_two]
    rw [hsin, mul_one, neg_lt_zero, sub_pos, lt_div_iff₀ hm]
    linarith [hδ s hs']

/-- The upper edge of the trapping strip: at `ψ = π / 2` we have `sin (2 ψ) = 0`, so the relative
angle cannot increase. The edge is pushed out by a linearly growing `ε (s - a + 1)`, beyond which
`sin (2 ψ) < 0` makes the crossing strict, and then `ε` tends to `0`. -/
private theorem sub_le_pi_div_two_of_hasDerivWithinAt_circleContinuationSlope {δ : ℝ}
    {ρ ρ' Θ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hδ : 0 ≤ δ)
    (hρ : ∀ t ∈ Icc a b, HasDerivAt ρ (ρ' t) t) (hρ' : ∀ t ∈ Icc a b, 0 ≤ ρ' t)
    (hΘ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) (Icc a b) t)
    (h₀ : Θ a - π * ρ a ≤ π / 2) :
    ∀ t ∈ Icc a b, Θ t - π * ρ t ≤ π / 2 := by
  have hψ := hasDerivWithinAt_sub_of_hasDerivWithinAt_circleContinuationSlope hρ hΘ
  have hψc : ContinuousOn (fun t ↦ Θ t - π * ρ t) (Icc a b) := fun t ht ↦
    (hΘ t ht).continuousWithinAt.sub ((hρ t ht).continuousAt.continuousWithinAt.const_mul π)
  intro t ht
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have hba : 0 < b - a + 1 := by linarith [ht.1.trans ht.2]
  set ε := min η (π / 4) / (b - a + 1)
  have hε0 : 0 < ε := div_pos (lt_min hη (by positivity)) hba
  have hεb : ε * (b - a + 1) = min η (π / 4) := div_mul_cancel₀ _ hba.ne'
  have hB : ∀ s, HasDerivAt (fun s ↦ π / 2 + ε * (s - a + 1)) ε s := fun s ↦ by
    simpa using ((((hasDerivAt_id s).sub_const a).add_const 1).const_mul ε).const_add (π / 2)
  have key := image_le_of_deriv_right_lt_deriv_boundary' (B := fun s ↦ π / 2 + ε * (s - a + 1))
    (B' := fun _ ↦ ε) hψc hψ (by simp only [sub_self, zero_add, mul_one]; linarith)
    (fun s _ ↦ (hB s).continuousAt.continuousWithinAt) (fun s _ ↦ (hB s).hasDerivWithinAt)
    (fun s hs hseq ↦ ?_) ht
  · have : ε * (t - a + 1) ≤ η := by
      calc ε * (t - a + 1) ≤ ε * (b - a + 1) := by gcongr; exact ht.2
        _ ≤ η := hεb ▸ min_le_left _ _
    linarith
  · have hs' := Ico_subset_Icc_self hs
    have hm := baseSpeed_pos (ha.trans_le hs'.1) (hs'.2.trans_lt hb)
    have hlo : 0 < ε * (s - a + 1) := mul_pos hε0 (by linarith [hs.1])
    have hhi : ε * (s - a + 1) ≤ π / 4 := by
      calc ε * (s - a + 1) ≤ ε * (b - a + 1) := by gcongr; exact hs.2.le
        _ ≤ π / 4 := hεb ▸ min_le_right _ _
    have hsin : sin (2 * (Θ s - π * ρ s)) < 0 := by
      rw [← sin_sub_two_pi]
      refine sin_neg_of_neg_of_neg_pi_lt ?_ ?_ <;> nlinarith [pi_pos]
    have h1 : 2 * δ * sin (2 * (Θ s - π * ρ s)) / (s * (1 - s ^ 2)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hsin.le) hm.le
    linarith [mul_nonneg pi_pos.le (hρ' s hs')]

/-- **Trapping in the strip `π / 4 ≤ θ - π ρ(t) ≤ π / 2`.** Let `ρ` be nondecreasing with
derivative `ρ'` on `[a, b] ⊆ (0, 1)`, and let `2 δ > π ρ'(t) t (1 - t²)` there. A solution of
`Θ' = circleContinuationSlope δ (π ρ) t (Θ t)` whose relative angle `Θ - π ρ` starts in
`[π / 4, π / 2]` keeps it there. At the lower edge `sin (2 ψ) = 1` and the hypothesis makes the
relative angle increase; at the upper edge `sin (2 ψ) = 0` and it cannot increase. -/
theorem mem_Icc_of_hasDerivWithinAt_circleContinuationSlope {δ : ℝ} {ρ ρ' Θ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hρ : ∀ t ∈ Icc a b, HasDerivAt ρ (ρ' t) t)
    (hρ' : ∀ t ∈ Icc a b, 0 ≤ ρ' t) (hδ : ∀ t ∈ Icc a b, π * ρ' t * (t * (1 - t ^ 2)) < 2 * δ)
    (hΘ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) (Icc a b) t)
    (h₀ : Θ a - π * ρ a ∈ Icc (π / 4) (π / 2)) :
    ∀ t ∈ Icc a b, Θ t - π * ρ t ∈ Icc (π / 4) (π / 2) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hδ0 : 0 ≤ δ := by
    have h := hδ a (left_mem_Icc.2 hab)
    have : 0 ≤ π * ρ' a * (a * (1 - a ^ 2)) := mul_nonneg
      (mul_nonneg pi_pos.le (hρ' a (left_mem_Icc.2 hab))) (baseSpeed_pos ha (hab.trans_lt hb)).le
    linarith
  exact ⟨pi_div_four_le_sub_of_hasDerivWithinAt_circleContinuationSlope ha hb hρ hδ hΘ h₀.1 t ht,
    sub_le_pi_div_two_of_hasDerivWithinAt_circleContinuationSlope ha hb hδ0 hρ hρ' hΘ h₀.2 t ht⟩

/-- The slope is `4 |δ| / (t (1 - t²))`-Lipschitz in the angle. -/
private theorem dist_circleContinuationSlope_le (δ : ℝ) (r : ℝ → ℝ) {t : ℝ} (h₀ : 0 < t)
    (h₁ : t < 1) (θ θ' : ℝ) :
    dist (circleContinuationSlope δ r t θ) (circleContinuationSlope δ r t θ') ≤
      4 * |δ| * (t * (1 - t ^ 2))⁻¹ * dist θ θ' := by
  have hm := baseSpeed_pos h₀ h₁
  rw [dist_eq_norm, Real.norm_eq_abs, circleContinuationSlope_def, circleContinuationSlope_def,
    ← sub_div, ← mul_sub, abs_div, abs_of_pos hm, abs_mul, abs_mul, abs_two, Real.dist_eq]
  have hs := abs_sin_sub_sin_le (2 * (θ - r t)) (2 * (θ' - r t))
  rw [show 2 * (θ - r t) - 2 * (θ' - r t) = 2 * (θ - θ') by ring, abs_mul, abs_two] at hs
  rw [div_eq_mul_inv]
  calc _ ≤ 2 * |δ| * (2 * |θ - θ'|) * (t * (1 - t ^ 2))⁻¹ := by gcongr
    _ = _ := by ring

/-- Changing `δ` changes the slope by at most `2 |δ - δ'| / (t (1 - t²))`. -/
private theorem dist_circleContinuationSlope_sub_le (δ δ' : ℝ) (r : ℝ → ℝ) {t : ℝ} (h₀ : 0 < t)
    (h₁ : t < 1) (θ : ℝ) :
    dist (circleContinuationSlope δ r t θ) (circleContinuationSlope δ' r t θ) ≤
      2 * |δ - δ'| * (t * (1 - t ^ 2))⁻¹ := by
  have h := abs_circleContinuationSlope_le (δ - δ') r h₀ h₁ θ
  rw [Real.dist_eq]
  convert h using 2
  simp only [circleContinuationSlope_def]
  ring

/-- **Continuous dependence on `δ`.** Let `m₀ > 0` bound `t (1 - t²)` below on `[a, b] ⊆ (0, 1)`.
Two solutions `Θ₁`, `Θ₂` of `Θ' = circleContinuationSlope δᵢ r t (Θ t)` on `[a, b]` stay within the
Grönwall bound with Lipschitz constant `4 |δ₂| / m₀` and error `2 |δ₁ - δ₂| / m₀`: the trajectories
depend continuously on the amplitude `δ` and on the initial angle. -/
theorem abs_sub_le_gronwallBound_of_hasDerivWithinAt_circleContinuationSlope
    {δ₁ δ₂ m₀ : ℝ} {r Θ₁ Θ₂ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hm₀ : 0 < m₀)
    (hm : ∀ t ∈ Icc a b, m₀ ≤ t * (1 - t ^ 2))
    (hΘ₁ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ₁ (circleContinuationSlope δ₁ r t (Θ₁ t)) (Icc a b) t)
    (hΘ₂ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Θ₂ (circleContinuationSlope δ₂ r t (Θ₂ t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, |Θ₁ t - Θ₂ t| ≤
      gronwallBound |Θ₁ a - Θ₂ a| (4 * |δ₂| / m₀) (2 * |δ₁ - δ₂| / m₀) (t - a) := by
  have hmem : ∀ t ∈ Icc a b, 0 < t ∧ t < 1 := fun t ht ↦ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hinv : ∀ t ∈ Icc a b, (t * (1 - t ^ 2))⁻¹ ≤ m₀⁻¹ := fun t ht ↦
    inv_anti₀ hm₀ (hm t ht)
  set K : ℝ≥0 := ⟨4 * |δ₂| / m₀, by positivity⟩
  have hK : ∀ t ∈ Ico a b, LipschitzOnWith K (circleContinuationSlope δ₂ r t) univ := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun θ θ' ↦ ?_).lipschitzOnWith
    have ht' := Ico_subset_Icc_self ht
    refine (dist_circleContinuationSlope_le δ₂ r (hmem t ht').1 (hmem t ht').2 θ θ').trans ?_
    -- Unfold the coercion of the `ℝ≥0` constant `K`.
    change _ ≤ (4 * |δ₂| / m₀) * dist θ θ'
    rw [div_eq_mul_inv]
    gcongr
    exact hm t ht'
  have hbound : ∀ t ∈ Ico a b, dist (circleContinuationSlope δ₁ r t (Θ₁ t))
      (circleContinuationSlope δ₂ r t (Θ₁ t)) ≤ 2 * |δ₁ - δ₂| / m₀ := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    refine (dist_circleContinuationSlope_sub_le δ₁ δ₂ r (hmem t ht').1 (hmem t ht').2 _).trans ?_
    rw [div_eq_mul_inv]
    gcongr
    exact hm t ht'
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := circleContinuationSlope δ₂ r)
    (s := fun _ ↦ univ) (εg := 0) hK
    (fun t ht ↦ (hΘ₁ t ht).continuousWithinAt)
    (fun t ht ↦ (hΘ₁ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    hbound (fun _ _ ↦ mem_univ _)
    (fun t ht ↦ (hΘ₂ t ht).continuousWithinAt)
    (fun t ht ↦ (hΘ₂ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ ↦ by simp) (fun _ _ ↦ mem_univ _) (le_of_eq (Real.dist_eq _ _))
  intro t ht
  have h := key t ht
  rw [Real.dist_eq, add_zero] at h
  exact h

/-- The slope of the half-turn path `π ρ` satisfies the Picard–Lindelöf hypotheses on the window
`[1/3, 5/6]`, with initial angle `π / 2`. -/
private theorem isPicardLindelof_circleContinuationSlope (δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    IsPicardLindelof (circleContinuationSlope δ (fun t ↦ π * ρ t))
      (tmin := 1 / 3) (tmax := 5 / 6) ⟨1 / 3, by norm_num, by norm_num⟩ (π / 2)
      ⟨4 * |δ|, by positivity⟩ 0 ⟨8 * |δ|, by positivity⟩ ⟨16 * |δ|, by positivity⟩ := by
  have hmem : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6), 0 < t ∧ t < 1 := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hinv : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6), (t * (1 - t ^ 2))⁻¹ ≤ 4 := fun t ht ↦ by
    rw [inv_le_comm₀ (baseSpeed_pos (hmem t ht).1 (hmem t ht).2) (by norm_num)]
    exact (by norm_num : (4 : ℝ)⁻¹ = 1 / 4) ▸ quarter_le_baseSpeed ht.1 ht.2
  refine ⟨fun t ht ↦ ?_, fun θ _ ↦ ?_, fun t ht θ _ ↦ ?_, ?_⟩
  · refine (LipschitzWith.of_dist_le_mul fun θ θ' ↦ ?_).lipschitzOnWith
    refine (dist_circleContinuationSlope_le δ _ (hmem t ht).1 (hmem t ht).2 θ θ').trans ?_
    -- Unfold the coercion of the `ℝ≥0` Lipschitz constant.
    change _ ≤ (16 * |δ|) * dist θ θ'
    calc 4 * |δ| * (t * (1 - t ^ 2))⁻¹ * dist θ θ' ≤ 4 * |δ| * 4 * dist θ θ' := by
          gcongr; exact hinv t ht
      _ = 16 * |δ| * dist θ θ' := by ring
  · simp only [circleContinuationSlope_def]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht ↦ ?_
    exact (baseSpeed_pos (hmem t ht).1 (hmem t ht).2).ne'
  · rw [Real.norm_eq_abs]
    refine (abs_circleContinuationSlope_le δ _ (hmem t ht).1 (hmem t ht).2 θ).trans ?_
    -- Unfold the coercion of the `ℝ≥0` bound.
    change _ ≤ 8 * |δ|
    have := hinv t ht
    nlinarith [abs_nonneg δ]
  · -- Unfold the coercions of the `ℝ≥0` constants and of the initial time.
    change (8 * |δ|) * max ((5 : ℝ) / 6 - 1 / 3) (1 / 3 - 1 / 3) ≤ 4 * |δ| - 0
    rw [show max ((5 : ℝ) / 6 - 1 / 3) (1 / 3 - 1 / 3) = 1 / 2 by norm_num]
    linarith

/-- The trajectory of the half-turn continuation leaving the source minimum, on the window
`[1/3, 5/6]`: a solution starting at the angle `π / 2`. -/
private theorem exists_hasDerivWithinAt_circleContinuationSlope (δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    ∃ Θ : ℝ → ℝ, Θ (1 / 3) = π / 2 ∧ ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6),
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t))
        (Icc (1 / 3) (5 / 6)) t :=
  (isPicardLindelof_circleContinuationSlope δ hρ).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- The angular velocity vanishes where `sin (2 (θ - r t)) = 0`. -/
private theorem circleContinuationSlope_eq_zero {δ : ℝ} {r : ℝ → ℝ} {t θ : ℝ}
    (h : sin (2 * (θ - r t)) = 0) : circleContinuationSlope δ r t θ = 0 := by
  simp [circleContinuationSlope_def, h]

/-- The base trajectory `τ s = (1 + e^{-2 s})^{-1/2}` of `t' = t (1 - t²)`, running from `t = 0`
to `t = 1`. -/
private noncomputable def baseOrbit (s : ℝ) : ℝ := (√(1 + exp (-2 * s)))⁻¹

private theorem one_lt_sqrt_baseOrbit (s : ℝ) : 1 < √(1 + exp (-2 * s)) := by
  rw [lt_sqrt zero_le_one, one_pow]
  linarith [exp_pos (-2 * s)]

private theorem baseOrbit_pos (s : ℝ) : 0 < baseOrbit s :=
  inv_pos.2 (zero_lt_one.trans (one_lt_sqrt_baseOrbit s))

private theorem baseOrbit_lt_one (s : ℝ) : baseOrbit s < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_sqrt_baseOrbit s)

private theorem hasDerivAt_baseOrbit (s : ℝ) :
    HasDerivAt baseOrbit (baseOrbit s * (1 - baseOrbit s ^ 2)) s := by
  have hu : 0 < 1 + exp (-2 * s) := by positivity
  have hq : 0 < √(1 + exp (-2 * s)) := sqrt_pos.2 hu
  have hd : HasDerivAt (fun s ↦ 1 + exp (-2 * s)) (exp (-2 * s) * (-2)) s := by
    simpa using (((hasDerivAt_id s).const_mul (-2)).exp).const_add 1
  have h := (hd.sqrt hu.ne').inv hq.ne'
  unfold baseOrbit
  refine h.congr_deriv ?_
  have hsq : √(1 + exp (-2 * s)) ^ 2 = 1 + exp (-2 * s) := sq_sqrt hu.le
  generalize √(1 + exp (-2 * s)) = q at hq hsq ⊢
  rw [show exp (-2 * s) = q ^ 2 - 1 by linarith]
  field_simp

private theorem tendsto_baseOrbit_atBot : Tendsto baseOrbit atBot (𝓝 0) := by
  have h : Tendsto (fun s : ℝ ↦ 1 + exp (-2 * s)) atBot atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atBot_of_neg (by norm_num : (-2 : ℝ) < 0)))
  exact tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp h)

private theorem tendsto_baseOrbit_atTop : Tendsto baseOrbit atTop (𝓝 1) := by
  have h : Tendsto (fun s : ℝ ↦ 1 + exp (-2 * s)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0)))
  have h' := ((continuous_sqrt.tendsto _).comp h).inv₀ (by norm_num)
  unfold baseOrbit
  simpa using h'

/-- For the half-turn path, the amplitude `δ` at which the trajectory leaving the source minimum
reaches angle exactly `π` at `t = 5/6`, with that trajectory on the window `[1/3, 5/6]`. -/
private theorem exists_hasDerivWithinAt_circleContinuationSlope_eq_pi {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hmono : Monotone ρ) (h0 : ∀ t ≤ 1 / 3, ρ t = 0)
    (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) :
    ∃ δ > 0, ∃ Θ : ℝ → ℝ, Θ (1 / 3) = π / 2 ∧ Θ (5 / 6) = π ∧ ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6),
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t))
        (Icc (1 / 3) (5 / 6)) t := by
  have hwin : (1 / 3 : ℝ) ≤ 5 / 6 := by norm_num
  choose Θ hΘ0 hΘ using fun δ ↦ exists_hasDerivWithinAt_circleContinuationSlope δ hρ.continuous
  -- The angle at `t = 5/6` depends continuously on `δ`, by the Grönwall estimate.
  have hF : Continuous fun δ ↦ Θ δ (5 / 6) := by
    rw [continuous_iff_continuousAt]
    intro δ₀
    set G : ℝ → ℝ := fun δ ↦
      gronwallBound 0 (4 * |δ₀| / (1 / 4)) (2 * |δ - δ₀| / (1 / 4)) (5 / 6 - 1 / 3)
    have hb : ∀ δ, dist (Θ δ (5 / 6)) (Θ δ₀ (5 / 6)) ≤ G δ := fun δ ↦ by
      have h := abs_sub_le_gronwallBound_of_hasDerivWithinAt_circleContinuationSlope
        (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4)
        (fun t ht ↦ quarter_le_baseSpeed ht.1 ht.2) (hΘ δ) (hΘ δ₀) (5 / 6) ⟨hwin, le_rfl⟩
      rw [hΘ0, hΘ0, sub_self, abs_zero] at h
      rwa [Real.dist_eq]
    have hG : Tendsto G (𝓝 δ₀) (𝓝 0) := by
      have hc : Continuous G := (gronwallBound_continuous_ε _ _ _).comp (by fun_prop)
      simpa [G, gronwallBound_ε0_δ0] using hc.tendsto δ₀
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) hb hG)
  -- For `δ = 0` the angle does not move.
  have hF0 : Θ 0 (5 / 6) = π / 2 := by
    have h := abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope (by norm_num) hwin
      (by norm_num) (hΘ 0)
    rw [abs_zero, mul_zero, zero_mul, abs_nonpos_iff, sub_eq_zero, hΘ0] at h
    exact h
  -- For large `δ` the relative angle is trapped above `π / 4`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hρ.continuous_deriv le_rfl).continuousOn (s := Icc (1 / 3 : ℝ) (5 / 6))
  set Δ := π * (|C| + 1) / 2 with hΔdef
  have hΔ : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6), π * deriv ρ t * (t * (1 - t ^ 2)) < 2 * Δ := by
    intro t ht
    have hm0 : 0 < t * (1 - t ^ 2) := baseSpeed_pos (by linarith [ht.1]) (by linarith [ht.2])
    have hm1 : t * (1 - t ^ 2) ≤ 1 := by nlinarith [ht.1, ht.2]
    have hd : deriv ρ t ≤ |C| := (le_abs_self _).trans ((hC t ht).trans (le_abs_self C))
    have hd0 : 0 ≤ deriv ρ t := hmono.deriv_nonneg
    calc π * deriv ρ t * (t * (1 - t ^ 2)) ≤ π * |C| * 1 := by gcongr
      _ < 2 * Δ := by rw [hΔdef]; nlinarith [pi_pos]
  have hFΔ : π + π / 4 ≤ Θ Δ (5 / 6) := by
    have h := mem_Icc_of_hasDerivWithinAt_circleContinuationSlope (by norm_num) (by norm_num)
      (fun t _ ↦ ((hρ.differentiable one_ne_zero) t).hasDerivAt) (fun _ _ ↦ hmono.deriv_nonneg) hΔ
      (hΘ Δ) (by rw [hΘ0, h0 _ le_rfl, mul_zero, sub_zero]; constructor <;> linarith [pi_pos])
      (5 / 6) ⟨hwin, le_rfl⟩
    rw [h1 _ (by norm_num), mul_one] at h
    linarith [h.1]
  -- The intermediate value theorem.
  have hπ : π ∈ Icc (Θ 0 (5 / 6)) (Θ Δ (5 / 6)) :=
    ⟨by rw [hF0]; linarith [pi_pos], by linarith [pi_pos]⟩
  obtain ⟨δ, hδmem, hδ⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Δ) hF.continuousOn hπ
  simp only at hδ
  refine ⟨δ, lt_of_le_of_ne hδmem.1 ?_, Θ δ, hΘ0 δ, hδ, hΘ δ⟩
  rintro rfl
  rw [hF0] at hδ
  linarith [pi_pos]

/-- A solution of `Θ' = circleContinuationSlope δ (π ρ) t (Θ t)` on `[1/3, 5/6]` from `π / 2` to
`π` extends to a solution on the whole line by the angle `π / 2` for `t ≤ 1/3` and `π` for
`t ≥ 5/6`. There `ρ` is `0`, respectively `1`, so these constant angles are zeros of the slope, and
the one-sided derivatives match at the junctions. -/
private theorem exists_hasDerivAt_circleContinuationSlope_of_window {δ : ℝ} {ρ Θ : ℝ → ℝ}
    (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hΘa : Θ (1 / 3) = π / 2)
    (hΘb : Θ (5 / 6) = π) (hΘ : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6),
      HasDerivWithinAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t))
        (Icc (1 / 3) (5 / 6)) t) :
    ∃ Θg : ℝ → ℝ, (∀ t ≤ 1 / 3, Θg t = π / 2) ∧ (∀ t, 5 / 6 ≤ t → Θg t = π) ∧
      ∀ t, HasDerivAt Θg (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θg t)) t := by
  set r : ℝ → ℝ := fun t ↦ π * ρ t
  set Θg : ℝ → ℝ := fun t ↦ if t ≤ 1 / 3 then π / 2 else if t ≤ 5 / 6 then Θ t else π
  have hΘg₀ : ∀ t ≤ 1 / 3, Θg t = π / 2 := fun t ht ↦ by simp only [Θg, ht, ↓reduceIte]
  have hΘg₁ : ∀ t, 5 / 6 ≤ t → Θg t = π := fun t ht ↦ by
    have h3 : ¬ t ≤ 1 / 3 := by linarith
    rcases ht.eq_or_lt with rfl | h
    · simp only [Θg, h3, le_refl, ↓reduceIte, hΘb]
    · simp only [Θg, h3, not_le.2 h, ↓reduceIte]
  have hΘgΘ : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6), Θg t = Θ t := fun t ht ↦ by
    rcases ht.1.eq_or_lt with rfl | h
    · rw [hΘg₀ _ le_rfl, hΘa]
    · simp only [Θg, not_le.2 h, ht.2, ↓reduceIte]
  have hzero₀ : ∀ t ≤ 1 / 3, circleContinuationSlope δ r t (π / 2) = 0 := fun t ht ↦
    circleContinuationSlope_eq_zero (by
      simp only [r]; rw [h0 t ht, mul_zero, sub_zero, mul_div_cancel₀ _ two_ne_zero, sin_pi])
  have hzero₁ : ∀ t, 2 / 3 ≤ t → circleContinuationSlope δ r t π = 0 := fun t ht ↦
    circleContinuationSlope_eq_zero (by
      simp only [r]; rw [h1 t ht, mul_one, sub_self, mul_zero, sin_zero])
  have hleft : ∀ t ≤ 1 / 3, HasDerivWithinAt Θg 0 (Iic (1 / 3)) t := fun t ht ↦
    (hasDerivWithinAt_const t _ (π / 2)).congr (fun y hy ↦ hΘg₀ y hy) (hΘg₀ t ht)
  have hright : ∀ t, 5 / 6 ≤ t → HasDerivWithinAt Θg 0 (Ici (5 / 6)) t := fun t ht ↦
    (hasDerivWithinAt_const t _ π).congr (fun y hy ↦ hΘg₁ y hy) (hΘg₁ t ht)
  have hmid : ∀ t ∈ Icc (1 / 3 : ℝ) (5 / 6),
      HasDerivWithinAt Θg (circleContinuationSlope δ r t (Θg t)) (Icc (1 / 3) (5 / 6)) t :=
    fun t ht ↦ by
      rw [hΘgΘ t ht]
      exact (hΘ t ht).congr (fun y hy ↦ hΘgΘ y hy) (hΘgΘ t ht)
  refine ⟨Θg, hΘg₀, hΘg₁, fun t ↦ ?_⟩
  rcases lt_trichotomy t (1 / 3) with h | rfl | h
  · rw [hΘg₀ t h.le, hzero₀ t h.le]
    exact (hleft t h.le).hasDerivAt (Iic_mem_nhds h)
  · rw [hΘg₀ _ le_rfl, hzero₀ _ le_rfl, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
    refine (hleft _ le_rfl).union ?_
    have h := (hmid (1 / 3) ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE (by norm_num))
    rwa [hΘg₀ _ le_rfl, hzero₀ _ le_rfl] at h
  rcases lt_trichotomy t (5 / 6) with h' | rfl | h'
  · exact (hmid t ⟨h.le, h'.le⟩).hasDerivAt (Icc_mem_nhds h h')
  · rw [hΘg₁ _ le_rfl, hzero₁ _ (by norm_num), ← hasDerivWithinAt_univ, ← Iic_union_Ici]
    refine HasDerivWithinAt.union ?_ (hright _ le_rfl)
    have h := (hmid (5 / 6) ⟨by norm_num, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE (by norm_num))
    rwa [hΘg₁ _ le_rfl, hzero₁ _ (by norm_num)] at h
  · rw [hΘg₁ t h'.le, hzero₁ t (by linarith)]
    exact (hright t h'.le).hasDerivAt (Ici_mem_nhds h')

/-- **A slice-wise Morse–Smale continuation whose parameter field is not transverse.** Let `ρ` be
`C¹`, nondecreasing, `0` for `t ≤ 1/3` and `1` for `t ≥ 2/3`, and consider the half-turn path
`r = π ρ`, from `δ cos (2 θ)` to the same function `δ cos (2 (θ - π))`. For some `δ > 0` the
parameter field `TauCeti.circleContinuationField δ (π ρ)` has a trajectory from the minimum
`(π / 2, 0)` of the source function to the maximum `(π, 1)` of the target function. Both are zeros
of the field with a one-dimensional unstable manifold
(`TauCeti.hasFDerivAt_circleContinuationField_pi_div_two_zero`,
`TauCeti.hasFDerivAt_circleContinuationField_pi_one`), so this connection has expected dimension
`0 - 1 = -1`, and the field is not transverse, although every slice is a Morse function whose
gradient flow on the circle is Morse–Smale. -/
theorem exists_circleContinuationField_connection {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hmono : Monotone ρ) (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) :
    ∃ δ > 0, ∃ γ : ℝ → ℝ × ℝ,
      (∀ s, HasDerivAt γ (circleContinuationField δ (fun t ↦ π * ρ t) (γ s)) s) ∧
      Tendsto γ atBot (𝓝 (π / 2, 0)) ∧ Tendsto γ atTop (𝓝 (π, 1)) := by
  obtain ⟨δ, hδ, Θ, hΘa, hΘb, hΘ⟩ :=
    exists_hasDerivWithinAt_circleContinuationSlope_eq_pi hρ hmono h0 h1
  obtain ⟨Θg, hΘg₀, hΘg₁, hΘg⟩ :=
    exists_hasDerivAt_circleContinuationSlope_of_window h0 h1 hΘa hΘb hΘ
  -- Follow the graph along the base trajectory from `t = 0` to `t = 1`.
  refine ⟨δ, hδ, fun s ↦ (Θg (baseOrbit s), baseOrbit s), fun s ↦ ?_, ?_, ?_⟩
  · exact hasDerivAt_circleContinuationField (hasDerivAt_baseOrbit s) (baseOrbit_pos s)
      (baseOrbit_lt_one s) (hΘg _)
  · refine Tendsto.prodMk_nhds (tendsto_const_nhds.congr' ?_) tendsto_baseOrbit_atBot
    filter_upwards [tendsto_baseOrbit_atBot.eventually (Iic_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 3))] with s hs
    exact (hΘg₀ _ hs).symm
  · refine Tendsto.prodMk_nhds (tendsto_const_nhds.congr' ?_) tendsto_baseOrbit_atTop
    filter_upwards [tendsto_baseOrbit_atTop.eventually (Ioi_mem_nhds (by norm_num :
      (5 / 6 : ℝ) < 1))] with s hs
    exact (hΘg₁ _ (le_of_lt hs)).symm

/-- The derivative of the parameter field at `(θ, t)`, for a path `r` with derivative `r'` at `t`:
`(dθ, dt) ↦ (4 δ cos (2 (θ - r t)) (dθ - r' dt), (1 - 3 t²) dt)`. -/
theorem hasFDerivAt_circleContinuationField {δ : ℝ} {r : ℝ → ℝ} {r' θ t : ℝ}
    (hr : HasDerivAt r r' t) :
    HasFDerivAt (circleContinuationField δ r)
      (((4 * δ * cos (2 * (θ - r t))) •
          (ContinuousLinearMap.fst ℝ ℝ ℝ - r' • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
        ((1 - 3 * t ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) (θ, t) := by
  have hg : HasFDerivAt (fun x : ℝ × ℝ ↦ x.1 - r x.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - r' • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ, t) :=
    hasFDerivAt_fst.sub (hr.comp_hasFDerivAt (θ, t) hasFDerivAt_snd)
  have h₁ := ((hasDerivAt_sin _).comp_hasFDerivAt (θ, t) (hg.const_mul 2)).const_mul (2 * δ)
  have hb : HasDerivAt (fun t : ℝ ↦ t * (1 - t ^ 2)) (1 - 3 * t ^ 2) t := by
    have h := (hasDerivAt_id t).sub (hasDerivAt_pow 3 t)
    have hf : (fun x : ℝ ↦ x * (1 - x ^ 2)) = fun x ↦ id x - x ^ 3 := by
      funext x
      simp only [id_eq]
      ring
    rw [hf]
    convert h using 1
  have h₂ := hb.comp_hasFDerivAt (θ, t) (hasFDerivAt_snd (𝕜 := ℝ) (p := (θ, t)))
  refine (h₁.prodMk h₂).congr_fderiv ?_
  ext <;> simp <;> ring

/-- The minimum `π / 2` of the source function `δ cos (2 θ)` is a zero of the parameter field of
the half-turn path `π ρ`. -/
theorem circleContinuationField_pi_div_two_zero {δ : ℝ} {ρ : ℝ → ℝ} (h0 : ρ 0 = 0) :
    circleContinuationField δ (fun t ↦ π * ρ t) (π / 2, 0) = 0 := by
  simp [h0, mul_div_cancel₀ _ (two_ne_zero' ℝ)]

/-- The maximum `π` of the target function `δ cos (2 (θ - π))` is a zero of the parameter field
of the half-turn path `π ρ`. -/
theorem circleContinuationField_pi_one {δ : ℝ} {ρ : ℝ → ℝ} (h1 : ρ 1 = 1) :
    circleContinuationField δ (fun t ↦ π * ρ t) (π, 1) = 0 := by
  simp [h1]

/-- **The source minimum has index one.** If `ρ 0 = 0` and `ρ' 0 = 0`, the linearization of the
parameter field of the half-turn path at the source minimum `(π / 2, 0)` is `diag(-4 δ, 1)`: for
`δ > 0` the angle direction is contracting and the parameter direction expanding. -/
theorem hasFDerivAt_circleContinuationField_pi_div_two_zero {δ : ℝ} {ρ : ℝ → ℝ}
    (hρ : HasDerivAt ρ 0 0) (h0 : ρ 0 = 0) :
    HasFDerivAt (circleContinuationField δ (fun t ↦ π * ρ t))
      (((-(4 * δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (π / 2, 0) := by
  refine (hasFDerivAt_circleContinuationField (hρ.const_mul π)).congr_fderiv ?_
  ext <;> simp [h0, mul_div_cancel₀ _ (two_ne_zero' ℝ)]

/-- **The target maximum has index one.** If `ρ 1 = 1` and `ρ' 1 = 0`, the linearization of the
parameter field of the half-turn path at the target maximum `(π, 1)` is `diag(4 δ, -2)`: for
`δ > 0` the angle direction is expanding and the parameter direction contracting. -/
theorem hasFDerivAt_circleContinuationField_pi_one {δ : ℝ} {ρ : ℝ → ℝ} (hρ : HasDerivAt ρ 0 1)
    (h1 : ρ 1 = 1) :
    HasFDerivAt (circleContinuationField δ (fun t ↦ π * ρ t))
      (((4 * δ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((-2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ))
      (π, 1) := by
  refine (hasFDerivAt_circleContinuationField (hρ.const_mul π)).congr_fderiv ?_
  ext <;> simp [h1]
  norm_num

/-- The non-transverse connection of `TauCeti.exists_circleContinuationField_connection` for the
standard smooth step `ρ t = smoothTransition (3 t - 1)`. -/
theorem exists_circleContinuationField_connection_smoothTransition :
    ∃ δ > 0, ∃ γ : ℝ → ℝ × ℝ, (∀ s, HasDerivAt γ
        (circleContinuationField δ (fun t ↦ π * smoothTransition (3 * t - 1)) (γ s)) s) ∧
      Tendsto γ atBot (𝓝 (π / 2, 0)) ∧ Tendsto γ atTop (𝓝 (π, 1)) :=
  exists_circleContinuationField_connection
    (smoothTransition.contDiff.comp (by fun_prop))
    (smoothTransition.monotone.comp fun _ _ h ↦ by linarith)
    (fun t ht ↦ smoothTransition.zero_of_nonpos (by linarith))
    (fun t ht ↦ smoothTransition.one_of_one_le (by linarith))

end TauCeti
