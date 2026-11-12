/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic
public import TauCeti.Analysis.Calculus.Morse.IntervalBase
import TauCeti.Analysis.Calculus.ContDiff.GlueHalfLine
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Index-preserving continuation trajectories on the circle, by basin membership

On the circle, consider the continuation family `f_{r(t)}(θ) = δ cos (2 (θ - r t))`, `δ > 0`, along
a path `r` which is constant, `r₀`, for `0 < t ≤ a` and constant, `r₁`, for `b ≤ t < 1`, where
`0 < a ≤ b < 1`. The maxima of `f_r` are the angles `r + j π` and its minima the angles
`r + π / 2 + j π`, `j ∈ ℤ`. Trajectories of the parameter field
`TauCeti.circleContinuationField` in `0 < t < 1` are the graphs of the solutions `Θ` on `(0, 1)` of
`Θ' = circleContinuationSlope δ r t (Θ t)`, in lifted angles. This file classifies the trajectories
between critical points of equal index of the two end functions, which are the ones counted by the
continuation map, and proves that none runs from a minimum of the source function to a maximum of
the target function.

Near a constant end the equation is solved explicitly. With the time coordinate
`U(t) = log t - (1 / 2) log (1 - t²)` of `TauCeti.intervalBaseTimeCoordinate`, the relative angle
`ψ = Θ - c` solves `ψ' = 2 δ sin (2 ψ) U'(t)`, so `tan (Θ - κ) exp (-4 δ σ U)` is constant for any
critical angle `κ` of the end function, with `σ = cos (2 (κ - c)) = ±1`
(`TauCeti.eqOn_arctan_of_hasDerivAt_circleContinuationSlope`). Since `U → -∞` at `t = 0` and
`U → +∞` at `t = 1`, a solution tends at `t = 0` to the maximum `κ` with `|Θ a - κ| < π / 2`, and at
`t = 1` to the minimum `κ` with `|Θ b - κ| < π / 2`; the critical points at the edges of these
basins, the minima at `t = 0` and the maxima at `t = 1`, are reached only by the constant solutions
(`TauCeti.eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope`,
`TauCeti.eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope`).

Across the window `[a, b]` a solution moves by at most the drift `2 δ ∫_a^b (t (1 - t²))⁻¹ dt`
(`TauCeti.abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope`).
Suppose that `|r₁ - r₀ - n π|` plus this drift is less than `π / 2` for an integer `n`. Then for
every `k ∈ ℤ` there is exactly one trajectory converging to the target maximum `r₁ + k π`, and it
comes from the source maximum `r₀ + (k + n) π`; there is exactly one trajectory leaving the source
minimum `r₀ + π / 2 + (k + n) π`, and it converges to the target minimum `r₁ + π / 2 + k π`; and no
trajectory runs from a source minimum to a target maximum. Labelling the two maxima and the two
minima of `f_r` on the circle by `j mod 2`, the continuation map in both degrees is the identity
for even `n` and the exchange of the two critical points for odd `n`.

This is the input for the circle continuation counterexamples of Morse homology. For the half turn
`r = π ρ` the end functions agree, `n = 1`, and the continuation map is the identity in the fixed
spatial basis of critical points (`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_halfTurn`,
`TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_halfTurn`), whereas tracking the critical points
`r(t) + j π` along the path moves each maximum to the other one. For rotations by `π / 3` and by
`2 π / 3` the integers are `n = 0` and `n = 1`, so in the moving labels the continuation maps of the
two halves of a rotation by `2 π / 3` are identities while that of the whole rotation is the
exchange (`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_sixthTurn`,
`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_thirdTurn`).

## Main results

* `TauCeti.eqOn_of_hasDerivAt_circleContinuationSlope`: uniqueness of solutions on an interval.
* `TauCeti.exists_hasDerivAt_circleContinuationSlope`: existence of solutions on `(0, 1)` for a
  path which is constant near the ends.
* `TauCeti.tendsto_nhdsGT_zero_circleContinuationSlope` and
  `TauCeti.tendsto_nhdsLT_one_circleContinuationSlope`: the end limits in the basins.
* `TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_max`,
  `TauCeti.eqOn_of_tendsto_nhdsLT_one_max` and `TauCeti.exists_tendsto_nhdsLT_one_max`: the
  trajectories between maxima.
* `TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_min`,
  `TauCeti.eqOn_of_tendsto_nhdsGT_zero_min` and `TauCeti.exists_tendsto_nhdsGT_zero_min`: the
  trajectories between minima.
* `TauCeti.not_tendsto_nhdsGT_zero_min_and_tendsto_nhdsLT_one_max`: no trajectory from a source
  minimum to a target maximum.
* `TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_halfTurn` and
  `TauCeti.tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_halfTurn`: the half turn.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Real Set Topology

namespace TauCeti

/-! ### Critical angles of the end functions -/

/-- The angles `c + k π` are the maxima of `δ cos (2 (θ - c))`. -/
private theorem sin_cos_two_mul_add_int_mul_pi_sub (c : ℝ) (k : ℤ) :
    sin (2 * (c + k * π - c)) = 0 ∧ cos (2 * (c + k * π - c)) = 1 := by
  rw [show 2 * (c + k * π - c) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring, sin_int_mul_pi,
    show ((2 * k : ℤ) : ℝ) * π = (k : ℝ) * (2 * π) by push_cast; ring, cos_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

/-- The angles `c + π / 2 + k π` are the minima of `δ cos (2 (θ - c))`. -/
private theorem sin_cos_two_mul_add_pi_div_two_add_int_mul_pi_sub (c : ℝ) (k : ℤ) :
    sin (2 * (c + π / 2 + k * π - c)) = 0 ∧ cos (2 * (c + π / 2 + k * π - c)) = -1 := by
  rw [show 2 * (c + π / 2 + k * π - c) = ((2 * k + 1 : ℤ) : ℝ) * π by push_cast; ring,
    sin_int_mul_pi, show ((2 * k + 1 : ℤ) : ℝ) * π = π + (k : ℝ) * (2 * π) by push_cast; ring,
    cos_add_int_mul_two_pi, cos_pi]
  exact ⟨rfl, rfl⟩

/-! ### Uniqueness and the explicit solution at a constant end -/

/-- **Uniqueness.** Two solutions of `Θ' = circleContinuationSlope δ r t (Θ t)` on an interval
`I ⊆ (0, 1)` which agree at one time of `I` agree on `I`. -/
theorem eqOn_of_hasDerivAt_circleContinuationSlope {δ : ℝ} {r Θ₁ Θ₂ : ℝ → ℝ} {I : Set ℝ}
    (hI : I ⊆ Ioo 0 1) (hIc : I.OrdConnected)
    (hΘ₁ : ∀ t ∈ I, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ I, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h : Θ₁ t₀ = Θ₂ t₀) : EqOn Θ₁ Θ₂ I := by
  intro t ht
  rcases le_total t₀ t with htt | htt
  · have hsub : Icc t₀ t ⊆ I := hIc.out ht₀ ht
    exact ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (fun s hs ↦ (lipschitzWith_circleContinuationSlope δ r (hI ht₀).1 (hI ht).2
        (Ico_subset_Icc_self hs)).lipschitzOnWith)
      (HasDerivAt.continuousOn fun s hs ↦ hΘ₁ s (hsub hs))
      (fun s hs ↦ (hΘ₁ s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _)
      (HasDerivAt.continuousOn fun s hs ↦ hΘ₂ s (hsub hs))
      (fun s hs ↦ (hΘ₂ s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) h ⟨htt, le_rfl⟩
  · have hsub : Icc t t₀ ⊆ I := hIc.out ht ht₀
    exact ODE_solution_unique_of_mem_Icc_left (s := fun _ ↦ univ)
      (fun s hs ↦ (lipschitzWith_circleContinuationSlope δ r (hI ht).1 (hI ht₀).2
        (Ioc_subset_Icc_self hs)).lipschitzOnWith)
      (HasDerivAt.continuousOn fun s hs ↦ hΘ₁ s (hsub hs))
      (fun s hs ↦ (hΘ₁ s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _)
      (HasDerivAt.continuousOn fun s hs ↦ hΘ₂ s (hsub hs))
      (fun s hs ↦ (hΘ₂ s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) h ⟨le_rfl, htt⟩

/-- Where the path is constant, `c`, the path `κ + arctan (X exp (4 δ σ (U t - U t₀)))` solves the
equation, for every critical angle `κ` of `δ cos (2 (θ - c))`, with `σ = cos (2 (κ - c))`. -/
private theorem hasDerivAt_arctan_circleContinuationSlope {δ c κ X t₀ t : ℝ} {r : ℝ → ℝ}
    (ht : t ∈ Ioo 0 1) (hr : r t = c) (hκ : sin (2 * (κ - c)) = 0) :
    HasDerivAt (fun t ↦ κ + arctan (X * exp (4 * δ * cos (2 * (κ - c)) *
        (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate t₀))))
      (circleContinuationSlope δ r t (κ + arctan (X * exp (4 * δ * cos (2 * (κ - c)) *
        (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate t₀))))) t := by
  set σ := cos (2 * (κ - c))
  have hY := ((((hasDerivAt_intervalBaseTimeCoordinate ht).sub_const
    (intervalBaseTimeCoordinate t₀)).const_mul (4 * δ * σ)).exp).const_mul X
  refine (hY.arctan.const_add κ).congr_deriv ?_
  set Y := X * exp (4 * δ * σ * (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate t₀))
    with hYdef
  rw [circleContinuationSlope_def, hr,
    show 2 * (κ + arctan Y - c) = 2 * (κ - c) + 2 * arctan Y by ring, sin_add, hκ, zero_mul,
    zero_add, sin_two_mul, sin_arctan, cos_arctan]
  field_simp
  rw [sq_sqrt (by positivity), hYdef]
  ring

/-- **The explicit solution at a constant end.** On an interval `I ⊆ (0, 1)` where the path is
constant, `c`, let `κ` be a critical angle of `δ cos (2 (θ - c))` with `|Θ t₀ - κ| < π / 2` at some
`t₀ ∈ I`. Then a solution `Θ` on `I` is
`κ + arctan (tan (Θ t₀ - κ) exp (4 δ cos (2 (κ - c)) (U t - U t₀)))`, where `U` is the time
coordinate `TauCeti.intervalBaseTimeCoordinate`, and `cos (2 (κ - c))` is `1` at a maximum and `-1`
at a minimum. -/
theorem eqOn_arctan_of_hasDerivAt_circleContinuationSlope {δ c κ t₀ : ℝ} {r Θ : ℝ → ℝ}
    {I : Set ℝ} (hI : I ⊆ Ioo 0 1) (hIc : I.OrdConnected) (hr : ∀ t ∈ I, r t = c)
    (hΘ : ∀ t ∈ I, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t)
    (hκ : sin (2 * (κ - c)) = 0) (ht₀ : t₀ ∈ I) (hψ : |Θ t₀ - κ| < π / 2) :
    EqOn Θ (fun t ↦ κ + arctan (tan (Θ t₀ - κ) * exp (4 * δ * cos (2 * (κ - c)) *
      (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate t₀)))) I :=
  eqOn_of_hasDerivAt_circleContinuationSlope hI hIc hΘ
    (fun t ht ↦ hasDerivAt_arctan_circleContinuationSlope (hI ht) (hr t ht) hκ) ht₀ (by
      rw [sub_self, mul_zero, exp_zero, mul_one,
        arctan_tan (by linarith [(abs_lt.1 hψ).1]) (abs_lt.1 hψ).2]
      ring)

/-- **Constant solutions.** On an interval `I ⊆ (0, 1)` where the path is constant, `c`, a solution
which is at a critical angle of `δ cos (2 (θ - c))` at one time of `I` stays there. -/
theorem eqOn_const_of_hasDerivAt_circleContinuationSlope {δ c t₀ : ℝ} {r Θ : ℝ → ℝ}
    {I : Set ℝ} (hI : I ⊆ Ioo 0 1) (hIc : I.OrdConnected) (hr : ∀ t ∈ I, r t = c)
    (hΘ : ∀ t ∈ I, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (ht₀ : t₀ ∈ I)
    (hc : sin (2 * (Θ t₀ - c)) = 0) : EqOn Θ (fun _ ↦ Θ t₀) I :=
  eqOn_of_hasDerivAt_circleContinuationSlope hI hIc hΘ (fun t ht ↦ by
    rw [circleContinuationSlope_eq_zero (by rw [hr t ht]; exact hc)]
    exact hasDerivAt_const _ _) ht₀ rfl

/-- **Solutions at a constant end.** On a set `I ⊆ (0, 1)` where the path is constant, there is a
solution on `I` with any value `θ₀` at any time `t₀`. -/
theorem exists_hasDerivAt_circleContinuationSlope_of_forall_eq (δ : ℝ) {r : ℝ → ℝ} {c t₀ : ℝ}
    {I : Set ℝ} (hI : I ⊆ Ioo 0 1) (hr : ∀ t ∈ I, r t = c) (θ₀ : ℝ) :
    ∃ Θ : ℝ → ℝ, Θ t₀ = θ₀ ∧ ∀ t ∈ I, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t := by
  obtain ⟨n, hn⟩ := exists_abs_sub_int_mul_pi_le (θ₀ - c)
  rcases hn.lt_or_eq with hlt | heq
  · set κ := c + n * π
    have hκ : sin (2 * (κ - c)) = 0 := (sin_cos_two_mul_add_int_mul_pi_sub c n).1
    have hψ : |θ₀ - κ| < π / 2 := by rwa [show θ₀ - κ = θ₀ - c - n * π by ring]
    refine ⟨fun t ↦ κ + arctan (tan (θ₀ - κ) * exp (4 * δ * cos (2 * (κ - c)) *
      (intervalBaseTimeCoordinate t - intervalBaseTimeCoordinate t₀))), ?_,
      fun t ht ↦ hasDerivAt_arctan_circleContinuationSlope (hI ht) (hr t ht) hκ⟩
    simp only [sub_self, mul_zero, exp_zero, mul_one]
    rw [arctan_tan (by linarith [(abs_lt.1 hψ).1]) (abs_lt.1 hψ).2]
    ring
  · refine ⟨fun _ ↦ θ₀, rfl, fun t ht ↦ ?_⟩
    rw [circleContinuationSlope_eq_zero (by
      rw [hr t ht]; exact sin_two_mul_eq_zero_of_abs_sub_int_mul_pi_eq heq)]
    exact hasDerivAt_const _ _

/-! ### The end limits -/

/-- **The backward limit in the basin of a maximum.** For `δ > 0`, let the path be constant, `c`, on
`(0, a]`, and let a solution `Θ` on `(0, a]` satisfy `|Θ a - (c + m π)| < π / 2`. Then `Θ` tends to
the maximum `c + m π` of the source function at `t = 0`. -/
theorem tendsto_nhdsGT_zero_circleContinuationSlope {δ c a : ℝ} {r Θ : ℝ → ℝ} (hδ : 0 < δ)
    (ha : a ∈ Ioo 0 1) (hr : ∀ t ∈ Ioc 0 a, r t = c)
    (hΘ : ∀ t ∈ Ioc 0 a, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (m : ℤ)
    (hψ : |Θ a - (c + m * π)| < π / 2) : Tendsto Θ (𝓝[>] 0) (𝓝 (c + m * π)) := by
  have hI : Ioc 0 a ⊆ Ioo 0 1 := fun t ht ↦ ⟨ht.1, ht.2.trans_lt ha.2⟩
  obtain ⟨hκ, hσ⟩ := sin_cos_two_mul_add_int_mul_pi_sub c m
  have hEq := eqOn_arctan_of_hasDerivAt_circleContinuationSlope hI ordConnected_Ioc hr hΘ hκ
    ⟨ha.1, le_rfl⟩ hψ
  rw [hσ, mul_one] at hEq
  -- As `t → 0`, the time coordinate tends to `-∞`, so the exponential tends to `0`.
  have hexp : Tendsto (fun t ↦ exp (4 * δ * (intervalBaseTimeCoordinate t -
      intervalBaseTimeCoordinate a))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_exp_atBot.comp ((tendsto_intervalBaseTimeCoordinate_nhdsGT_zero.atBot_add
      tendsto_const_nhds).const_mul_atBot (by positivity))
  have hX := hexp.const_mul (tan (Θ a - (c + m * π)))
  rw [mul_zero] at hX
  have hlim := ((continuous_arctan.tendsto 0).comp hX).const_add (c + m * π)
  rw [arctan_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT ha.1] with t ht
  exact (hEq ht).symm

/-- **The forward limit in the basin of a minimum.** For `δ > 0`, let the path be constant, `c`, on
`[b, 1)`, and let a solution `Θ` on `[b, 1)` satisfy `|Θ b - (c + π / 2 + m π)| < π / 2`. Then `Θ`
tends to the minimum `c + π / 2 + m π` of the target function at `t = 1`. -/
theorem tendsto_nhdsLT_one_circleContinuationSlope {δ c b : ℝ} {r Θ : ℝ → ℝ} (hδ : 0 < δ)
    (hb : b ∈ Ioo 0 1) (hr : ∀ t ∈ Ico b 1, r t = c)
    (hΘ : ∀ t ∈ Ico b 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (m : ℤ)
    (hψ : |Θ b - (c + π / 2 + m * π)| < π / 2) : Tendsto Θ (𝓝[<] 1) (𝓝 (c + π / 2 + m * π)) := by
  have hI : Ico b 1 ⊆ Ioo 0 1 := fun t ht ↦ ⟨hb.1.trans_le ht.1, ht.2⟩
  obtain ⟨hκ, hσ⟩ := sin_cos_two_mul_add_pi_div_two_add_int_mul_pi_sub c m
  have hEq := eqOn_arctan_of_hasDerivAt_circleContinuationSlope hI ordConnected_Ico hr hΘ hκ
    ⟨le_rfl, hb.2⟩ hψ
  rw [hσ] at hEq
  -- As `t → 1`, the time coordinate tends to `+∞`, so the exponential tends to `0`.
  have hexp : Tendsto (fun t ↦ exp (4 * δ * -1 * (intervalBaseTimeCoordinate t -
      intervalBaseTimeCoordinate b))) (𝓝[<] 1) (𝓝 0) :=
    tendsto_exp_atBot.comp ((tendsto_intervalBaseTimeCoordinate_nhdsLT_one.atTop_add
      tendsto_const_nhds).const_mul_atTop_of_neg (by linarith))
  have hX := hexp.const_mul (tan (Θ b - (c + π / 2 + m * π)))
  rw [mul_zero] at hX
  have hlim := ((continuous_arctan.tendsto 0).comp hX).const_add (c + π / 2 + m * π)
  rw [arctan_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hb.2] with t ht
  exact (hEq ⟨ht.1.le, ht.2⟩).symm

/-- **Only constant solutions leave a source minimum.** For `δ > 0`, let the path be constant, `c`,
on `(0, a]`. A solution on `(0, a]` which tends at `t = 0` to a minimum `c + π / 2 + m π` of the
source function is constant there. -/
theorem eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope {δ c a : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (ha : a ∈ Ioo 0 1) (hr : ∀ t ∈ Ioc 0 a, r t = c)
    (hΘ : ∀ t ∈ Ioc 0 a, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (m : ℤ)
    (h : Tendsto Θ (𝓝[>] 0) (𝓝 (c + π / 2 + m * π))) :
    ∀ t ∈ Ioc 0 a, Θ t = c + π / 2 + m * π := by
  have hI : Ioc 0 a ⊆ Ioo 0 1 := fun t ht ↦ ⟨ht.1, ht.2.trans_lt ha.2⟩
  obtain ⟨n, hn⟩ := exists_abs_sub_int_mul_pi_le (Θ a - c)
  rcases hn.lt_or_eq with hlt | heq
  · -- Otherwise `Θ` would tend to the maximum `c + n π`.
    have h' := tendsto_nhdsGT_zero_circleContinuationSlope hδ ha hr hΘ n
      (by rwa [show Θ a - (c + n * π) = Θ a - c - n * π by ring])
    exact absurd (tendsto_nhds_unique h' h) (add_int_mul_pi_ne_add_pi_div_two_add_int_mul_pi c n m)
  · have hEq := eqOn_const_of_hasDerivAt_circleContinuationSlope hI ordConnected_Ioc hr hΘ
      ⟨ha.1, le_rfl⟩ (sin_two_mul_eq_zero_of_abs_sub_int_mul_pi_eq heq)
    have hc : Tendsto Θ (𝓝[>] 0) (𝓝 (Θ a)) :=
      tendsto_const_nhds.congr' (eventually_of_mem (Ioc_mem_nhdsGT ha.1) fun t ht ↦ (hEq ht).symm)
    intro t ht
    rw [hEq ht, tendsto_nhds_unique hc h]

/-- **Only constant solutions reach a target maximum.** For `δ > 0`, let the path be constant, `c`,
on `[b, 1)`. A solution on `[b, 1)` which tends at `t = 1` to a maximum `c + m π` of the target
function is constant there. -/
theorem eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope {δ c b : ℝ} {r Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hb : b ∈ Ioo 0 1) (hr : ∀ t ∈ Ico b 1, r t = c)
    (hΘ : ∀ t ∈ Ico b 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (m : ℤ)
    (h : Tendsto Θ (𝓝[<] 1) (𝓝 (c + m * π))) : ∀ t ∈ Ico b 1, Θ t = c + m * π := by
  have hI : Ico b 1 ⊆ Ioo 0 1 := fun t ht ↦ ⟨hb.1.trans_le ht.1, ht.2⟩
  obtain ⟨n, hn⟩ := exists_abs_sub_int_mul_pi_le (Θ b - c - π / 2)
  rcases hn.lt_or_eq with hlt | heq
  · -- Otherwise `Θ` would tend to the minimum `c + π / 2 + n π`.
    have h' := tendsto_nhdsLT_one_circleContinuationSlope hδ hb hr hΘ n
      (by rwa [show Θ b - (c + π / 2 + n * π) = Θ b - c - π / 2 - n * π by ring])
    exact absurd (tendsto_nhds_unique h h') (add_int_mul_pi_ne_add_pi_div_two_add_int_mul_pi c m n)
  · have hsin : sin (2 * (Θ b - c)) = 0 := by
      have := sin_two_mul_eq_zero_of_abs_sub_int_mul_pi_eq heq
      rwa [show 2 * (Θ b - c - π / 2) = 2 * (Θ b - c) - π by ring, sin_sub_pi, neg_eq_zero]
        at this
    have hEq := eqOn_const_of_hasDerivAt_circleContinuationSlope hI ordConnected_Ico hr hΘ
      ⟨le_rfl, hb.2⟩ hsin
    have hc : Tendsto Θ (𝓝[<] 1) (𝓝 (Θ b)) :=
      tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsLT hb.2) fun t ht ↦
        (hEq ⟨ht.1.le, ht.2⟩).symm)
    intro t ht
    rw [hEq ht, tendsto_nhds_unique hc h]

/-! ### Existence on `(0, 1)` -/

/-- **Existence of solutions on `(0, 1)`.** For a path `r` which is constant on `(0, a]` and on
`[b, 1)` and continuous on `[a, b]`, where `0 < a` and `b < 1`, the equation
`Θ' = circleContinuationSlope δ r t (Θ t)` has a solution on `(0, 1)` with any value at any time
`t₀ ∈ [a, b]`. -/
theorem exists_hasDerivAt_circleContinuationSlope (δ : ℝ) {r : ℝ → ℝ} {a b r₀ r₁ t₀ : ℝ}
    (ha : 0 < a) (hb : b < 1) (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) (ht₀ : t₀ ∈ Icc a b) (θ₀ : ℝ) :
    ∃ Θ : ℝ → ℝ, Θ t₀ = θ₀ ∧
      ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t := by
  -- Glue a solution on the window to the explicit solutions at the ends.
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  obtain ⟨Θm, hΘm₀, hΘm⟩ := exists_hasDerivWithinAt_circleContinuationSlope_Icc δ ha hb hr ht₀ θ₀
  obtain ⟨Θl, hΘl₀, hΘl⟩ := exists_hasDerivAt_circleContinuationSlope_of_forall_eq δ (t₀ := a)
    (I := Ioc 0 a) (fun t ht ↦ ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) hr₀ (Θm a)
  obtain ⟨Θr, hΘr₀, hΘr⟩ := exists_hasDerivAt_circleContinuationSlope_of_forall_eq δ (t₀ := b)
    (I := Ico b 1) (fun t ht ↦ ⟨ha.trans_le (hab.trans ht.1), ht.2⟩) hr₁ (Θm b)
  -- First glue the window solution to the solution on `[b, 1)`, on `[a, 1)`.
  have h₁ : ∀ t ∈ Ico a 1, HasDerivWithinAt (fun t ↦ if t ≤ b then Θm t else Θr t)
      (circleContinuationSlope δ r t (if t ≤ b then Θm t else Θr t)) (Ico a 1) t := fun t ht ↦ by
    rw [apply_ite (circleContinuationSlope δ r t)]
    exact hasDerivWithinAt_if_le (f' := fun t ↦ circleContinuationSlope δ r t (Θm t))
      (g' := fun t ↦ circleContinuationSlope δ r t (Θr t)) ht
      (fun htb ↦ (hΘm t ⟨ht.1, htb⟩).mono fun y (hy : y ∈ Ico a 1 ∩ Iic b) ↦ ⟨hy.1.1, hy.2⟩)
      (fun hbt ↦ (hΘr t ⟨hbt, ht.2⟩).hasDerivWithinAt) hΘr₀.symm (by rw [hΘr₀])
  -- Then glue the solution on `(0, a]` to it, on `(0, 1)`.
  refine ⟨fun t ↦ if t ≤ a then Θl t else if t ≤ b then Θm t else Θr t, ?_, fun t ht ↦ ?_⟩
  · rcases ht₀.1.eq_or_lt with rfl | hlt
    · simp [hΘl₀, hΘm₀]
    · simp [not_le.2 hlt, ht₀.2, hΘm₀]
  · have hglue : (if a ≤ b then Θm a else Θr a) = Θl a := by simp [hΘl₀, hab]
    rw [apply_ite (circleContinuationSlope δ r t)]
    exact (hasDerivWithinAt_if_le (f' := fun t ↦ circleContinuationSlope δ r t (Θl t))
      (g' := fun t ↦ circleContinuationSlope δ r t (if t ≤ b then Θm t else Θr t)) ht
      (fun hta ↦ (hΘl t ⟨ht.1, hta⟩).hasDerivWithinAt)
      (fun hat ↦ (h₁ t ⟨hat, ht.2⟩).mono fun y (hy : y ∈ Ioo 0 1 ∩ Ici a) ↦ ⟨hy.2, hy.1.2⟩)
      hglue.symm
      (by rw [hglue])).hasDerivAt (Ioo_mem_nhds ht.1 ht.2)

/-! ### Classification of the index-preserving trajectories -/

variable {δ a b r₀ r₁ : ℝ} {r Θ Θ₁ Θ₂ : ℝ → ℝ} {n : ℤ}

/-- The drift across the window bounds the displacement of a solution on `(0, 1)`. -/
private theorem abs_sub_le_drift (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) :
    |Θ b - Θ a| ≤ 2 * |δ| * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ :=
  abs_sub_le_integral_of_hasDerivWithinAt_circleContinuationSlope ha hab hb fun t ht ↦
    (hΘ t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).hasDerivWithinAt

/-- **Trajectories into a target maximum come from the source maximum `n` steps along.** For
`δ > 0`, let the path be `r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `|r₁ - r₀ - n π|` plus the
drift `2 δ ∫_a^b (t (1 - t²))⁻¹ dt` across the window be less than `π / 2`. A trajectory converging
at `t = 1` to the target maximum `r₁ + k π` comes at `t = 0` from the source maximum
`r₀ + (k + n) π`. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_max (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + (k + n) * π)) := by
  have hb' : b ∈ Ioo 0 1 := ⟨ha.trans_le hab, hb⟩
  have hΘb := eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope hδ hb' hr₁
    (fun t ht ↦ hΘ t ⟨hb'.1.trans_le ht.1, ht.2⟩) k h b ⟨le_rfl, hb⟩
  have hdrift := abs_sub_le_drift ha hab hb hΘ
  rw [abs_of_pos hδ] at hdrift
  have h' := tendsto_nhdsGT_zero_circleContinuationSlope hδ ⟨ha, hab.trans_lt hb⟩ hr₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) (k + n) (by
      push_cast
      calc |Θ a - (r₀ + (k + n) * π)| ≤ |Θ b - Θ a| + |r₁ - r₀ - n * π| := by
            rw [show Θ a - (r₀ + (k + n) * π) = -(Θ b - Θ a) + (r₁ - r₀ - n * π) by
              rw [hΘb]; ring]
            exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
        _ < π / 2 := by linarith)
  push_cast at h'
  exact h'

/-- **At most one trajectory reaches a target maximum.** For `δ > 0`, let the path be constant on
`[b, 1)`. Two trajectories converging at `t = 1` to the same target maximum agree on `(0, 1)`. -/
theorem eqOn_of_tendsto_nhdsLT_one_max (hδ : 0 < δ) (hb : b ∈ Ioo 0 1)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) (k : ℤ)
    (h₁ : Tendsto Θ₁ (𝓝[<] 1) (𝓝 (r₁ + k * π))) (h₂ : Tendsto Θ₂ (𝓝[<] 1) (𝓝 (r₁ + k * π))) :
    EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hI : Ico b 1 ⊆ Ioo 0 1 := fun t ht ↦ ⟨hb.1.trans_le ht.1, ht.2⟩
  refine eqOn_of_hasDerivAt_circleContinuationSlope subset_rfl ordConnected_Ioo hΘ₁ hΘ₂ hb ?_
  rw [eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope hδ hb hr₁ (fun t ht ↦ hΘ₁ t (hI ht)) k h₁
      b ⟨le_rfl, hb.2⟩,
    eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope hδ hb hr₁ (fun t ht ↦ hΘ₂ t (hI ht)) k h₂
      b ⟨le_rfl, hb.2⟩]

/-- **Every target maximum is reached.** For a path which is `r₀` on `(0, a]`, `r₁` on `[b, 1)` and
continuous on `[a, b]`, there is a trajectory converging at `t = 1` to the target maximum
`r₁ + k π`: the solution which is at `r₁ + k π` at time `b`. -/
theorem exists_tendsto_nhdsLT_one_max (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) (k : ℤ) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π)) := by
  obtain ⟨Θ, hΘb, hΘ⟩ := exists_hasDerivAt_circleContinuationSlope δ ha hb hr hr₀ hr₁
    ⟨hab, le_rfl⟩ (r₁ + k * π)
  have hEq := eqOn_const_of_hasDerivAt_circleContinuationSlope (I := Ico b 1)
    (fun t ht ↦ ⟨ha.trans_le (hab.trans ht.1), ht.2⟩) ordConnected_Ico hr₁
    (fun t ht ↦ hΘ t ⟨ha.trans_le (hab.trans ht.1), ht.2⟩) ⟨le_rfl, hb⟩
    (by rw [hΘb]; exact (sin_cos_two_mul_add_int_mul_pi_sub r₁ k).1)
  refine ⟨Θ, hΘ, ?_⟩
  rw [← hΘb]
  exact tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsLT hb) fun t ht ↦
    (hEq ⟨ht.1.le, ht.2⟩).symm)

/-- **Trajectories leaving a source minimum go to the target minimum `n` steps back.** For `δ > 0`,
let the path be `r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `|r₁ - r₀ - n π|` plus the drift
`2 δ ∫_a^b (t (1 - t²))⁻¹ dt` across the window be less than `π / 2`. A trajectory leaving the
source minimum `r₀ + π / 2 + (k + n) π` at `t = 0` converges at `t = 1` to the target minimum
`r₁ + π / 2 + k π`. -/
theorem tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_min (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + (k + n) * π))) :
    Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + π / 2 + k * π)) := by
  have ha' : a ∈ Ioo 0 1 := ⟨ha, hab.trans_lt hb⟩
  have hΘa := eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ ha' hr₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt ha'.2⟩) (k + n) (by push_cast; exact h) a ⟨ha, le_rfl⟩
  push_cast at hΘa
  have hdrift := abs_sub_le_drift ha hab hb hΘ
  rw [abs_of_pos hδ] at hdrift
  exact tendsto_nhdsLT_one_circleContinuationSlope hδ ⟨ha.trans_le hab, hb⟩ hr₁
    (fun t ht ↦ hΘ t ⟨ha.trans_le (hab.trans ht.1), ht.2⟩) k (by
      calc |Θ b - (r₁ + π / 2 + k * π)| ≤ |Θ b - Θ a| + |r₁ - r₀ - n * π| := by
            rw [show Θ b - (r₁ + π / 2 + k * π) = (Θ b - Θ a) - (r₁ - r₀ - n * π) by
              rw [hΘa]; ring]
            exact abs_sub _ _
        _ < π / 2 := by linarith)

/-- **At most one trajectory leaves a source minimum.** For `δ > 0`, let the path be constant on
`(0, a]`. Two trajectories leaving the same source minimum at `t = 0` agree on `(0, 1)`. -/
theorem eqOn_of_tendsto_nhdsGT_zero_min (hδ : 0 < δ) (ha : a ∈ Ioo 0 1)
    (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) (k : ℤ)
    (h₁ : Tendsto Θ₁ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + k * π)))
    (h₂ : Tendsto Θ₂ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + k * π))) : EqOn Θ₁ Θ₂ (Ioo 0 1) := by
  have hI : Ioc 0 a ⊆ Ioo 0 1 := fun t ht ↦ ⟨ht.1, ht.2.trans_lt ha.2⟩
  refine eqOn_of_hasDerivAt_circleContinuationSlope subset_rfl ordConnected_Ioo hΘ₁ hΘ₂ ha ?_
  rw [eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ ha hr₀ (fun t ht ↦ hΘ₁ t (hI ht)) k h₁
      a ⟨ha.1, le_rfl⟩,
    eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ ha hr₀ (fun t ht ↦ hΘ₂ t (hI ht)) k h₂
      a ⟨ha.1, le_rfl⟩]

/-- **Every source minimum is left by a trajectory.** For a path which is `r₀` on `(0, a]`, `r₁` on
`[b, 1)` and continuous on `[a, b]`, there is a trajectory leaving the source minimum
`r₀ + π / 2 + k π` at `t = 0`: the solution which is at `r₀ + π / 2 + k π` at time `a`. -/
theorem exists_tendsto_nhdsGT_zero_min (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) (k : ℤ) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + k * π)) := by
  obtain ⟨Θ, hΘa, hΘ⟩ := exists_hasDerivAt_circleContinuationSlope δ ha hb hr hr₀ hr₁
    ⟨le_rfl, hab⟩ (r₀ + π / 2 + k * π)
  have hEq := eqOn_const_of_hasDerivAt_circleContinuationSlope (I := Ioc 0 a)
    (fun t ht ↦ ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) ordConnected_Ioc hr₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt (hab.trans_lt hb)⟩) ⟨ha, le_rfl⟩
    (by rw [hΘa]; exact (sin_cos_two_mul_add_pi_div_two_add_int_mul_pi_sub r₀ k).1)
  refine ⟨Θ, hΘ, ?_⟩
  rw [← hΘa]
  exact tendsto_const_nhds.congr' (eventually_of_mem (Ioc_mem_nhdsGT ha) fun t ht ↦
    (hEq ht).symm)

/-- **No trajectory runs from a source minimum to a target maximum.** For `δ > 0`, let the path be
`r₀` on `(0, a]` and `r₁` on `[b, 1)`, and let `|r₁ - r₀ - n π|` plus the drift
`2 δ ∫_a^b (t (1 - t²))⁻¹ dt` across the window be less than `π / 2`. Then no trajectory leaves a
source minimum at `t = 0` and converges to a target maximum at `t = 1`. Such connections between
zeros of equal index of the parameter field would have expected dimension `-1`. -/
theorem not_tendsto_nhdsGT_zero_min_and_tendsto_nhdsLT_one_max (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (j k : ℤ) :
    ¬ (Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + π / 2 + j * π)) ∧ Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) := by
  -- Both ends would be constant, at angles at least `π / 2 - |r₁ - r₀ - n π|` apart, which is
  -- more than the drift.
  rintro ⟨h₀, h₁⟩
  have ha' : a ∈ Ioo 0 1 := ⟨ha, hab.trans_lt hb⟩
  have hb' : b ∈ Ioo 0 1 := ⟨ha.trans_le hab, hb⟩
  have hΘa := eqOn_of_tendsto_nhdsGT_zero_circleContinuationSlope hδ ha' hr₀
    (fun t ht ↦ hΘ t ⟨ht.1, ht.2.trans_lt ha'.2⟩) j h₀ a ⟨ha, le_rfl⟩
  have hΘb := eqOn_of_tendsto_nhdsLT_one_circleContinuationSlope hδ hb' hr₁
    (fun t ht ↦ hΘ t ⟨hb'.1.trans_le ht.1, ht.2⟩) k h₁ b ⟨le_rfl, hb⟩
  have hdrift := abs_sub_le_drift ha hab hb hΘ
  rw [abs_of_pos hδ, hΘa, hΘb] at hdrift
  have hN := pi_div_two_le_abs_int_mul_pi_sub_pi_div_two (k + n - j)
  have h' : |((k + n - j : ℤ) : ℝ) * π - π / 2| ≤
      |r₁ + k * π - (r₀ + π / 2 + j * π)| + |r₁ - r₀ - n * π| := by
    rw [show ((k + n - j : ℤ) : ℝ) * π - π / 2 =
      (r₁ + k * π - (r₀ + π / 2 + j * π)) - (r₁ - r₀ - n * π) by push_cast; ring]
    exact abs_sub _ _
  linarith

/-! ### The half turn -/

/-- **The continuation map of the half turn is the identity on maxima.** Along the half turn
`r = π ρ`, with `ρ = 0` on `(0, a]` and `ρ = 1` on `[b, 1)`, the end functions `δ cos (2 θ)` and
`δ cos (2 (θ - π))` agree. If the drift `2 δ ∫_a^b (t (1 - t²))⁻¹ dt` is less than `π / 2`, a
trajectory converging at `t = 1` to a maximum `k π` comes from the same maximum `k π` at `t = 0`,
although tracking the maxima `π ρ(t) + j π` along the path moves `k π` to `(k + 1) π`. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_halfTurn {ρ : ℝ → ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hρ₀ : ∀ t ∈ Ioc 0 a, ρ t = 0) (hρ₁ : ∀ t ∈ Ico b 1, ρ t = 1)
    (hdrift : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[<] 1) (𝓝 (k * π))) : Tendsto Θ (𝓝[>] 0) (𝓝 (k * π)) := by
  have h' := tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_max (r₀ := 0) (r₁ := π) (n := 1) hδ ha hab
    hb (fun t ht ↦ by simp [hρ₀ t ht]) (fun t ht ↦ by simp [hρ₁ t ht]) (by simpa using hdrift)
    hΘ (k - 1) (by convert h using 2; push_cast; ring)
  convert h' using 2
  push_cast
  ring

/-- **The continuation map of the half turn is the identity on minima.** Along the half turn
`r = π ρ`, with `ρ = 0` on `(0, a]` and `ρ = 1` on `[b, 1)`, if the drift
`2 δ ∫_a^b (t (1 - t²))⁻¹ dt` is less than `π / 2`, a trajectory leaving a minimum `π / 2 + k π` at
`t = 0` converges to the same minimum `π / 2 + k π` at `t = 1`. -/
theorem tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_halfTurn {ρ : ℝ → ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hρ₀ : ∀ t ∈ Ioc 0 a, ρ t = 0) (hρ₁ : ∀ t ∈ Ico b 1, ρ t = 1)
    (hdrift : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ π * ρ t) t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[>] 0) (𝓝 (π / 2 + k * π))) : Tendsto Θ (𝓝[<] 1) (𝓝 (π / 2 + k * π)) := by
  have h' := tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_min (r₀ := 0) (r₁ := π) (n := 1) hδ ha hab
    hb (fun t ht ↦ by simp [hρ₀ t ht]) (fun t ht ↦ by simp [hρ₁ t ht]) (by simpa using hdrift)
    hΘ (k - 1) (by convert h using 2; push_cast; ring)
  convert h' using 2
  push_cast
  ring

/-! ### Rotations by a sixth and a third of a turn -/

/-- **A rotation by `π / 3` continues each maximum to the same label.** If the path rotates by
`r₁ - r₀ = π / 3` and the drift `2 δ ∫_a^b (t (1 - t²))⁻¹ dt` is less than `π / 6`, a trajectory
converging at `t = 1` to the target maximum `r₁ + k π` comes from the source maximum `r₀ + k π`:
in the labels `r + j π`, `j mod 2`, of the maxima, the continuation map is the identity. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_sixthTurn (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hr : r₁ - r₀ = π / 3) (hdrift : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 6)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + k * π)) := by
  have h' := tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_max (n := 0) hδ ha hab hb hr₀ hr₁ (by
    rw [hr, Int.cast_zero, zero_mul, sub_zero, abs_of_pos (by positivity)]
    linarith) hΘ k h
  simpa using h'

/-- **A rotation by `2 π / 3` exchanges the labels of the maxima.** If the path rotates by
`r₁ - r₀ = 2 π / 3` and the drift `2 δ ∫_a^b (t (1 - t²))⁻¹ dt` is less than `π / 6`, a trajectory
converging at `t = 1` to the target maximum `r₁ + k π` comes from the source maximum
`r₀ + (k + 1) π`: in the labels `r + j π`, `j mod 2`, of the maxima, the continuation map is the
exchange. Composing two rotations by `π / 3`, each with identity continuation map
(`TauCeti.tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_sixthTurn`), therefore does not give the
continuation map of the composite rotation. -/
theorem tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_thirdTurn (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hr : r₁ - r₀ = 2 * π / 3) (hdrift : 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 6)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (k : ℤ)
    (h : Tendsto Θ (𝓝[<] 1) (𝓝 (r₁ + k * π))) : Tendsto Θ (𝓝[>] 0) (𝓝 (r₀ + (k + 1) * π)) := by
  have h' := tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_max (n := 1) hδ ha hab hb hr₀ hr₁ (by
    rw [hr, Int.cast_one, one_mul, show 2 * π / 3 - π = -(π / 3) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith) hΘ k h
  simpa using h'

end TauCeti
