/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Topology.Circle.AddCircle

/-!
# The Morse function `δ cos (2 (θ - r))` on the circle

On the circle `ℝ ⧸ 2πℤ` with angle `θ`, the function `f_r(θ) = δ cos (2 (θ - r))`
(`TauCeti.circleCosTwo δ r`) is, for `δ ≠ 0`, a Morse function with two maxima and two minima. Its
rotations `f_{r(t)}` along a path `t ↦ r(t)` are the end functions of the circle continuation
examples of Morse homology, whose parameter field `TauCeti.circleContinuationField` is studied on
the universal cover in `TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basic`.

For `δ > 0` the critical points are labelled as in those examples: the maxima
`p_j = r + j π` (`TauCeti.circleCosTwoMax r j`) and the minima `q_j = r + π / 2 + j π`
(`TauCeti.circleCosTwoMin r j`), for `j ∈ {0, 1}`. In the preferred chart at any point, whose
coordinate is a local real lift of the angle, the function reads `y ↦ δ cos (2 (y - r))`, with
second derivative `-4 δ cos (2 (y - r))`. So the critical points are the angles with
`sin (2 (θ - r)) = 0`, each of them nondegenerate, of Morse index `1` at the maxima, where
`cos (2 (θ - r)) = 1`, and `0` at the minima, where `cos (2 (θ - r)) = -1`.

## Main declarations

* `TauCeti.circleCosTwo`: the function `θ ↦ δ cos (2 (θ - r))` on `AddCircle (2 * π)`.
* `TauCeti.circleCosTwoMax`, `TauCeti.circleCosTwoMin`: the angles `r + j π` and
  `r + π / 2 + j π`.
* `TauCeti.isMorse_circleCosTwo`: for `δ ≠ 0` it is a Morse function.
* `TauCeti.manifoldMorseIndex_circleCosTwoMax`, `TauCeti.manifoldMorseIndex_circleCosTwoMin`: for
  `δ > 0` the maxima have index `1` and the minima index `0`.
* `TauCeti.eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero`: for `δ > 0` every critical point of
  index `0` is one of the two minima.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Set Filter Function Topology AddCircle
open scoped Manifold ContDiff Real

namespace TauCeti

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The function `θ ↦ δ cos (2 (θ - r))` on the circle `ℝ ⧸ 2πℤ`, written with the real part of
`AddCircle.toCircle`. -/
noncomputable def circleCosTwo (δ r : ℝ) (θ : AddCircle (2 * π)) : ℝ :=
  δ * (toCircle (2 • (θ - (r : AddCircle (2 * π)))) : ℂ).re

/-- At the class of a real number `t`, the function is `δ cos (2 (t - r))`. -/
@[simp]
theorem circleCosTwo_coe (δ r t : ℝ) :
    circleCosTwo δ r (t : AddCircle (2 * π)) = δ * Real.cos (2 * (t - r)) := by
  rw [circleCosTwo, ← coe_sub, ← coe_nsmul, re_toCircle_coe, nsmul_eq_mul,
    div_self Real.two_pi_pos.ne', one_mul, Nat.cast_ofNat]

/-- The maximum `r + j π` of `θ ↦ δ cos (2 (θ - r))`, for `δ > 0` and `j ∈ {0, 1}`. -/
noncomputable def circleCosTwoMax (r : ℝ) (j : Fin 2) : AddCircle (2 * π) :=
  ((r + j * π : ℝ) : AddCircle (2 * π))

/-- The minimum `r + π / 2 + j π` of `θ ↦ δ cos (2 (θ - r))`, for `δ > 0` and `j ∈ {0, 1}`. -/
noncomputable def circleCosTwoMin (r : ℝ) (j : Fin 2) : AddCircle (2 * π) :=
  ((r + π / 2 + j * π : ℝ) : AddCircle (2 * π))

/-- The angles `a` and `a + π` are different points of the circle. -/
private theorem coe_add_pi_ne (a : ℝ) :
    ((a + π : ℝ) : AddCircle (2 * π)) ≠ (a : AddCircle (2 * π)) :=
  fun h ↦ coe_half_period_ne_zero Real.two_pi_pos.ne' <| by
    rw [show (2 * π / 2 : ℝ) = a + π - a by ring, coe_sub, h, sub_self]

/-- The two maxima are different. -/
theorem circleCosTwoMax_injective (r : ℝ) : Injective (circleCosTwoMax r) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact ((coe_add_pi_ne r) (by simpa [circleCosTwoMax] using hij.symm)).elim
  · exact ((coe_add_pi_ne r) (by simpa [circleCosTwoMax] using hij)).elim
  · rfl

/-- The two minima are different. -/
theorem circleCosTwoMin_injective (r : ℝ) : Injective (circleCosTwoMin r) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact ((coe_add_pi_ne (r + π / 2)) (by simpa [circleCosTwoMin] using hij.symm)).elim
  · exact ((coe_add_pi_ne (r + π / 2)) (by simpa [circleCosTwoMin] using hij)).elim
  · rfl

/-! ### The function in charts -/

/-- **The function in the preferred charts.** Near the image of `x` in its preferred chart, the
coordinate expression of `θ ↦ δ cos (2 (θ - r))` is `y ↦ δ cos (2 (y - r))`. -/
theorem circleCosTwo_comp_extChartAt_symm_eventuallyEq (δ r : ℝ) (x : AddCircle (2 * π)) :
    circleCosTwo δ r ∘ (extChartAt 𝓘(ℝ) x).symm
      =ᶠ[𝓝 (extChartAt 𝓘(ℝ) x x)] fun y ↦ δ * Real.cos (2 * (y - r)) := by
  filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ)) x] with y hy
  rw [comp_apply, AddCircle.extChartAt_symm_apply x hy, circleCosTwo_coe]

/-- The derivative of `y ↦ δ cos (2 (y - r))` is `y ↦ -2 δ sin (2 (y - r))`. -/
private theorem hasDerivAt_cos_two (δ r y : ℝ) :
    HasDerivAt (fun y ↦ δ * Real.cos (2 * (y - r))) (-(2 * δ) * Real.sin (2 * (y - r))) y := by
  exact ((((hasDerivAt_id y).sub_const r).const_mul 2).cos.const_mul δ).congr_deriv
    (by simp only [id]; ring)

/-- The derivative of `y ↦ -2 δ sin (2 (y - r))` is `y ↦ -4 δ cos (2 (y - r))`. -/
private theorem hasDerivAt_sin_two (δ r y : ℝ) :
    HasDerivAt (fun y ↦ -(2 * δ) * Real.sin (2 * (y - r))) (-(4 * δ) * Real.cos (2 * (y - r)))
      y := by
  exact ((((hasDerivAt_id y).sub_const r).const_mul 2).sin.const_mul (-(2 * δ))).congr_deriv
    (by simp only [id]; ring)

private theorem deriv_cos_two (δ r : ℝ) :
    deriv (fun y ↦ δ * Real.cos (2 * (y - r))) = fun y ↦ -(2 * δ) * Real.sin (2 * (y - r)) :=
  funext fun y ↦ (hasDerivAt_cos_two δ r y).deriv

private theorem iteratedDeriv_two_cos_two (δ r y : ℝ) :
    iteratedDeriv 2 (fun y ↦ δ * Real.cos (2 * (y - r))) y = -(4 * δ) * Real.cos (2 * (y - r)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cos_two]
  exact (hasDerivAt_sin_two δ r y).deriv

/-- The function `θ ↦ δ cos (2 (θ - r))` is smooth. -/
theorem contMDiff_circleCosTwo (δ r : ℝ) : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (circleCosTwo δ r) := fun x ↦
  contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
    ContDiffAt.congr_of_eventuallyEq (by fun_prop)
      (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x)

/-- At a point `x` of the circle with lift `y`, the angle `2 (y - r)` has the sine and cosine of the
class of `2 (θ - r)`; these do not depend on the lift. -/
private theorem sin_two_eq_of_coe_eq {x : AddCircle (2 * π)} {y : ℝ}
    (hy : (y : AddCircle (2 * π)) = x) (r : ℝ) :
    Real.sin (2 * (y - r)) = (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).im := by
  rw [← hy, ← coe_sub, ← coe_nsmul, im_toCircle_coe, nsmul_eq_mul, div_self Real.two_pi_pos.ne',
    one_mul, Nat.cast_ofNat]

private theorem cos_two_eq_of_coe_eq {x : AddCircle (2 * π)} {y : ℝ}
    (hy : (y : AddCircle (2 * π)) = x) (r : ℝ) :
    Real.cos (2 * (y - r)) = (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).re := by
  rw [← hy, ← coe_sub, ← coe_nsmul, re_toCircle_coe, nsmul_eq_mul, div_self Real.two_pi_pos.ne',
    one_mul, Nat.cast_ofNat]

/-- **The critical points** of `θ ↦ δ cos (2 (θ - r))`, for `δ ≠ 0`, are the angles with
`sin (2 (θ - r)) = 0`. -/
theorem mem_criticalPoints_circleCosTwo_iff {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ) {x : AddCircle (2 * π)} :
    x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) ↔
      (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).im = 0 := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x).fderiv_eq,
    (hasDerivAt_cos_two δ r _).hasFDerivAt.fderiv,
    ← sin_two_eq_of_coe_eq (coe_extChartAt_self x) r]
  have h0 (v : ℝ) : ContinuousLinearMap.toSpanSingleton ℝ v = 0 ↔ v = 0 :=
    ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩
  rw [h0, mul_eq_zero, or_iff_right (by simpa using hδ)]

/-- **The function `θ ↦ δ cos (2 (θ - r))` is a Morse function** for `δ ≠ 0`: at its critical
points the cosine of `2 (θ - r)` is `±1`, so the second derivative `-4 δ cos (2 (θ - r))` does not
vanish. -/
theorem isMorse_circleCosTwo {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ) : IsMorse 𝓘(ℝ) (circleCosTwo δ r) := by
  refine isMorse_iff.2 ⟨contMDiff_circleCosTwo δ r, fun x hx ↦ ?_⟩
  have hcrit := (mem_criticalPoints_circleCosTwo_iff hδ r).1
    (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2 hx)
  rw [isManifoldNondegenerateCriticalPoint_iff]
  refine IsNondegenerateCriticalPoint.congr_of_eventuallyEq ?_
    (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x).symm
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop), (hasDerivAt_cos_two δ r _).deriv,
    iteratedDeriv_two_cos_two, sin_two_eq_of_coe_eq (coe_extChartAt_self x) r, hcrit, mul_zero]
  refine ⟨rfl, mul_ne_zero (by simpa using hδ) fun hcos ↦ ?_⟩
  -- The sine and the cosine of `2 (θ - r)` cannot vanish together.
  have := Real.sin_sq_add_cos_sq (2 * (extChartAt 𝓘(ℝ) x x - r))
  rw [sin_two_eq_of_coe_eq (coe_extChartAt_self x) r, hcrit, hcos] at this
  norm_num at this

/-- The Morse index of `θ ↦ δ cos (2 (θ - r))` at a critical point is `1` where the cosine of
`2 (θ - r)` is positive and `0` where it is negative, for `δ > 0`. -/
private theorem manifoldMorseIndex_circleCosTwo_of_lift (δ r : ℝ) (x : AddCircle (2 * π)) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) x =
      morseIndex (fun y ↦ δ * Real.cos (2 * (y - r))) (extChartAt 𝓘(ℝ) x x) := by
  rw [manifoldMorseIndex_def,
    morseIndex_congr_of_eventuallyEq (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x)]

/-- The class of `a + 2 k π` is the class of `a`. -/
private theorem coe_add_int_mul_two_pi (a : ℝ) (k : ℤ) :
    ((a + k * (2 * π) : ℝ) : AddCircle (2 * π)) = a := by
  rw [coe_add, ← zsmul_eq_mul, coe_zsmul, coe_period, smul_zero, add_zero]

/-- The maxima `r + j π` are critical points of index `1`, for `δ > 0`. -/
theorem circleCosTwoMax_mem_criticalPoints {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ) (j : Fin 2) :
    circleCosTwoMax r j ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) := by
  rw [mem_criticalPoints_circleCosTwo_iff hδ r,
    ← sin_two_eq_of_coe_eq (x := circleCosTwoMax r j) (y := r + j * π) rfl r,
    show 2 * (r + (j : ℝ) * π - r) = ((2 * (j : ℕ) : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi]

/-- The minima `r + π / 2 + j π` are critical points of index `0`, for `δ > 0`. -/
theorem circleCosTwoMin_mem_criticalPoints {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ) (j : Fin 2) :
    circleCosTwoMin r j ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) := by
  rw [mem_criticalPoints_circleCosTwo_iff hδ r,
    ← sin_two_eq_of_coe_eq (x := circleCosTwoMin r j) (y := r + π / 2 + j * π) rfl r,
    show 2 * (r + π / 2 + (j : ℝ) * π - r) = ((2 * (j : ℕ) + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi]

/-- **The maxima have Morse index `1`.** -/
theorem manifoldMorseIndex_circleCosTwoMax {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMax r j) = 1 := by
  rw [manifoldMorseIndex_circleCosTwo_of_lift]
  refine morseIndex_real_of_neg ?_
  rw [iteratedDeriv_two_cos_two, cos_two_eq_of_coe_eq (coe_extChartAt_self _) r,
    ← cos_two_eq_of_coe_eq (x := circleCosTwoMax r j) (y := r + j * π) rfl r,
    show 2 * (r + (j : ℝ) * π - r) = ((j : ℕ) : ℝ) * (2 * π) by ring,
    Real.cos_nat_mul_two_pi, mul_one]
  linarith

/-- **The minima have Morse index `0`.** -/
theorem manifoldMorseIndex_circleCosTwoMin {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMin r j) = 0 := by
  rw [manifoldMorseIndex_circleCosTwo_of_lift]
  refine morseIndex_real_of_pos ?_
  rw [iteratedDeriv_two_cos_two, cos_two_eq_of_coe_eq (coe_extChartAt_self _) r,
    ← cos_two_eq_of_coe_eq (x := circleCosTwoMin r j) (y := r + π / 2 + j * π) rfl r,
    show 2 * (r + π / 2 + (j : ℝ) * π - r) = π + ((j : ℕ) : ℝ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_pi]
  linarith

/-- **The critical points of index `0` are the two minima**, for `δ > 0`: at a critical point of
index `0` the cosine of `2 (θ - r)` is `-1`, so `θ` is `r + π / 2` or `r + 3π / 2` modulo `2π`. -/
theorem eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero {δ : ℝ} (hδ : 0 < δ) (r : ℝ)
    {x : AddCircle (2 * π)} (hx : x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r))
    (hind : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) x = 0) :
    ∃ j, x = circleCosTwoMin r j := by
  set y := extChartAt 𝓘(ℝ) x x
  have hy : (y : AddCircle (2 * π)) = x := coe_extChartAt_self x
  have hsin : Real.sin (2 * (y - r)) = 0 := by
    rw [sin_two_eq_of_coe_eq hy r]
    exact (mem_criticalPoints_circleCosTwo_iff hδ.ne' r).1 hx
  -- The cosine is `±1`, and it is not `1`, where the index would be `1`.
  have hcos : Real.cos (2 * (y - r)) ≠ 1 := fun hcos ↦ by
    rw [manifoldMorseIndex_circleCosTwo_of_lift,
      morseIndex_real_of_neg (by rw [iteratedDeriv_two_cos_two, hcos]; linarith)] at hind
    exact one_ne_zero hind
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  -- So `2 (y - r) = k π` with `k` odd.
  have hodd : Odd k := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | h
    · refine (hcos ?_).elim
      rw [← hk, show ((m + m : ℤ) : ℝ) * π = (m : ℝ) * (2 * π) by push_cast; ring,
        Real.cos_int_mul_two_pi]
    · exact h
  obtain ⟨m, rfl⟩ := hodd
  -- Write `m = 2 n` or `m = 2 n + 1`.
  rcases Int.even_or_odd m with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · refine ⟨0, ?_⟩
    rw [← hy, circleCosTwoMin, ← coe_add_int_mul_two_pi (r + π / 2 + ((0 : Fin 2) : ℝ) * π) n]
    congr 1
    push_cast at hk
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    linear_combination -hk / 2
  · refine ⟨1, ?_⟩
    rw [← hy, circleCosTwoMin, ← coe_add_int_mul_two_pi (r + π / 2 + ((1 : Fin 2) : ℝ) * π) n]
    congr 1
    push_cast at hk
    simp only [Fin.val_one, Nat.cast_one, one_mul]
    linear_combination -hk / 2

end TauCeti
