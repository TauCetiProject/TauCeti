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
import TauCeti.Algebra.AddCircle
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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
* `TauCeti.circleCosTwoMax_inj`, `TauCeti.circleCosTwoMin_inj`,
  `TauCeti.circleCosTwoMax_ne_circleCosTwoMin`: the four labelled angles are distinct.
* `TauCeti.exists_circleCosTwoMax_eq`, `TauCeti.exists_circleCosTwoMin_eq`: every lifted maximum
  `r + j π` and minimum `r + π / 2 + j π`, `j ∈ ℤ`, is one of them.
* `TauCeti.circleCosTwoMax_add_coe`, `TauCeti.circleCosTwoMin_add_coe`,
  `TauCeti.circleCosTwoMax_sub_coe`: rotating the function moves the labelled points with it.
* `TauCeti.circleCosTwo_add_pi`: rotating the function by `π` does not change it;
  `TauCeti.circleCosTwoMax_add_pi`, `TauCeti.circleCosTwoMin_add_pi`: it exchanges the labels.
* `TauCeti.circleCosTwoMaxCrit`, `TauCeti.circleCosTwoMinCrit`: the same points as elements of
  the set of critical points, the basis elements of the Morse complex;
  `TauCeti.circleCosTwoMaxCrit_ne_circleCosTwoMinCrit`: a maximum is never a minimum among them.
* `TauCeti.mvfderiv_circleCosTwo_coe`: its differential at the class of `t` is multiplication
  by `-2 δ sin (2 (t - r))`.
* `TauCeti.isMorse_circleCosTwo`: for `δ ≠ 0` it is a Morse function.
* `TauCeti.mem_criticalPoints_circleCosTwo_iff_exists`: for `δ ≠ 0` its critical points are the
  two maxima and the two minima.
* `TauCeti.manifoldMorseIndex_circleCosTwoMax`, `TauCeti.manifoldMorseIndex_circleCosTwoMin`: for
  `δ > 0` the maxima have index `1` and the minima index `0`; likewise
  `TauCeti.manifoldMorseIndex_circleCosTwoMaxCrit` and
  `TauCeti.manifoldMorseIndex_circleCosTwoMinCrit` for the critical points.
* `TauCeti.exists_eq_circleCosTwoMax_of_manifoldMorseIndex_eq_one`,
  `TauCeti.exists_eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero`: for `δ > 0` every critical
  point of index `1` is one of the two maxima, and every critical point of index `0` is one of the
  two minima.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Set Filter Function Topology AddCircle
open scoped Manifold ContDiff Real

namespace TauCeti

local instance morseCircleTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The function `θ ↦ δ cos (2 (θ - r))` on the circle `ℝ ⧸ 2πℤ`, written with the real part of
`AddCircle.toCircle`. -/
noncomputable def circleCosTwo (δ r : ℝ) (θ : AddCircle (2 * π)) : ℝ :=
  δ * (toCircle (2 • (θ - (r : AddCircle (2 * π)))) : ℂ).re

/-- At the class of a real number `t`, the point `2 (θ - r)` of the circle is
`exp (2 (t - r) i)`. -/
private theorem toCircle_two_nsmul_coe_sub (t r : ℝ) :
    toCircle (2 • ((t : AddCircle (2 * π)) - (r : AddCircle (2 * π)))) =
      Circle.exp (2 * (t - r)) := by
  rw [← coe_sub, ← coe_nsmul, toCircle_apply_mk, nsmul_eq_mul, div_self Real.two_pi_pos.ne',
    one_mul, Nat.cast_ofNat]

/-- At the class of a real number `t`, the function is `δ cos (2 (t - r))`. -/
@[simp]
theorem circleCosTwo_coe (δ r t : ℝ) :
    circleCosTwo δ r (t : AddCircle (2 * π)) = δ * Real.cos (2 * (t - r)) := by
  rw [circleCosTwo, toCircle_two_nsmul_coe_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- The maximum `r + j π` of `θ ↦ δ cos (2 (θ - r))`, for `δ > 0` and `j ∈ {0, 1}`. -/
noncomputable def circleCosTwoMax (r : ℝ) (j : Fin 2) : AddCircle (2 * π) :=
  ((r + j * π : ℝ) : AddCircle (2 * π))

/-- The minimum `r + π / 2 + j π` of `θ ↦ δ cos (2 (θ - r))`, for `δ > 0` and `j ∈ {0, 1}`. -/
noncomputable def circleCosTwoMin (r : ℝ) (j : Fin 2) : AddCircle (2 * π) :=
  ((r + π / 2 + j * π : ℝ) : AddCircle (2 * π))

/-- The maximum `circleCosTwoMax r j` is the class of `r + j π`. -/
theorem circleCosTwoMax_def (r : ℝ) (j : Fin 2) :
    circleCosTwoMax r j = ((r + j * π : ℝ) : AddCircle (2 * π)) := by
  rw [circleCosTwoMax]

/-- The minimum `circleCosTwoMin r j` is the class of `r + π / 2 + j π`. -/
theorem circleCosTwoMin_def (r : ℝ) (j : Fin 2) :
    circleCosTwoMin r j = ((r + π / 2 + j * π : ℝ) : AddCircle (2 * π)) := by
  rw [circleCosTwoMin]

/-- At the maxima, the point `2 (θ - r)` of the circle is `1`. -/
private theorem toCircle_two_nsmul_circleCosTwoMax_sub (r : ℝ) (j : Fin 2) :
    (toCircle (2 • (circleCosTwoMax r j - (r : AddCircle (2 * π)))) : ℂ) = 1 := by
  rw [circleCosTwoMax_def, toCircle_two_nsmul_coe_sub,
    show 2 * (r + (j : ℝ) * π - r) = ((j : ℕ) : ℤ) * (2 * π) by push_cast; ring,
    Circle.exp_int_mul_two_pi, Circle.coe_one]

/-- At the minima, the point `2 (θ - r)` of the circle is `-1`. -/
private theorem toCircle_two_nsmul_circleCosTwoMin_sub (r : ℝ) (j : Fin 2) :
    (toCircle (2 • (circleCosTwoMin r j - (r : AddCircle (2 * π)))) : ℂ) = -1 := by
  rw [circleCosTwoMin_def, toCircle_two_nsmul_coe_sub,
    show 2 * (r + π / 2 + (j : ℝ) * π - r) = π + ((j : ℕ) : ℤ) * (2 * π) by push_cast; ring,
    Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one, Circle.coe_exp, Complex.exp_pi_mul_I]

/-- The value of `θ ↦ δ cos (2 (θ - r))` at the maxima is `δ`. -/
@[simp]
theorem circleCosTwo_circleCosTwoMax (δ r : ℝ) (j : Fin 2) :
    circleCosTwo δ r (circleCosTwoMax r j) = δ := by
  rw [circleCosTwo, toCircle_two_nsmul_circleCosTwoMax_sub, Complex.one_re, mul_one]

/-- The value of `θ ↦ δ cos (2 (θ - r))` at the minima is `-δ`. -/
@[simp]
theorem circleCosTwo_circleCosTwoMin (δ r : ℝ) (j : Fin 2) :
    circleCosTwo δ r (circleCosTwoMin r j) = -δ := by
  rw [circleCosTwo, toCircle_two_nsmul_circleCosTwoMin_sub, Complex.neg_re, Complex.one_re,
    mul_neg_one]

/-- A maximum is never a minimum: the function takes the values `1` and `-1` there for `δ = 1`. -/
@[simp]
theorem circleCosTwoMax_ne_circleCosTwoMin (r : ℝ) (i j : Fin 2) :
    circleCosTwoMax r i ≠ circleCosTwoMin r j := fun h ↦ by
  have := circleCosTwo_circleCosTwoMin 1 r j
  rw [← h, circleCosTwo_circleCosTwoMax] at this
  norm_num at this

/-- A minimum is never a maximum. -/
@[simp]
theorem circleCosTwoMin_ne_circleCosTwoMax (r : ℝ) (i j : Fin 2) :
    circleCosTwoMin r i ≠ circleCosTwoMax r j :=
  (circleCosTwoMax_ne_circleCosTwoMin r j i).symm

/-- The angles `a` and `a + π` are different points of the circle. -/
private theorem coe_add_pi_ne (a : ℝ) :
    ((a + π : ℝ) : AddCircle (2 * π)) ≠ (a : AddCircle (2 * π)) := by
  simpa using coe_add_half_period_ne Real.two_pi_pos.ne' a

/-- The two maxima are different. -/
theorem circleCosTwoMax_injective (r : ℝ) : Injective (circleCosTwoMax r) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact ((coe_add_pi_ne r) (by simpa [circleCosTwoMax_def] using hij.symm)).elim
  · exact ((coe_add_pi_ne r) (by simpa [circleCosTwoMax_def] using hij)).elim
  · rfl

/-- The two minima are different. -/
theorem circleCosTwoMin_injective (r : ℝ) : Injective (circleCosTwoMin r) := by
  -- The minima for `r` are the maxima for `r + π / 2`.
  have : circleCosTwoMin r = circleCosTwoMax (r + π / 2) :=
    funext fun j ↦ by rw [circleCosTwoMin_def, circleCosTwoMax_def]
  rw [this]
  exact circleCosTwoMax_injective (r + π / 2)

/-- The two maxima are equal only if their labels are. -/
@[simp]
theorem circleCosTwoMax_inj (r : ℝ) {i j : Fin 2} :
    circleCosTwoMax r i = circleCosTwoMax r j ↔ i = j :=
  (circleCosTwoMax_injective r).eq_iff

/-- The two minima are equal only if their labels are. -/
@[simp]
theorem circleCosTwoMin_inj (r : ℝ) {i j : Fin 2} :
    circleCosTwoMin r i = circleCosTwoMin r j ↔ i = j :=
  (circleCosTwoMin_injective r).eq_iff

/-- Every class `r + j π` with `j ∈ ℤ` is one of the two maxima. -/
theorem exists_circleCosTwoMax_eq (r : ℝ) (m : ℤ) :
    ∃ j : Fin 2, circleCosTwoMax r j = ((r + m * π : ℝ) : AddCircle (2 * π)) := by
  have hm : (m : ℝ) = 2 * ((m / 2 : ℤ) : ℝ) + ((m % 2 : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod m 2).symm
  rcases Int.emod_two_eq_zero_or_one m with h | h <;> rw [h] at hm <;>
    [refine ⟨0, coe_eq_coe_iff_exists_zsmul.2 ⟨-(m / 2), ?_⟩⟩;
      refine ⟨1, coe_eq_coe_iff_exists_zsmul.2 ⟨-(m / 2), ?_⟩⟩] <;>
    · rw [zsmul_eq_mul, hm]
      push_cast [Fin.val_zero, Fin.val_one]
      ring

/-- Every class `r + π / 2 + j π` with `j ∈ ℤ` is one of the two minima. -/
theorem exists_circleCosTwoMin_eq (r : ℝ) (m : ℤ) :
    ∃ j : Fin 2, circleCosTwoMin r j = ((r + π / 2 + m * π : ℝ) : AddCircle (2 * π)) := by
  obtain ⟨j, hj⟩ := exists_circleCosTwoMax_eq (r + π / 2) m
  exact ⟨j, by rw [circleCosTwoMin_def, ← hj, circleCosTwoMax_def]⟩

/-- Rotating the function by `π` does not change it, since `cos` has period `2 π`. -/
theorem circleCosTwo_add_pi (δ r : ℝ) : circleCosTwo δ (r + π) = circleCosTwo δ r := by
  funext θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [circleCosTwo_coe, circleCosTwo_coe,
    show 2 * (t - (r + π)) = 2 * (t - r) - 2 * π by ring, Real.cos_sub_two_pi]

/-- Rotating the function by `c` moves its maxima by `c`, keeping their labels. -/
theorem circleCosTwoMax_add_coe (r c : ℝ) (j : Fin 2) :
    circleCosTwoMax r j + (c : AddCircle (2 * π)) = circleCosTwoMax (r + c) j := by
  rw [circleCosTwoMax_def, circleCosTwoMax_def, ← coe_add, add_right_comm]

/-- Rotating the function by `-c` moves its maxima by `-c`, keeping their labels. -/
theorem circleCosTwoMax_sub_coe (r c : ℝ) (j : Fin 2) :
    circleCosTwoMax r j - (c : AddCircle (2 * π)) = circleCosTwoMax (r - c) j := by
  rw [sub_eq_add_neg, ← coe_neg, circleCosTwoMax_add_coe, sub_eq_add_neg]

/-- Rotating the function by `c` moves its minima by `c`, keeping their labels. -/
theorem circleCosTwoMin_add_coe (r c : ℝ) (j : Fin 2) :
    circleCosTwoMin r j + (c : AddCircle (2 * π)) = circleCosTwoMin (r + c) j := by
  rw [circleCosTwoMin_def, circleCosTwoMin_def, ← coe_add]
  congr 1
  ring

/-- Rotating the function by `π` exchanges the labels of its maxima: the maximum `r + π + j π` is
`r + (j + 1) π`. -/
@[simp]
theorem circleCosTwoMax_add_pi (r : ℝ) (j : Fin 2) :
    circleCosTwoMax (r + π) j = circleCosTwoMax r (j + 1) := by
  rw [circleCosTwoMax_def, circleCosTwoMax_def]
  fin_cases j
  · norm_num
  · exact coe_eq_coe_iff_exists_zsmul.2 ⟨1, by push_cast [Fin.val_zero, Fin.val_one]; ring⟩

/-- Rotating the function by `π` exchanges the labels of its minima: the minimum
`r + π + π / 2 + j π` is `r + π / 2 + (j + 1) π`. -/
@[simp]
theorem circleCosTwoMin_add_pi (r : ℝ) (j : Fin 2) :
    circleCosTwoMin (r + π) j = circleCosTwoMin r (j + 1) := by
  rw [circleCosTwoMin_def, circleCosTwoMin_def, add_right_comm r π,
    ← circleCosTwoMax_def, ← circleCosTwoMax_def, circleCosTwoMax_add_pi]

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

/-- **The differential of `θ ↦ δ cos (2 (θ - r))`.** At the class of `t`, the tangent line of the
circle being read as `ℝ` through the local real lifts, it is multiplication by
`-2 δ sin (2 (t - r))`. -/
theorem mvfderiv_circleCosTwo_coe (δ r t : ℝ) :
    mvfderiv 𝓘(ℝ) (circleCosTwo δ r) (t : AddCircle (2 * π)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (-(2 * δ) * Real.sin (2 * (t - r))) :=
  AddCircle.mvfderiv_eq_smulRight_of_hasDerivAt <| by
    simpa only [Function.comp_def, circleCosTwo_coe] using hasDerivAt_cos_two δ r t

/-- At a point `x` of the circle with lift `y`, the angle `2 (y - r)` has the sine and cosine of the
class of `2 (θ - r)`; these do not depend on the lift. -/
private theorem sin_two_eq_of_coe_eq {x : AddCircle (2 * π)} {y : ℝ}
    (hy : (y : AddCircle (2 * π)) = x) (r : ℝ) :
    Real.sin (2 * (y - r)) = (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).im := by
  rw [← hy, toCircle_two_nsmul_coe_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

private theorem cos_two_eq_of_coe_eq {x : AddCircle (2 * π)} {y : ℝ}
    (hy : (y : AddCircle (2 * π)) = x) (r : ℝ) :
    Real.cos (2 * (y - r)) = (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).re := by
  rw [← hy, toCircle_two_nsmul_coe_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- A point is critical for `θ ↦ δ cos (2 (θ - r))` exactly when `δ sin (2 (θ - r))` vanishes
there. -/
private theorem mem_criticalPoints_circleCosTwo_iff_mul (δ r : ℝ) {x : AddCircle (2 * π)} :
    x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) ↔
      δ * (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).im = 0 := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x).fderiv_eq,
    (hasDerivAt_cos_two δ r _).hasFDerivAt.fderiv,
    ← sin_two_eq_of_coe_eq (coe_extChartAt_self x) r]
  have h0 (v : ℝ) : ContinuousLinearMap.toSpanSingleton ℝ v = 0 ↔ v = 0 :=
    ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩
  rw [h0]
  exact ⟨fun h ↦ by linear_combination (-1 / 2 : ℝ) * h, fun h ↦ by linear_combination -2 * h⟩

/-- **The critical points** of `θ ↦ δ cos (2 (θ - r))`, for `δ ≠ 0`, are the angles with
`sin (2 (θ - r)) = 0`. -/
theorem mem_criticalPoints_circleCosTwo_iff {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ) {x : AddCircle (2 * π)} :
    x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) ↔
      (toCircle (2 • (x - (r : AddCircle (2 * π)))) : ℂ).im = 0 := by
  rw [mem_criticalPoints_circleCosTwo_iff_mul, mul_eq_zero, or_iff_right hδ]

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

/-- The Morse index of `θ ↦ δ cos (2 (θ - r))` at `x` is the Morse index of
`y ↦ δ cos (2 (y - r))` at the chart coordinate of `x`. -/
private theorem manifoldMorseIndex_circleCosTwo_of_lift (δ r : ℝ) (x : AddCircle (2 * π)) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) x =
      morseIndex (fun y ↦ δ * Real.cos (2 * (y - r))) (extChartAt 𝓘(ℝ) x x) := by
  rw [manifoldMorseIndex_def,
    morseIndex_congr_of_eventuallyEq (circleCosTwo_comp_extChartAt_symm_eventuallyEq δ r x)]

/-- The maxima `r + j π` are critical points. -/
theorem circleCosTwoMax_mem_criticalPoints (δ r : ℝ) (j : Fin 2) :
    circleCosTwoMax r j ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) := by
  rw [mem_criticalPoints_circleCosTwo_iff_mul, toCircle_two_nsmul_circleCosTwoMax_sub,
    Complex.one_im, mul_zero]

/-- The minima `r + π / 2 + j π` are critical points. -/
theorem circleCosTwoMin_mem_criticalPoints (δ r : ℝ) (j : Fin 2) :
    circleCosTwoMin r j ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) := by
  rw [mem_criticalPoints_circleCosTwo_iff_mul, toCircle_two_nsmul_circleCosTwoMin_sub,
    Complex.neg_im, Complex.one_im, neg_zero, mul_zero]

/-- The maximum `r + j π` as a critical point of `θ ↦ δ cos (2 (θ - r))`. -/
noncomputable def circleCosTwoMaxCrit (δ r : ℝ) (j : Fin 2) :
    criticalPoints 𝓘(ℝ) (circleCosTwo δ r) :=
  ⟨circleCosTwoMax r j, circleCosTwoMax_mem_criticalPoints δ r j⟩

/-- The minimum `r + π / 2 + j π` as a critical point of `θ ↦ δ cos (2 (θ - r))`. -/
noncomputable def circleCosTwoMinCrit (δ r : ℝ) (j : Fin 2) :
    criticalPoints 𝓘(ℝ) (circleCosTwo δ r) :=
  ⟨circleCosTwoMin r j, circleCosTwoMin_mem_criticalPoints δ r j⟩

/-- The critical point `circleCosTwoMaxCrit δ r j` is the angle `circleCosTwoMax r j`. -/
@[simp]
theorem coe_circleCosTwoMaxCrit (δ r : ℝ) (j : Fin 2) :
    (circleCosTwoMaxCrit δ r j : AddCircle (2 * π)) = circleCosTwoMax r j := by
  rw [circleCosTwoMaxCrit]

/-- The critical point `circleCosTwoMinCrit δ r j` is the angle `circleCosTwoMin r j`. -/
@[simp]
theorem coe_circleCosTwoMinCrit (δ r : ℝ) (j : Fin 2) :
    (circleCosTwoMinCrit δ r j : AddCircle (2 * π)) = circleCosTwoMin r j := by
  rw [circleCosTwoMinCrit]

/-- The two maxima are equal as critical points only if their labels are. -/
@[simp]
theorem circleCosTwoMaxCrit_inj (δ r : ℝ) {i j : Fin 2} :
    circleCosTwoMaxCrit δ r i = circleCosTwoMaxCrit δ r j ↔ i = j := by
  rw [Subtype.ext_iff, coe_circleCosTwoMaxCrit, coe_circleCosTwoMaxCrit, circleCosTwoMax_inj]

/-- The two minima are equal as critical points only if their labels are. -/
@[simp]
theorem circleCosTwoMinCrit_inj (δ r : ℝ) {i j : Fin 2} :
    circleCosTwoMinCrit δ r i = circleCosTwoMinCrit δ r j ↔ i = j := by
  rw [Subtype.ext_iff, coe_circleCosTwoMinCrit, coe_circleCosTwoMinCrit, circleCosTwoMin_inj]

/-- A maximum is never a minimum as a critical point. -/
@[simp]
theorem circleCosTwoMaxCrit_ne_circleCosTwoMinCrit (δ r : ℝ) (i j : Fin 2) :
    circleCosTwoMaxCrit δ r i ≠ circleCosTwoMinCrit δ r j := by
  rw [Ne, Subtype.ext_iff, coe_circleCosTwoMaxCrit, coe_circleCosTwoMinCrit]
  exact circleCosTwoMax_ne_circleCosTwoMin r i j

/-- A minimum is never a maximum as a critical point. -/
@[simp]
theorem circleCosTwoMinCrit_ne_circleCosTwoMaxCrit (δ r : ℝ) (i j : Fin 2) :
    circleCosTwoMinCrit δ r i ≠ circleCosTwoMaxCrit δ r j :=
  (circleCosTwoMaxCrit_ne_circleCosTwoMinCrit δ r j i).symm

/-- **The labelled critical points.** For `δ ≠ 0`, the critical points of `θ ↦ δ cos (2 (θ - r))`
are the maxima `r + j π` and the minima `r + π / 2 + j π`: if `sin (2 (θ - r)) = 0`, then
`2 (θ - r)` is a multiple `k π`, and the residue of `k` modulo `4` gives the label. -/
theorem mem_criticalPoints_circleCosTwo_iff_exists {δ : ℝ} (hδ : δ ≠ 0) (r : ℝ)
    {x : AddCircle (2 * π)} :
    x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r) ↔
      ∃ j, x = circleCosTwoMax r j ∨ x = circleCosTwoMin r j := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · set y := extChartAt 𝓘(ℝ) x x
    have hy : (y : AddCircle (2 * π)) = x := coe_extChartAt_self x
    have hsin : Real.sin (2 * (y - r)) = 0 := by
      rw [sin_two_eq_of_coe_eq hy r]
      exact (mem_criticalPoints_circleCosTwo_iff hδ r).1 hx
    have hlift (a : ℝ) (n : ℤ) (h : y = a + n * (2 * π)) : x = (a : AddCircle (2 * π)) := by
      rw [← hy, h, coe_add_int_mul_period]
    -- Write `2 (y - r) = k π` with `k = 4 n + l` and `l ∈ {0, 1, 2, 3}`.
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k <;> obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' m <;>
      push_cast at hk
    · refine ⟨0, Or.inl (hlift _ n ?_)⟩
      simp only [Fin.val_zero, Nat.cast_zero]
      linear_combination -hk / 2
    · refine ⟨1, Or.inl (hlift _ n ?_)⟩
      simp only [Fin.val_one, Nat.cast_one]
      linear_combination -hk / 2
    · refine ⟨0, Or.inr (hlift _ n ?_)⟩
      simp only [Fin.val_zero, Nat.cast_zero]
      linear_combination -hk / 2
    · refine ⟨1, Or.inr (hlift _ n ?_)⟩
      simp only [Fin.val_one, Nat.cast_one]
      linear_combination -hk / 2
  · rintro ⟨j, rfl | rfl⟩
    · exact circleCosTwoMax_mem_criticalPoints δ r j
    · exact circleCosTwoMin_mem_criticalPoints δ r j

/-- **The maxima have Morse index `1`.** -/
theorem manifoldMorseIndex_circleCosTwoMax {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMax r j) = 1 := by
  rw [manifoldMorseIndex_circleCosTwo_of_lift]
  refine morseIndex_real_of_neg ?_
  rw [iteratedDeriv_two_cos_two, cos_two_eq_of_coe_eq (coe_extChartAt_self _) r,
    toCircle_two_nsmul_circleCosTwoMax_sub, Complex.one_re, mul_one]
  linarith

/-- **The minima have Morse index `0`.** -/
theorem manifoldMorseIndex_circleCosTwoMin {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMin r j) = 0 := by
  rw [manifoldMorseIndex_circleCosTwo_of_lift]
  refine morseIndex_real_of_pos ?_
  rw [iteratedDeriv_two_cos_two, cos_two_eq_of_coe_eq (coe_extChartAt_self _) r,
    toCircle_two_nsmul_circleCosTwoMin_sub, Complex.neg_re, Complex.one_re]
  linarith

/-- **The maxima have Morse index `1`**, as critical points. -/
theorem manifoldMorseIndex_circleCosTwoMaxCrit {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMaxCrit δ r j) = 1 := by
  rw [coe_circleCosTwoMaxCrit, manifoldMorseIndex_circleCosTwoMax hδ]

/-- **The minima have Morse index `0`**, as critical points. -/
theorem manifoldMorseIndex_circleCosTwoMinCrit {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (j : Fin 2) :
    manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMinCrit δ r j) = 0 := by
  rw [coe_circleCosTwoMinCrit, manifoldMorseIndex_circleCosTwoMin hδ]

/-- **The critical points of index `1` are the two maxima**, for `δ > 0`: the minima have
index `0`. -/
theorem exists_eq_circleCosTwoMax_of_manifoldMorseIndex_eq_one {δ : ℝ} (hδ : 0 < δ) (r : ℝ)
    {x : AddCircle (2 * π)} (hx : x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r))
    (hind : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) x = 1) :
    ∃ j, x = circleCosTwoMax r j := by
  obtain ⟨j, rfl | rfl⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r).1 hx
  · exact ⟨j, rfl⟩
  · rw [manifoldMorseIndex_circleCosTwoMin hδ] at hind
    exact absurd hind zero_ne_one

/-- **The critical points of index `0` are the two minima**, for `δ > 0`: the maxima have
index `1`. -/
theorem exists_eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero {δ : ℝ} (hδ : 0 < δ) (r : ℝ)
    {x : AddCircle (2 * π)} (hx : x ∈ criticalPoints 𝓘(ℝ) (circleCosTwo δ r))
    (hind : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) x = 0) :
    ∃ j, x = circleCosTwoMin r j := by
  obtain ⟨j, rfl | rfl⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r).1 hx
  · rw [manifoldMorseIndex_circleCosTwoMax hδ] at hind
    exact absurd hind one_ne_zero
  · exact ⟨j, rfl⟩

end TauCeti
