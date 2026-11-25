/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Normed.Operator.Mul

/-!
# Checks for the descent lemma

The descent lemma `TauCeti.le_add_fderiv_add_of_lipschitz` bounds `f (x + h)` by
`f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2`. These checks pin down its constant and its hypothesis.

* For `f y = y ^ 2 / 2` on `ℝ` the hypothesis holds with `L = 1` and the bound is an equality, so
  the factor `1 / 2` cannot be lowered.
* For an affine function the hypothesis holds with `L = 0` and the bound is an equality.
* For `L < 0` the hypothesis forces `h = 0`, where the bound is an equality for every `L`.
-/

public section

open TauCeti

/-- The function `y ↦ y ^ 2 / 2` on `ℝ` satisfies the hypothesis of the descent lemma with
`L = 1`, at every point and not only on a segment. -/
example (x y : ℝ) :
    ‖fderiv ℝ (fun y : ℝ ↦ y ^ 2 / 2) y - fderiv ℝ (fun y : ℝ ↦ y ^ 2 / 2) x‖ ≤ 1 * ‖y - x‖ := by
  have hd (y : ℝ) : deriv (fun y : ℝ ↦ y ^ 2 / 2) y = y := by simp
  rw [← toSpanSingleton_deriv, ← toSpanSingleton_deriv]
  simp [ContinuousLinearMap.norm_toSpanSingleton_sub, hd]

/-- For `y ↦ y ^ 2 / 2` on `ℝ` and `L = 1` the descent lemma is an equality. -/
example (x h : ℝ) :
    (x + h) ^ 2 / 2 = x ^ 2 / 2 + fderiv ℝ (fun y : ℝ ↦ y ^ 2 / 2) x h + 1 / 2 * ‖h‖ ^ 2 := by
  have hd : deriv (fun y : ℝ ↦ y ^ 2 / 2) x = x := by simp
  simp only [fderiv_eq_smul_deriv, hd, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  ring

section Affine

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (ℓ : V →L[ℝ] ℝ)

/-- An affine function satisfies the hypothesis of the descent lemma with `L = 0`. -/
example (x y : V) :
    ‖fderiv ℝ (fun y ↦ c + ℓ y) y - fderiv ℝ (fun y ↦ c + ℓ y) x‖ ≤ 0 * ‖y - x‖ := by
  simp [fderiv_const_add]

/-- For an affine function and `L = 0` the descent lemma is an equality. -/
example (x h : V) :
    c + ℓ (x + h) = c + ℓ x + fderiv ℝ (fun y ↦ c + ℓ y) x h + 0 / 2 * ‖h‖ ^ 2 := by
  simp [fderiv_const_add, add_assoc]

end Affine

section Negative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {x h : V} {L : ℝ}

/-- With `L < 0` the hypothesis of the descent lemma forces `h = 0`. -/
example (hL : ∀ y ∈ segment ℝ x (x + h), ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖)
    (hneg : L < 0) : h = 0 := by
  have hh := hL (x + h) (right_mem_segment ℝ x (x + h))
  rw [add_sub_cancel_left] at hh
  by_contra hne
  nlinarith [norm_nonneg (fderiv ℝ f (x + h) - fderiv ℝ f x), norm_pos_iff.2 hne]

/-- At `h = 0` the descent lemma is an equality, for every `L`. -/
example : f (x + 0) = f x + fderiv ℝ f x 0 + L / 2 * ‖(0 : V)‖ ^ 2 := by
  simp

end Negative
