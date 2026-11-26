/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.RungeKutta.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Checks for Butcher tableaux and their stage equations

These examples test the conventions of `TauCeti.ButcherTableau`: the orientation of the matrix
`A`, the stage times `t + c i * h`, and the junk value `0` of `TauCeti.ButcherTableau.stages`
when the stage equations have no solution or several.

* A tableau with no stages is explicit, its stage vector is empty and its increment is `0`.
* The one-stage tableau `A = (0)`, `b = (1)`, `c = (0)` has increment `f t y`.
* The two-stage tableau `A = (0, 0; 1, 0)`, `b = (1/2, 1/2)`, `c = (0, 1)` has stages `f t y` and
  `f (t + h) (y + h • f t y)`; the transpose of its matrix is not strictly lower triangular.
* The one-stage tableau `A = (1)`, `b = (1)`, `c = (1)` on `f t u = λ u` over `ℝ` has the stage
  `λ y / (1 - h λ)` when `h λ ≠ 1`. When `h λ = 1` the stage equation has no solution for
  `y ≠ 0` and every number is a solution for `y = 0`, so the stage vector is `0` in both cases.
* A tableau with `A 0 0 = 1/2` is not explicit.
-/

public section

namespace TauCeti.Examples.ButcherTableau

open TauCeti TauCeti.ButcherTableau
open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### No stages -/

/-- Every tableau with no stages is explicit. -/
theorem isExplicit_of_zero (T : ButcherTableau 0) : T.IsExplicit :=
  isExplicit_iff.mpr fun i ↦ i.elim0

/-- With no stages the increment function is `0`, so the numerical solution is constant. -/
theorem increment_of_zero (T : ButcherTableau 0) (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) :
    T.increment f t y h = 0 := by
  simp [increment_def]

/-! ### One explicit stage -/

/-- The tableau `A = (0)`, `b = (1)`, `c = (0)`. -/
noncomputable def euler : ButcherTableau 1 := ⟨!![0], ![1], ![0]⟩

theorem euler_isExplicit : euler.IsExplicit :=
  isExplicit_iff.mpr fun i j _ ↦ by fin_cases i; fin_cases j; simp [euler]

/-- The stage of `euler` is `f t y`: the stage time is `t + 0 * h = t`. -/
theorem euler_stages (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) :
    euler.stages f t y h = ![f t y] := by
  ext i
  fin_cases i
  rw [stages_apply_of_isExplicit euler_isExplicit]
  simp [euler]

/-- The increment of `euler` is `f t y`. -/
theorem euler_increment (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) :
    euler.increment f t y h = f t y := by
  rw [increment_def, euler_stages]
  simp [euler]

/-! ### Two explicit stages -/

/-- The tableau `A = (0, 0; 1, 0)`, `b = (1/2, 1/2)`, `c = (0, 1)`. -/
noncomputable def twoStage : ButcherTableau 2 := ⟨!![0, 0; 1, 0], ![1 / 2, 1 / 2], ![0, 1]⟩

theorem twoStage_isExplicit : twoStage.IsExplicit :=
  isExplicit_iff.mpr fun i j hij ↦ by
    fin_cases i <;> fin_cases j <;> simp_all [twoStage]

/-- The stages of `twoStage`: `k 0 = f t y` and `k 1 = f (t + h) (y + h • k 0)`. -/
theorem twoStage_stages (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) :
    twoStage.stages f t y h = ![f t y, f (t + h) (y + h • f t y)] := by
  have h0 : twoStage.stages f t y h 0 = f t y := by
    have : Finset.Iio (0 : Fin 2) = ∅ := by decide
    rw [stages_apply_of_isExplicit twoStage_isExplicit, this]
    simp [twoStage]
  have h1 : twoStage.stages f t y h 1 = f (t + h) (y + h • f t y) := by
    have : Finset.Iio (1 : Fin 2) = {0} := by decide
    rw [stages_apply_of_isExplicit twoStage_isExplicit, this, Finset.sum_singleton, h0]
    simp [twoStage]
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- The increment of `twoStage` is `(1/2) • (f t y + f (t + h) (y + h • f t y))`. -/
theorem twoStage_increment (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) :
    twoStage.increment f t y h = (1 / 2 : ℝ) • (f t y + f (t + h) (y + h • f t y)) := by
  rw [increment_def, twoStage_stages]
  simp [twoStage, smul_add]

/-- Reading the matrix of `twoStage` as its transpose gives a tableau that is not explicit. -/
theorem not_isExplicit_transpose :
    ¬(⟨twoStage.Aᵀ, twoStage.b, twoStage.c⟩ : ButcherTableau 2).IsExplicit := fun h ↦ by
  have := isExplicit_iff.mp h 0 1 (by decide)
  norm_num [twoStage] at this

/-! ### One implicit stage on a linear field -/

/-- The tableau `A = (1)`, `b = (1)`, `c = (1)`. -/
noncomputable def implicitOne : ButcherTableau 1 := ⟨!![1], ![1], ![1]⟩

/-- On `f t u = λ u`, the stage equation of `implicitOne` reads `k = λ (y + h k)`. -/
theorem implicitOne_isStage_iff (lam t y h : ℝ) (k : Fin 1 → ℝ) :
    implicitOne.IsStage (fun _ u ↦ lam * u) t y h k ↔ k 0 = lam * (y + h * k 0) := by
  simp [isStage_iff, implicitOne, Fin.forall_fin_one]

/-- For `h λ ≠ 1` the stage of `implicitOne` on `f t u = λ u` is `λ y / (1 - h λ)`. -/
theorem implicitOne_stages (lam t y h : ℝ) (hhl : h * lam ≠ 1) :
    implicitOne.stages (fun _ u ↦ lam * u) t y h = ![lam * y / (1 - h * lam)] := by
  have hne : 1 - h * lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hhl)
  refine stages_eq_of_isStage ((implicitOne_isStage_iff ..).mpr ?_) fun k hk ↦ ?_
  · have hu : (1 - h * lam) * (1 - h * lam)⁻¹ = 1 := mul_inv_cancel₀ hne
    simp only [Matrix.cons_val_fin_one, div_eq_mul_inv]
    linear_combination (lam * y) * hu
  · ext i
    fin_cases i
    have hk := (implicitOne_isStage_iff ..).mp hk
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
    rw [eq_div_iff hne]
    linear_combination hk

/-- For `h λ = 1` and `y ≠ 0` the stage equation of `implicitOne` on `f t u = λ u` has no
solution. -/
theorem implicitOne_not_isStage (lam t y h : ℝ) (hhl : h * lam = 1) (hy : y ≠ 0)
    (k : Fin 1 → ℝ) : ¬implicitOne.IsStage (fun _ u ↦ lam * u) t y h k := fun hk ↦ by
  have hk := (implicitOne_isStage_iff ..).mp hk
  have hlam : lam ≠ 0 := by rintro rfl; simp at hhl
  exact mul_ne_zero hlam hy (by linear_combination -hk - k 0 * hhl)

/-- For `h λ = 1` and `y = 0` every vector solves the stage equation of `implicitOne` on
`f t u = λ u`. -/
theorem implicitOne_isStage_of_zero (lam t h : ℝ) (hhl : h * lam = 1) (k : Fin 1 → ℝ) :
    implicitOne.IsStage (fun _ u ↦ lam * u) t 0 h k :=
  (implicitOne_isStage_iff ..).mpr (by linear_combination -(k 0) * hhl)

/-- For `h λ = 1` the stage vector of `implicitOne` on `f t u = λ u` is the junk value `0`,
whether there is no stage vector (`y ≠ 0`) or every vector is one (`y = 0`). -/
theorem implicitOne_stages_of_mul_eq_one (lam t y h : ℝ) (hhl : h * lam = 1) :
    implicitOne.stages (fun _ u ↦ lam * u) t y h = 0 := by
  refine stages_of_not_existsUnique fun ⟨k, hk, huniq⟩ ↦ ?_
  by_cases hy : y = 0
  · subst hy
    have h0 := huniq 0 (implicitOne_isStage_of_zero lam t h hhl 0)
    have h1 := huniq 1 (implicitOne_isStage_of_zero lam t h hhl 1)
    have := congrFun (h0.trans h1.symm) 0
    simp at this
  · exact implicitOne_not_isStage lam t y h hhl hy k hk

/-! ### A diagonal entry -/

/-- A tableau with `A 0 0 = 1/2` is not explicit. -/
theorem not_isExplicit_of_A_self {s : ℕ} (T : ButcherTableau (s + 1)) (hA : T.A 0 0 = 1 / 2) :
    ¬T.IsExplicit := fun h ↦ by
  have := isExplicit_iff.mp h 0 0 le_rfl
  norm_num [hA] at this

end TauCeti.Examples.ButcherTableau
