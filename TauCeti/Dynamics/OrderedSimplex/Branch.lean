/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Dynamics.OrderedSimplex.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unaccelerated and accelerated projective branches on the ordered simplex

For `n = d + 2`, each index `j : Fin (d + 1)` defines a linear map `γ_j`
(`TauCeti.OrderedSimplex.unaccelMove j`) on `ℝ^{d+2}` sending `y` to
`(y₁, …, ŷ_j, …, y_n, ∑_{k ≠ j} y_k)`. It maps the hyperplane `coneSpan d` and the ordered cone
`orderedCone d` into themselves; on `coneSpan d`, the last coordinate of `γ_j y` equals
`2 y_n - y_j`.

For a letter `a = (A, j) : ℕ × Fin d`, the **accelerated linear move** is
`γ_{n-1}^A γ_j` (`TauCeti.OrderedSimplex.accelMove a`). On the projective chart `orderedSimplex d`,
it acts by the rational branch `branchMap a` with denominator
`branchDenom a x = 1 + (A + 1) (1 - x_j)` and logarithmic delay
`branchDelay a x = log (branchDenom a x)`.
On `orderedSimplex d`, we establish the homogeneous intertwining identity, the two-sided bounds
`(A + 3) / 2 ≤ q_a ≤ A + 2` and `τ_a ≥ log (3 / 2)`, the uniform logarithmic derivative bound
`‖d (log q_a)‖ ≤ 2 (A + 1) / (A + 3) < 2`, smoothness of `branchMap a` on the open neighbourhood
`{x | 0 < branchDenom a x}` of `orderedSimplex d`, invariance of `orderedSimplex d`, and the
modulus and real-positivity laws for the complex weight `q_a^{-s}`.

## Main definitions

* `TauCeti.OrderedSimplex.unaccelMove`: the linear move `γ_j` on `Fin (d + 2) → ℝ`.
* `TauCeti.OrderedSimplex.accelMove`: the accelerated linear move `γ_{n-1}^A γ_j`.
* `TauCeti.OrderedSimplex.branchDenom`: the denominator `q_a(w) = 1 + (A + 1) (1 - w_j)`.
* `TauCeti.OrderedSimplex.branchMap`: the accelerated projective branch `F_a` in chart coordinates.
* `TauCeti.OrderedSimplex.branchDelay`: the branch delay `τ_a = log q_a`.

## References

* A. Gamburd, M. Magee and R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. (2) 190 (2019), no. 3, 751–809, Lemma 33, (4.5)–(4.6).
-/

public section

noncomputable section

open Finset Set
open scoped ContDiff

namespace TauCeti.OrderedSimplex

/-! ### Unaccelerated linear moves -/

/-- The unaccelerated linear move `γ_j(y) = (y₁, …, ŷ_j, …, y_n, ∑_{k ≠ j} y_k)` on
`Fin (d + 2) → ℝ` for `j : Fin (d + 1)`. -/
def unaccelMove {d : ℕ} (j : Fin (d + 1)) :
    (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ) where
  toFun y :=
    Fin.snoc (α := fun _ => ℝ) (fun i : Fin (d + 1) => y (j.castSucc.succAbove i))
      (∑ i : Fin (d + 1), y (j.castSucc.succAbove i))
  map_add' y z := by
    ext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp [Finset.sum_add_distrib]
    · simp
  map_smul' c y := by
    ext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp [Finset.mul_sum]
    · simp

@[simp]
theorem unaccelMove_castSucc {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ)
    (i : Fin (d + 1)) :
    unaccelMove j y i.castSucc = y (j.castSucc.succAbove i) := by
  simp [unaccelMove]

@[simp]
theorem unaccelMove_last {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    unaccelMove j y (Fin.last (d + 1)) = ∑ i : Fin (d + 1), y (j.castSucc.succAbove i) := by
  simp [unaccelMove]

/-- Every image of `unaccelMove j` lies in the hyperplane `coneSpan d`. -/
theorem unaccelMove_mem_coneSpan {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    unaccelMove j y ∈ coneSpan d := by
  simp

/-- The penultimate coordinate of `γ_j y` is always the last coordinate `y_n`. -/
theorem unaccelMove_penultimate {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    unaccelMove j y (Fin.last d).castSucc = y (Fin.last (d + 1)) := by
  rw [unaccelMove_castSucc]
  congr 1
  exact Fin.succAbove_of_le_castSucc j.castSucc (Fin.last d)
    (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last j))

/-- On `coneSpan d`, the last coordinate of `γ_j y` equals `2 y_n - y_j`. -/
theorem unaccelMove_last_of_mem_coneSpan {d : ℕ} (j : Fin (d + 1)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ coneSpan d) :
    unaccelMove j y (Fin.last (d + 1)) = 2 * y (Fin.last (d + 1)) - y j.castSucc := by
  rw [unaccelMove_last]
  have hsum : ∑ k : Fin (d + 2), y k =
      y j.castSucc + ∑ i : Fin (d + 1), y (j.castSucc.succAbove i) :=
    Fin.sum_univ_succAbove y j.castSucc
  have hsum2 : ∑ k : Fin (d + 2), y k = 2 * y (Fin.last (d + 1)) := by
    rw [Fin.sum_univ_castSucc, mem_coneSpan_iff.1 hy]
    ring
  linarith

/-- The last unaccelerated move `γ_{n-1}` leaves the first `d` coordinates unchanged. -/
theorem unaccelMove_last_index_castSucc {d : ℕ} (y : Fin (d + 2) → ℝ) (i : Fin d) :
    unaccelMove (Fin.last d) y i.castSucc.castSucc = y i.castSucc.castSucc := by
  rw [unaccelMove_castSucc]
  congr 1
  exact Fin.succAbove_of_castSucc_lt (Fin.last d).castSucc i.castSucc
    (Fin.castSucc_lt_castSucc_iff.2 (Fin.castSucc_lt_last i))

/-- Each unaccelerated move maps `orderedCone d` into itself. -/
theorem unaccelMove_mapsTo_orderedCone {d : ℕ} (j : Fin (d + 1)) :
    MapsTo (unaccelMove j) (orderedCone d) (orderedCone d) := by
  intro y hy
  have hpos := last_pos_of_mem_orderedCone hy
  rw [mem_orderedCone_iff] at hy ⊢
  refine ⟨?_, ?_, ?_, mem_coneSpan_iff.1 (unaccelMove_mem_coneSpan j y)⟩
  · intro h0
    have hpen := congrFun h0 (Fin.last d).castSucc
    rw [unaccelMove_penultimate, Pi.zero_apply] at hpen
    linarith
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · rw [unaccelMove_last]
      exact Finset.sum_nonneg fun i _ => hy.2.1 _
    · rw [unaccelMove_castSucc]
      exact hy.2.1 _
  · intro k₁ k₂
    refine Fin.lastCases ?_ (fun i₂ => ?_) k₂
    · refine Fin.lastCases (fun _ => le_refl _) (fun i₁ _ => ?_) k₁
      rw [unaccelMove_castSucc, unaccelMove_last]
      exact Finset.single_le_sum (fun m _ => hy.2.1 _) (Finset.mem_univ i₁)
    · refine Fin.lastCases (fun h => ?_) (fun i₁ h => ?_) k₁
      · exact absurd h (not_le.2 (Fin.castSucc_lt_last i₂))
      · rw [unaccelMove_castSucc, unaccelMove_castSucc]
        exact hy.2.2.1 ((Fin.strictMono_succAbove _).monotone (Fin.castSucc_le_castSucc_iff.1 h))

/-! ### Accelerated linear moves -/

/-- The accelerated linear move `γ_{n-1}^A γ_j` for a letter `a = (A, j) : ℕ × Fin d`. -/
def accelMove {d : ℕ} (a : ℕ × Fin d) :
    (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ) :=
  (unaccelMove (Fin.last d) ^ a.1).comp (unaccelMove a.2.castSucc)

theorem accelMove_def {d : ℕ} (a : ℕ × Fin d) :
    accelMove a = (unaccelMove (Fin.last d) ^ a.1).comp (unaccelMove a.2.castSucc) :=
  (rfl)

@[simp]
theorem accelMove_zero {d : ℕ} (j : Fin d) :
    accelMove (0, j) = unaccelMove j.castSucc := by
  simp [accelMove, Module.End.one_eq_id]

theorem accelMove_succ {d : ℕ} (A : ℕ) (j : Fin d) :
    accelMove (A + 1, j) = (unaccelMove (Fin.last d)).comp (accelMove (A, j)) := by
  ext y k
  simp [accelMove, pow_succ']

/-- Every image of `accelMove a` lies in `coneSpan d`. -/
theorem accelMove_mem_coneSpan {d : ℕ} (a : ℕ × Fin d) (y : Fin (d + 2) → ℝ) :
    accelMove a y ∈ coneSpan d := by
  rcases a with ⟨A, j⟩
  induction A with
  | zero =>
    rw [accelMove_zero]
    exact unaccelMove_mem_coneSpan j.castSucc y
  | succ A _ =>
    rw [accelMove_succ]
    exact unaccelMove_mem_coneSpan (Fin.last d) _

/-- The first `d` coordinates of `γ_{n-1}^A γ_j y` delete `y_j` from `(y₁, …, y_{n-1})`. -/
theorem accelMove_castSucc_castSucc {d : ℕ} (a : ℕ × Fin d) (y : Fin (d + 2) → ℝ) (i : Fin d) :
    accelMove a y i.castSucc.castSucc = y ((a.2.castSucc.succAbove i).castSucc) := by
  rcases a with ⟨A, j⟩
  induction A with
  | zero =>
    rw [accelMove_zero, unaccelMove_castSucc]
    congr 1
    by_cases h : i.castSucc < j.castSucc
    · have h' : i.castSucc.castSucc < j.castSucc.castSucc := Fin.castSucc_lt_castSucc_iff.2 h
      rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.succAbove_of_castSucc_lt _ _ h]
    · have hge : j.castSucc ≤ i.castSucc := not_lt.1 h
      have hge' : j.castSucc.castSucc ≤ i.castSucc.castSucc :=
        Fin.castSucc_le_castSucc_iff.2 hge
      rw [Fin.succAbove_of_le_castSucc _ _ hge', Fin.succAbove_of_le_castSucc _ _ hge]
      rfl
  | succ A ih =>
    rw [accelMove_succ, LinearMap.comp_apply, unaccelMove_last_index_castSucc, ih]

/-- On `coneSpan d`, the penultimate and last coordinates of `γ_{n-1}^A γ_j y` are
`y_n + A (y_n - y_j)` and `y_n + (A + 1) (y_n - y_j)`. -/
theorem accelMove_penultimate_and_last {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ coneSpan d) :
    accelMove a y (Fin.last d).castSucc =
      y (Fin.last (d + 1)) + (a.1 : ℝ) * (y (Fin.last (d + 1)) - y a.2.castSucc.castSucc) ∧
    accelMove a y (Fin.last (d + 1)) =
      y (Fin.last (d + 1)) +
        ((a.1 : ℝ) + 1) * (y (Fin.last (d + 1)) - y a.2.castSucc.castSucc) := by
  rcases a with ⟨A, j⟩
  induction A with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · rw [accelMove_zero, unaccelMove_last_of_mem_coneSpan j.castSucc hy]
      simp only [Nat.cast_zero, zero_add, one_mul]
      ring
  | succ A ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨?_, ?_⟩
    · rw [accelMove_succ, LinearMap.comp_apply, unaccelMove_penultimate, ih2]
      push_cast
      ring
    · rw [accelMove_succ, LinearMap.comp_apply,
        unaccelMove_last_of_mem_coneSpan (Fin.last d) (accelMove_mem_coneSpan (A, j) y), ih1, ih2]
      push_cast
      ring

/-- On `coneSpan d`, the penultimate coordinate of `γ_{n-1}^A γ_j y` is
`y_n + A (y_n - y_j)`. -/
theorem accelMove_penultimate {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ} (hy : y ∈ coneSpan d) :
    accelMove a y (Fin.last d).castSucc =
      y (Fin.last (d + 1)) + (a.1 : ℝ) * (y (Fin.last (d + 1)) - y a.2.castSucc.castSucc) :=
  (accelMove_penultimate_and_last a hy).1

/-- On `coneSpan d`, the last coordinate of `γ_{n-1}^A γ_j y` is
`y_n + (A + 1) (y_n - y_j)`. -/
theorem accelMove_last {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ} (hy : y ∈ coneSpan d) :
    accelMove a y (Fin.last (d + 1)) =
      y (Fin.last (d + 1)) + ((a.1 : ℝ) + 1) * (y (Fin.last (d + 1)) - y a.2.castSucc.castSucc) :=
  (accelMove_penultimate_and_last a hy).2

/-- Each accelerated move maps `orderedCone d` into itself. -/
theorem accelMove_mapsTo_orderedCone {d : ℕ} (a : ℕ × Fin d) :
    MapsTo (accelMove a) (orderedCone d) (orderedCone d) := by
  rcases a with ⟨A, j⟩
  induction A with
  | zero =>
    intro y hy
    rw [accelMove_zero]
    exact unaccelMove_mapsTo_orderedCone j.castSucc hy
  | succ A ih =>
    intro y hy
    rw [accelMove_succ, LinearMap.comp_apply]
    exact unaccelMove_mapsTo_orderedCone (Fin.last d) (ih hy)

/-! ### Accelerated projective branches -/

/-- The denominator `q_a(w) = 1 + (A + 1)(1 - w_j)` of the accelerated branch `a = (A, j)`. -/
def branchDenom {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : ℝ :=
  1 + ((a.1 : ℝ) + 1) * (1 - x a.2)

theorem branchDenom_def {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchDenom a x = 1 + ((a.1 : ℝ) + 1) * (1 - x a.2) :=
  (rfl)

/-- The accelerated branch `F_a` in chart coordinates: delete `w_j` from `(w₁, …, w_{d+1})`
and divide by `q_a(w)`. -/
def branchMap {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (Fin.snoc (α := fun _ => ℝ) x (1 - ∑ k, x k) ((Fin.castSucc a.2).succAbove i)) /
    branchDenom a x

theorem branchMap_def {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) (i : Fin d) :
    branchMap a x i = toProjective x (a.2.castSucc.succAbove i) / branchDenom a x := by
  unfold branchMap
  congr 1
  refine Fin.lastCases ?_ (fun k => ?_) (a.2.castSucc.succAbove i) <;> simp

/-- The logarithmic delay `τ_a(w) = log (q_a(w))` of the accelerated branch `a`. -/
def branchDelay {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : ℝ :=
  Real.log (branchDenom a x)

theorem branchDelay_def {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchDelay a x = Real.log (branchDenom a x) :=
  (rfl)

/-- The remaining mass `1 - ∑ i, F_a(w)_i` equals `(1 + A (1 - w_j)) / q_a(w)` wherever
`q_a(w) ≠ 0`. -/
theorem one_sub_sum_branchMap {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    1 - ∑ i : Fin d, branchMap a x i = (1 + (a.1 : ℝ) * (1 - x a.2)) / branchDenom a x := by
  have hsum : ∑ i : Fin d, toProjective x (a.2.castSucc.succAbove i) = 1 - x a.2 := by
    have h1 := Fin.sum_univ_succAbove (toProjective x) a.2.castSucc
    rw [sum_toProjective, toProjective_castSucc] at h1
    linarith
  simp only [branchMap_def, ← Finset.sum_div]
  rw [hsum, eq_div_iff hq, sub_mul, one_mul, div_mul_cancel₀ _ hq, branchDenom_def]
  ring

/-- The homogeneous intertwining identity on the lifted chart point:
`γ_{n-1}^A γ_j (w, 1) = q_a(w) (F_a(w), 1)` whenever `q_a(w) ≠ 0`. -/
theorem accelMove_toHomogeneous {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    accelMove a (toHomogeneous x) = branchDenom a x • toHomogeneous (branchMap a x) := by
  have hspan : toHomogeneous x ∈ coneSpan d := by simp
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [accelMove_last a hspan, branchDenom_def]
  · refine Fin.lastCases ?_ (fun m => ?_) i
    · simp [accelMove_penultimate a hspan, one_sub_sum_branchMap a hq, mul_div_cancel₀ _ hq]
    · simp [accelMove_castSucc_castSucc, branchMap_def, mul_div_cancel₀ _ hq]

/-! ### Bounds and invariance on the ordered simplex -/

/-- Lower bound `(A + 3) / 2 ≤ q_a(w)` on `orderedSimplex d`. -/
theorem branchDenom_ge {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    ((a.1 : ℝ) + 3) / 2 ≤ branchDenom a x := by
  rw [branchDenom_def]
  have hhalf := coord_le_half_of_mem_orderedSimplex hx a.2
  have : (0 : ℝ) ≤ (a.1 : ℝ) + 1 := by positivity
  nlinarith

/-- Upper bound `q_a(w) ≤ A + 2` on `orderedSimplex d`. -/
theorem branchDenom_le {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    branchDenom a x ≤ (a.1 : ℝ) + 2 := by
  rw [branchDenom_def]
  have h0 := coord_nonneg_of_mem_orderedSimplex hx a.2
  have : (0 : ℝ) ≤ (a.1 : ℝ) + 1 := by positivity
  nlinarith

/-- Uniform lower bound `3 / 2 ≤ q_a(w)` on `orderedSimplex d`. -/
theorem three_div_two_le_branchDenom {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 3 / 2 ≤ branchDenom a x := by
  linarith [branchDenom_ge a hx, Nat.cast_nonneg (α := ℝ) a.1]

/-- The branch denominator is strictly positive on `orderedSimplex d`. -/
theorem branchDenom_pos {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    0 < branchDenom a x := by
  linarith [three_div_two_le_branchDenom a hx]

/-- Lower bound `log ((A + 3) / 2) ≤ τ_a(w)` on `orderedSimplex d`. -/
theorem log_le_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (((a.1 : ℝ) + 3) / 2) ≤ branchDelay a x :=
  Real.log_le_log (by positivity) (branchDenom_ge a hx)

/-- Uniform lower bound `log (3 / 2) ≤ τ_a(w)` on `orderedSimplex d`. -/
theorem log_three_div_two_le_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : Real.log (3 / 2) ≤ branchDelay a x :=
  Real.log_le_log (by norm_num) (three_div_two_le_branchDenom a hx)

/-- The branch delay is strictly positive on `orderedSimplex d`. -/
theorem branchDelay_pos {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    0 < branchDelay a x :=
  Real.log_pos (by linarith [three_div_two_le_branchDenom a hx])

/-- Upper bound `τ_a(w) ≤ log (A + 2)` on `orderedSimplex d`. -/
theorem branchDelay_le {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    branchDelay a x ≤ Real.log ((a.1 : ℝ) + 2) :=
  Real.log_le_log (branchDenom_pos a hx) (branchDenom_le a hx)

/-- Homogeneous identity on `orderedCone d`:
`γ_{n-1}^A γ_j y = y_n q_a(w) (F_a(w), 1)` where `w = normalizeCone y`. -/
theorem accelMove_eq_smul_toHomogeneous {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    accelMove a y =
      (y (Fin.last (d + 1)) * branchDenom a (normalizeCone y)) •
        toHomogeneous (branchMap a (normalizeCone y)) := by
  have hq : branchDenom a (normalizeCone y) ≠ 0 :=
    (branchDenom_pos a (normalizeCone_mem_orderedSimplex hy)).ne'
  calc accelMove a y
      = accelMove a (y (Fin.last (d + 1)) • toHomogeneous (normalizeCone y)) := by
          rw [smul_toHomogeneous_normalizeCone (orderedCone_subset_coneSpan d hy)
            (last_pos_of_mem_orderedCone hy).ne']
    _ = y (Fin.last (d + 1)) • accelMove a (toHomogeneous (normalizeCone y)) := by
          rw [map_smul]
    _ = (y (Fin.last (d + 1)) * branchDenom a (normalizeCone y)) •
          toHomogeneous (branchMap a (normalizeCone y)) := by
          rw [accelMove_toHomogeneous a hq, smul_smul]

/-- The last coordinate of `γ_{n-1}^A γ_j y` on `orderedCone d` is `y_n q_a(normalizeCone y)`. -/
theorem accelMove_last_eq_mul_branchDenom {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    accelMove a y (Fin.last (d + 1)) =
      y (Fin.last (d + 1)) * branchDenom a (normalizeCone y) := by
  rw [accelMove_eq_smul_toHomogeneous a hy]
  simp

/-- Projective normalisation intertwines `accelMove a` and `branchMap a` on `orderedCone d`. -/
theorem normalizeCone_accelMove {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    normalizeCone (accelMove a y) = branchMap a (normalizeCone y) := by
  have hpos := last_pos_of_mem_orderedCone hy
  have hq := branchDenom_pos a (normalizeCone_mem_orderedSimplex hy)
  rw [accelMove_eq_smul_toHomogeneous a hy, normalizeCone_smul (mul_pos hpos hq).ne',
    normalizeCone_toHomogeneous]

/-- On `orderedCone d`, `branchDelay a (normalizeCone y) = log ((γ_a y)_n / y_n)`. -/
theorem branchDelay_normalizeCone {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    branchDelay a (normalizeCone y) =
      Real.log (accelMove a y (Fin.last (d + 1)) / y (Fin.last (d + 1))) := by
  rw [accelMove_last_eq_mul_branchDenom a hy,
    mul_div_cancel_left₀ _ (last_pos_of_mem_orderedCone hy).ne', branchDelay_def]

/-- Every accelerated branch maps `orderedSimplex d` into itself. -/
theorem branchMap_mapsTo {d : ℕ} (a : ℕ × Fin d) :
    MapsTo (branchMap a) (orderedSimplex d) (orderedSimplex d) := by
  intro x hx
  have hq := branchDenom_pos a hx
  rw [mem_orderedSimplex_iff]
  refine ⟨fun i => by rw [branchMap_def]; exact div_nonneg (toProjective_nonneg hx _) hq.le,
    fun i₁ i₂ h => by
      rw [branchMap_def, branchMap_def]
      exact div_le_div_of_nonneg_right
        (monotone_toProjective hx ((Fin.strictMono_succAbove _).monotone h)) hq.le,
    fun i => ?_⟩
  rw [one_sub_sum_branchMap a hq.ne', branchMap_def]
  refine div_le_div_of_nonneg_right ?_ hq.le
  have hle1 : toProjective x (a.2.castSucc.succAbove i) ≤ 1 := toProjective_le_one hx _
  have hnonneg : 0 ≤ (a.1 : ℝ) * (1 - x a.2) :=
    mul_nonneg (Nat.cast_nonneg a.1) (by linarith [coord_le_half_of_mem_orderedSimplex hx a.2])
  linarith

/-! ### Derivatives and smoothness of the branches -/

/-- The open neighbourhood `{x | 0 < branchDenom a x}` of `orderedSimplex d`. -/
theorem isOpen_branchDenom_pos {d : ℕ} (a : ℕ × Fin d) :
    IsOpen {x : Fin d → ℝ | 0 < branchDenom a x} := by
  have hcont : Continuous (branchDenom a) := by
    unfold branchDenom
    fun_prop
  exact isOpen_lt continuous_const hcont

/-- The ordered simplex lies inside `{x | 0 < branchDenom a x}`. -/
theorem orderedSimplex_subset_branchDenom_pos {d : ℕ} (a : ℕ × Fin d) :
    orderedSimplex d ⊆ {x : Fin d → ℝ | 0 < branchDenom a x} :=
  fun _ hx => branchDenom_pos a hx

/-- The Fréchet derivative of `branchDenom a` at any point `x`. -/
theorem hasFDerivAt_branchDenom {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    HasFDerivAt (branchDenom a)
      ((-((a.1 : ℝ) + 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) a.2) x := by
  have h :=
    ((((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2).hasFDerivAt
      (x := x)).const_sub (1 : ℝ)).const_mul ((a.1 : ℝ) + 1)).const_add (1 : ℝ)
  rw [smul_neg, ← neg_smul] at h
  exact h

/-- The Fréchet derivative of `branchDelay a = log ∘ branchDenom a` wherever `q_a(x) ≠ 0`. -/
theorem hasFDerivAt_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    HasFDerivAt (branchDelay a)
      ((-((a.1 : ℝ) + 1) / branchDenom a x) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) a.2) x := by
  have h := (hasFDerivAt_branchDenom a x).log hq
  have hmul : (branchDenom a x)⁻¹ * -((a.1 : ℝ) + 1) = -((a.1 : ℝ) + 1) / branchDenom a x := by
    ring
  rw [smul_smul, hmul] at h
  exact h

/-- Formula for `fderiv ℝ (branchDelay a) x` wherever `q_a(x) ≠ 0`. -/
theorem fderiv_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hq : branchDenom a x ≠ 0) :
    fderiv ℝ (branchDelay a) x =
      (-((a.1 : ℝ) + 1) / branchDenom a x) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) a.2 :=
  (hasFDerivAt_branchDelay a hq).fderiv

/-- The `j`-th partial derivative of `log q_a` equals `-(A + 1) / q_a`. -/
theorem fderiv_branchDelay_single_self {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    fderiv ℝ (branchDelay a) x (Pi.single a.2 (1 : ℝ)) =
      -((a.1 : ℝ) + 1) / branchDenom a x := by
  rw [fderiv_branchDelay a hq]
  simp

/-- All partial derivatives of `log q_a` in coordinates `k ≠ j` vanish. -/
theorem fderiv_branchDelay_single_of_ne {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) {k : Fin d} (hk : k ≠ a.2) :
    fderiv ℝ (branchDelay a) x (Pi.single k (1 : ℝ)) = 0 := by
  rw [fderiv_branchDelay a hq]
  simp [Pi.single_eq_of_ne hk.symm]

/-- Operator norm of `d (log q_a)` in the sup norm on `Fin d → ℝ`. -/
theorem norm_fderiv_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) :
    ‖fderiv ℝ (branchDelay a) x‖ = ((a.1 : ℝ) + 1) / branchDenom a x := by
  have hproj_norm : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2‖ = 1 := by
    refine le_antisymm ?_ ?_
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using norm_le_pi_norm v a.2
    · have h1 := ContinuousLinearMap.le_opNorm
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2)
        (Pi.single a.2 (1 : ℝ))
      have hsing : ‖(Pi.single a.2 (1 : ℝ) : Fin d → ℝ)‖ = 1 := by
        simp [Pi.norm_single]
      simpa [hsing] using h1
  rw [fderiv_branchDelay a hq.ne', norm_smul, hproj_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) hq.le),
    neg_div, neg_neg]

/-- Uniform logarithmic derivative bound `‖d (log q_a)‖ ≤ 2 (A + 1) / (A + 3)` on
`orderedSimplex d`. -/
theorem norm_fderiv_branchDelay_le {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    ‖fderiv ℝ (branchDelay a) x‖ ≤ 2 * ((a.1 : ℝ) + 1) / ((a.1 : ℝ) + 3) := by
  rw [norm_fderiv_branchDelay a (branchDenom_pos a hx)]
  have hge := branchDenom_ge a hx
  rw [div_le_div_iff₀ (branchDenom_pos a hx) (by positivity)]
  nlinarith

/-- Uniform strict bound `‖d (log q_a)‖ < 2` on `orderedSimplex d`, independent of `A`, `j`, and
`x`. -/
theorem norm_fderiv_branchDelay_lt_two {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    ‖fderiv ℝ (branchDelay a) x‖ < 2 := by
  refine (norm_fderiv_branchDelay_le a hx).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- On `orderedSimplex d`, `fderivWithin` of `branchDelay a` coincides with `fderiv`. -/
theorem fderivWithin_branchDelay_eq {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    fderivWithin ℝ (branchDelay a) (orderedSimplex d) x = fderiv ℝ (branchDelay a) x :=
  (hasFDerivAt_branchDelay a (branchDenom_pos a hx).ne').differentiableAt.fderivWithin
    (uniqueDiffOn_orderedSimplex d x hx)

/-- `branchDenom a` is smooth (in fact analytic) on all of `Fin d → ℝ`. -/
theorem contDiff_branchDenom {d : ℕ} (a : ℕ × Fin d) (n : WithTop ℕ∞) :
    ContDiff ℝ n (branchDenom a) := by
  unfold branchDenom
  exact contDiff_const.add
    (contDiff_const.mul (contDiff_const.sub (contDiff_apply ℝ (fun _ : Fin d => ℝ) a.2)))

/-- `branchDelay a` is smooth on the open neighbourhood `{x | 0 < branchDenom a x}`. -/
theorem contDiffOn_branchDelay {d : ℕ} (a : ℕ × Fin d) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (branchDelay a) {x : Fin d → ℝ | 0 < branchDenom a x} :=
  (contDiff_branchDenom a n).contDiffOn.log fun _ hx => hx.ne'

/-- `branchDelay a` is smooth on `orderedSimplex d`. -/
theorem contDiffOn_branchDelay_orderedSimplex {d : ℕ} (a : ℕ × Fin d) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (branchDelay a) (orderedSimplex d) :=
  (contDiffOn_branchDelay a n).mono (orderedSimplex_subset_branchDenom_pos a)

/-- `branchMap a` is smooth on the open neighbourhood `{x | 0 < branchDenom a x}`. -/
theorem contDiffOn_branchMap {d : ℕ} (a : ℕ × Fin d) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (branchMap a) {x : Fin d → ℝ | 0 < branchDenom a x} := by
  rw [contDiffOn_pi]
  intro i
  simp only [branchMap_def]
  have hnum : ContDiff ℝ n (fun x : Fin d → ℝ => toProjective x (a.2.castSucc.succAbove i)) := by
    refine Fin.lastCases ?_ (fun k => ?_) (a.2.castSucc.succAbove i)
    · simp only [toProjective_last]
      exact contDiff_const.sub (ContDiff.sum fun m _ => contDiff_apply ℝ (fun _ : Fin d => ℝ) m)
    · simp only [toProjective_castSucc]
      exact contDiff_apply ℝ (fun _ : Fin d => ℝ) k
  exact hnum.contDiffOn.div (contDiff_branchDenom a n).contDiffOn fun _ hx => hx.ne'

/-- `branchMap a` is smooth on `orderedSimplex d`. -/
theorem contDiffOn_branchMap_orderedSimplex {d : ℕ} (a : ℕ × Fin d) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (branchMap a) (orderedSimplex d) :=
  (contDiffOn_branchMap a n).mono (orderedSimplex_subset_branchDenom_pos a)

/-! ### Complex weights -/

/-- Wherever `q_a(x) > 0`, the complex weight `q_a(x)^{-s}` equals `exp (-s * τ_a(x))`. -/
theorem branchDenom_cpow_neg_eq_exp {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (s : ℂ) :
    (branchDenom a x : ℂ) ^ (-s) = Complex.exp (-s * (branchDelay a x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hq.ne'),
    ← Complex.ofReal_log hq.le, branchDelay_def, mul_comm]

/-- Wherever `q_a(x) > 0`, `‖q_a(x)^{-s}‖ = q_a(x)^{-Re s}`. -/
theorem norm_branchDenom_cpow_neg {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (s : ℂ) :
    ‖(branchDenom a x : ℂ) ^ (-s)‖ = (branchDenom a x) ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq (-s), Complex.neg_re]

/-- At real `σ`, the complex weight `q_a(x)^{-σ}` equals the coercion of the positive real
power `q_a(x)^{-σ}`. -/
theorem branchDenom_cpow_neg_ofReal {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (σ : ℝ) :
    (branchDenom a x : ℂ) ^ (-(σ : ℂ)) = (((branchDenom a x) ^ (-σ) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_neg, Complex.ofReal_cpow hq.le]

/-- At real `σ`, the real weight `q_a(x)^{-σ}` is strictly positive wherever `q_a(x) > 0`. -/
theorem branchDenom_rpow_neg_pos {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (σ : ℝ) :
    0 < (branchDenom a x) ^ (-σ) :=
  Real.rpow_pos_of_pos hq (-σ)

end TauCeti.OrderedSimplex
