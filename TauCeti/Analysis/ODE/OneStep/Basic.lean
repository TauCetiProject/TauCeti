/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Meshes and one-step methods

A one-step method for the initial value problem `y' = f (t, y)`, `y t₀ = y₀`, on a real normed
space `E` is given by an *increment function* `Φ : ℝ → E → ℝ → E`, with arguments time, state and
step: one step from `(t, y)` with step `h` leads to `y + h • Φ t y h`. The explicit Euler method
has `Φ t y h = f t y`; Runge–Kutta methods have more elaborate increment functions.

This file sets up the objects of the convergence theory of such methods on a mesh with variable
steps.

* `TauCeti.meshNode t₀ h n = t₀ + h 0 + ⋯ + h (n - 1)`: the nodes of the mesh with first node
  `t₀` and steps `h : ℕ → ℝ`.
* `TauCeti.oneStepSeq Φ t₀ h y₀`: the numerical solution, `Y 0 = y₀` and
  `Y (n + 1) = Y n + h n • Φ (t_n) (Y n) (h n)`.
* `TauCeti.oneStepDefect Φ y t h = y (t + h) - y t - h • Φ t (y t) h`: the defect of a curve `y`
  under one step of the method. The local truncation error of the literature is the defect
  divided by `h`; the defect needs no division and vanishes at `h = 0`.

The definitions allow steps of any sign; the stability and convergence theorems assume
nonnegative steps.

## Main results

* `TauCeti.monotoneOn_meshNode`: with nonnegative steps the nodes are nondecreasing.
* `TauCeti.oneStepDefect_meshNode`: inserting the values `y (t_n)` of a curve into one step of
  the method leaves exactly the defect of `y`.
* `TauCeti.meshNode_congr`, `TauCeti.oneStepSeq_congr`: the `n`-th node and the `n`-th value of
  the numerical solution depend only on the first `n` steps.
* `TauCeti.continuous_oneStepSeq`: for a jointly continuous increment function, the `n`-th value
  of the numerical solution is jointly continuous in the initial value and the steps.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford, 2022, Section 2.
-/

public section

open Finset

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Meshes -/

/-- The `n`-th node `t₀ + h 0 + ⋯ + h (n - 1)` of the mesh with first node `t₀` and steps `h`. -/
def meshNode (t₀ : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ := t₀ + ∑ i ∈ range n, h i

theorem meshNode_def (t₀ : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    meshNode t₀ h n = t₀ + ∑ i ∈ range n, h i := (rfl)

/-- The distance from the first node to the `n`-th node is the sum of the first `n` steps. -/
theorem meshNode_sub_self (t₀ : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    meshNode t₀ h n - t₀ = ∑ i ∈ range n, h i := by
  rw [meshNode_def, add_sub_cancel_left]

@[simp]
theorem meshNode_zero (t₀ : ℝ) (h : ℕ → ℝ) : meshNode t₀ h 0 = t₀ := by
  simp [meshNode_def]

@[simp]
theorem meshNode_succ (t₀ : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    meshNode t₀ h (n + 1) = meshNode t₀ h n + h n := by
  simp [meshNode_def, sum_range_succ, add_assoc]

/-- The nodes of a uniform mesh with step `η` are `t₀ + n η`. -/
@[simp]
theorem meshNode_const (t₀ η : ℝ) (n : ℕ) : meshNode t₀ (fun _ ↦ η) n = t₀ + n * η := by
  simp [meshNode_def]

/-- The `n`-th node depends only on the first `n` steps `h 0, …, h (n - 1)`. -/
theorem meshNode_congr {t₀ : ℝ} {h h' : ℕ → ℝ} {n : ℕ} (hh : ∀ i < n, h i = h' i) :
    meshNode t₀ h n = meshNode t₀ h' n := by
  simp only [meshNode_def]
  congr 1
  exact sum_congr rfl fun i hi ↦ hh i (mem_range.1 hi)

/-- If the first `N` steps are nonnegative, the nodes are nondecreasing up to index `N`. -/
theorem monotoneOn_meshNode {t₀ : ℝ} {h : ℕ → ℝ} {N : ℕ} (hh : ∀ n < N, 0 ≤ h n) :
    MonotoneOn (meshNode t₀ h) (Set.Iic N) := by
  intro m _ n hn hmn
  simp only [meshNode_def, add_le_add_iff_left]
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hmn) fun i hi _ ↦
    hh i ((mem_range.1 hi).trans_le hn)

/-- If the first `N` steps are nonnegative, the nodes up to index `N` lie to the right of the
first node. -/
theorem self_le_meshNode {t₀ : ℝ} {h : ℕ → ℝ} {N n : ℕ} (hh : ∀ n < N, 0 ≤ h n)
    (hn : n ≤ N) : t₀ ≤ meshNode t₀ h n := by
  simpa using monotoneOn_meshNode hh (Set.mem_Iic.2 (Nat.zero_le N)) hn (Nat.zero_le n)

/-- The `n`-th node is continuous in the steps, for the product topology on step sequences. -/
@[fun_prop]
theorem continuous_meshNode (t₀ : ℝ) (n : ℕ) : Continuous fun h : ℕ → ℝ ↦ meshNode t₀ h n := by
  simp only [meshNode_def]
  fun_prop

/-! ### One-step methods -/

/-- The numerical solution of the one-step method with increment function `Φ` on the mesh with
first node `t₀` and steps `h`, started at `y₀`: `Y 0 = y₀` and
`Y (n + 1) = Y n + h n • Φ (t_n) (Y n) (h n)`, where `t_n = meshNode t₀ h n`. -/
def oneStepSeq (Φ : ℝ → E → ℝ → E) (t₀ : ℝ) (h : ℕ → ℝ) (y₀ : E) : ℕ → E
  | 0 => y₀
  | n + 1 => oneStepSeq Φ t₀ h y₀ n + h n • Φ (meshNode t₀ h n) (oneStepSeq Φ t₀ h y₀ n) (h n)

@[simp]
theorem oneStepSeq_zero (Φ : ℝ → E → ℝ → E) (t₀ : ℝ) (h : ℕ → ℝ) (y₀ : E) :
    oneStepSeq Φ t₀ h y₀ 0 = y₀ := (rfl)

@[simp]
theorem oneStepSeq_succ (Φ : ℝ → E → ℝ → E) (t₀ : ℝ) (h : ℕ → ℝ) (y₀ : E) (n : ℕ) :
    oneStepSeq Φ t₀ h y₀ (n + 1) =
      oneStepSeq Φ t₀ h y₀ n + h n • Φ (meshNode t₀ h n) (oneStepSeq Φ t₀ h y₀ n) (h n) :=
  (rfl)

/-- The `n`-th value of the numerical solution depends only on the first `n` steps
`h 0, …, h (n - 1)`. -/
theorem oneStepSeq_congr {Φ : ℝ → E → ℝ → E} {t₀ : ℝ} {h h' : ℕ → ℝ} {y₀ : E} {n : ℕ}
    (hh : ∀ i < n, h i = h' i) : oneStepSeq Φ t₀ h y₀ n = oneStepSeq Φ t₀ h' y₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh' : ∀ i < n, h i = h' i := fun i hi ↦ hh i (hi.trans n.lt_succ_self)
    rw [oneStepSeq_succ, oneStepSeq_succ, ih hh', meshNode_congr hh', hh n n.lt_succ_self]

/-- If the increment function is jointly continuous, the `n`-th value of the numerical solution
is jointly continuous in the initial value and the steps, for the product topology on step
sequences. -/
theorem continuous_oneStepSeq {Φ : ℝ → E → ℝ → E}
    (hΦ : Continuous fun q : ℝ × E × ℝ ↦ Φ q.1 q.2.1 q.2.2) (t₀ : ℝ) (n : ℕ) :
    Continuous fun p : E × (ℕ → ℝ) ↦ oneStepSeq Φ t₀ p.2 p.1 n := by
  induction n with
  | zero => simpa using continuous_fst
  | succ n ih =>
    simp only [oneStepSeq_succ]
    have hh : Continuous fun p : E × (ℕ → ℝ) ↦ p.2 n := (continuous_apply n).comp continuous_snd
    have hnode : Continuous fun p : E × (ℕ → ℝ) ↦ meshNode t₀ p.2 n :=
      (continuous_meshNode t₀ n).comp continuous_snd
    exact ih.add (hh.smul (hΦ.comp (hnode.prodMk (ih.prodMk hh))))

/-! ### The defect -/

/-- The defect `y (t + h) - y t - h • Φ t (y t) h` of a curve `y` under one step of the
one-step method with increment function `Φ`, from time `t` with step `h`: the exact increment
minus the numerical one. The local truncation error is the defect divided by `h`. -/
def oneStepDefect (Φ : ℝ → E → ℝ → E) (y : ℝ → E) (t h : ℝ) : E :=
  y (t + h) - y t - h • Φ t (y t) h

theorem oneStepDefect_def (Φ : ℝ → E → ℝ → E) (y : ℝ → E) (t h : ℝ) :
    oneStepDefect Φ y t h = y (t + h) - y t - h • Φ t (y t) h := (rfl)

/-- The defect vanishes for the zero step. -/
@[simp]
theorem oneStepDefect_zero_right (Φ : ℝ → E → ℝ → E) (y : ℝ → E) (t : ℝ) :
    oneStepDefect Φ y t 0 = 0 := by
  simp [oneStepDefect_def]

/-- The defect of the zero increment function is the increment of the curve. -/
@[simp]
theorem oneStepDefect_zero_left (y : ℝ → E) (t h : ℝ) :
    oneStepDefect 0 y t h = y (t + h) - y t := by
  simp [oneStepDefect_def]

/-- Inserting the values `z n = y (t_n)` of a curve at the nodes into one step of the method
leaves the defect of `y`: `z (n + 1) - z n - h n • Φ (t_n) (z n) (h n)` is the defect of `y` at
`t_n` with step `h n`. -/
theorem oneStepDefect_meshNode (Φ : ℝ → E → ℝ → E) (y : ℝ → E) (t₀ : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    oneStepDefect Φ y (meshNode t₀ h n) (h n) =
      y (meshNode t₀ h (n + 1)) - y (meshNode t₀ h n) -
        h n • Φ (meshNode t₀ h n) (y (meshNode t₀ h n)) (h n) := by
  rw [oneStepDefect_def, meshNode_succ]

end TauCeti
