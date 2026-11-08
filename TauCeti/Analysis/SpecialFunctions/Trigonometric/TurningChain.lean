/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Heights along a closed chain with monotone turning

Consider a closed planar chain whose step directions turn monotonically through less than one
full turn and whose last two steps point in direction `0`.  Measure the height of each point of
the chain after rotating the direction of one of its steps to the positive real axis.  Along the
chain the height first rises and then falls, and since the chain closes up the height is
nonnegative throughout: the line through that step supports the whole chain.

The statement only records the heights: a step of length `d ≥ 0` and direction `ψ`, measured
from a reference direction `θ`, raises the height by `d * sin (ψ - θ)`.

## Main results

* `TauCeti.heights_nonneg_of_monotone_turning` -- every height of such a chain, measured from
  the line through one of its steps, is nonnegative.
-/

public section

namespace TauCeti

/-- **The height at vertex `k + 1` is nonnegative**, for `i ≤ k < n`, when the directions `φ` turn
monotonically through `(-2π, 0]` with `φ n = 0`, every step `l < n` raises the height by
`d * sin (φ l - φ i)` with `d ≥ 0`, and the height is normalized by `H i = 0`. The closing steps
through `Hinf` are assumed, in case `φ i ≤ -π`, not to raise the height: `Hinf - H n ≤ 0` and
`H 0 - Hinf ≤ 0`. -/
private lemma height_succ_nonneg {n i k : ℕ} (hi : i < n) (hik : i ≤ k) (hkn : k < n)
    {H φ : ℕ → ℝ} {Hinf : ℝ} (hmono : ∀ l m, l ≤ m → m ≤ n → φ l ≤ φ m)
    (hlow : ∀ l ≤ n, -2 * Real.pi < φ l) (hlast : φ n = 0)
    (hstep : ∀ l < n, ∃ d, 0 ≤ d ∧ H (l + 1) - H l = d * Real.sin (φ l - φ i))
    (hHi : H i = 0) (hclose : φ i ≤ -Real.pi → Hinf - H n ≤ 0 ∧ H 0 - Hinf ≤ 0) :
    0 ≤ H (k + 1) := by
  -- Either every side from `i` to `k + 1` turns by at most `π`, so the height rises, or one
  -- follows the boundary on through the closing side back to `i`, so it only falls to zero.
  by_cases hshort : φ k ≤ φ i + Real.pi
  · have htel := Finset.sum_Ico_sub H (Nat.le_succ_of_le hik)
    rw [hHi, sub_zero] at htel
    rw [← htel]
    refine Finset.sum_nonneg fun l hl ↦ ?_
    rw [Finset.mem_Ico] at hl
    exact nonneg_of_step_of_le_add_pi (hstep l (by omega)) (hmono i l hl.1 (by omega))
      ((hmono l k (by omega) (by omega)).trans hshort)
  · rw [not_le] at hshort
    have hθπ : φ i < -Real.pi := by linarith [hmono k n (by omega) le_rfl]
    have h₁ : ∑ l ∈ Finset.Ico (k + 1) n, (H (l + 1) - H l) ≤ 0 :=
      Finset.sum_nonpos fun l hl ↦ by
        rw [Finset.mem_Ico] at hl
        have := hmono l n hl.2.le le_rfl
        exact nonpos_of_step_of_add_pi_le (hstep l hl.2)
          (hshort.le.trans (hmono k l (by omega) hl.2.le))
          (by linarith [hlow i hi.le, hlast ▸ this])
    have h₂ : ∑ l ∈ Finset.Ico 0 i, (H (l + 1) - H l) ≤ 0 :=
      Finset.sum_nonpos fun l hl ↦ by
        rw [Finset.mem_Ico] at hl
        exact nonpos_of_step_of_sub_pi_le (hstep l (by omega))
          (by linarith [hlow l (by omega)]) (hmono l i hl.2.le hi.le)
    rw [Finset.sum_Ico_sub H hkn] at h₁
    rw [Finset.sum_Ico_sub H (Nat.zero_le i), hHi] at h₂
    linarith [hclose hθπ.le]

/-- **The height at vertex `k ≤ i` is nonnegative**, when the directions `φ` turn monotonically
through `(-2π, 0]` with `φ n = 0`, every step `l < n` raises the height by `d * sin (φ l - φ i)`
with `d ≥ 0`, and the height is normalized by `H i = 0`. The closing steps through `Hinf` are
assumed, in case `-π ≤ φ i`, not to lower the height: `0 ≤ Hinf - H n` and `0 ≤ H 0 - Hinf`. -/
private lemma height_nonneg_of_le {n i k : ℕ} (hi : i < n) (hki : k ≤ i)
    {H φ : ℕ → ℝ} {Hinf : ℝ} (hmono : ∀ l m, l ≤ m → m ≤ n → φ l ≤ φ m)
    (hlow : ∀ l ≤ n, -2 * Real.pi < φ l) (hlast : φ n = 0)
    (hstep : ∀ l < n, ∃ d, 0 ≤ d ∧ H (l + 1) - H l = d * Real.sin (φ l - φ i))
    (hHi : H i = 0) (hclose : -Real.pi ≤ φ i → 0 ≤ Hinf - H n ∧ 0 ≤ H 0 - Hinf) :
    0 ≤ H k := by
  have hk : k ≤ n := by omega
  -- Either every side from `k` up to `i` turns back by at most `π`, so the height falls to zero,
  -- or one reaches `k` from `i` the other way round, so the height only rises.
  by_cases hshort : φ i - Real.pi ≤ φ k
  · have h : ∑ l ∈ Finset.Ico k i, (H (l + 1) - H l) ≤ 0 :=
      Finset.sum_nonpos fun l hl ↦ by
        rw [Finset.mem_Ico] at hl
        exact nonpos_of_step_of_sub_pi_le (hstep l (by omega))
          (hshort.trans (hmono k l hl.1 (by omega))) (hmono l i hl.2.le hi.le)
    rw [Finset.sum_Ico_sub H hki, hHi] at h
    linarith
  · rw [not_le] at hshort
    have hθπ : -Real.pi ≤ φ i := by linarith [hlow k hk]
    have h₁ : 0 ≤ ∑ l ∈ Finset.Ico i n, (H (l + 1) - H l) :=
      Finset.sum_nonneg fun l hl ↦ by
        rw [Finset.mem_Ico] at hl
        have := hmono l n hl.2.le le_rfl
        exact nonneg_of_step_of_le_add_pi (hstep l hl.2) (hmono i l hl.1 hl.2.le)
          (by linarith)
    have h₂ : 0 ≤ ∑ l ∈ Finset.Ico 0 k, (H (l + 1) - H l) :=
      Finset.sum_nonneg fun l hl ↦ by
        rw [Finset.mem_Ico] at hl
        exact nonneg_of_step_of_le_sub_pi (hstep l (by omega))
          (by linarith [hlow l (by omega), hlast ▸ hmono i n hi.le le_rfl])
          ((hmono l k hl.2.le hk).trans hshort.le)
    rw [Finset.sum_Ico_sub H hi.le, hHi] at h₁
    rw [Finset.sum_Ico_sub H (Nat.zero_le k)] at h₂
    linarith [hclose hθπ]

/-- **Heights along a closed chain with monotone turning are nonnegative.**  A closed chain of
`n + 2` steps starts and ends at height zero: `n` steps `H l ↦ H (l + 1)` whose directions `φ l`
are monotone in `(-2π, 0]` with `φ n = 0`, followed by two steps through `Hinf` in direction `0`.
All heights are measured after rotating the direction `φ i` of a step `i < n` to zero, so a step
of length `d` and direction `ψ` raises the height by `d * sin (ψ - φ i)`.  Then every height is
nonnegative. -/
theorem heights_nonneg_of_monotone_turning {n i : ℕ} (hi : i < n) {H φ : ℕ → ℝ} {Hinf : ℝ}
    (hmono : ∀ l m, l ≤ m → m ≤ n → φ l ≤ φ m) (hlow : ∀ l ≤ n, -2 * Real.pi < φ l)
    (hlast : φ n = 0)
    (hstep : ∀ l < n, ∃ d, 0 ≤ d ∧ H (l + 1) - H l = d * Real.sin (φ l - φ i))
    (hclose₁ : ∃ r, 0 ≤ r ∧ Hinf - H n = r * Real.sin (-φ i))
    (hclose₂ : ∃ r, 0 ≤ r ∧ H 0 - Hinf = r * Real.sin (-φ i)) (hHi : H i = 0) :
    (∀ k ≤ n, 0 ≤ H k) ∧ 0 ≤ Hinf := by
  have hθ0 : φ i ≤ 0 := hlast ▸ hmono i n hi.le le_rfl
  have hθlow : -2 * Real.pi < φ i := hlow i hi.le
  simp only [← zero_sub (φ i)] at hclose₁ hclose₂
  -- The closing steps rise when the side points no further back than `-π`, and fall otherwise.
  have hclose_nonneg (h : -Real.pi ≤ φ i) : 0 ≤ Hinf - H n ∧ 0 ≤ H 0 - Hinf :=
    ⟨nonneg_of_step_of_le_add_pi hclose₁ hθ0 (by linarith),
      nonneg_of_step_of_le_add_pi hclose₂ hθ0 (by linarith)⟩
  have hclose_nonpos (h : φ i ≤ -Real.pi) : Hinf - H n ≤ 0 ∧ H 0 - Hinf ≤ 0 :=
    ⟨nonpos_of_step_of_add_pi_le hclose₁ (by linarith) (by linarith),
      nonpos_of_step_of_add_pi_le hclose₂ (by linarith) (by linarith)⟩
  have hvertex (k : ℕ) (hk : k ≤ n) : 0 ≤ H k := by
    rcases lt_or_ge i k with hik | hki
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact height_succ_nonneg hi (by omega) (by omega) hmono hlow hlast hstep hHi hclose_nonpos
    · exact height_nonneg_of_le hi hki hmono hlow hlast hstep hHi hclose_nonneg
  refine ⟨hvertex, ?_⟩
  rcases le_total (-Real.pi) (φ i) with hθπ | hθπ
  · linarith [hvertex n le_rfl, (hclose_nonneg hθπ).1]
  · linarith [hvertex 0 (Nat.zero_le n), (hclose_nonpos hθπ).2]

end TauCeti
