/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Intervals

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
  set θ := φ i
  have hθ0 : θ ≤ 0 := hlast ▸ hmono i n hi.le le_rfl
  have hθlow : -2 * Real.pi < θ := hlow i hi.le
  -- Signs of the individual steps, according to where the direction lies relative to `θ`.
  have hstep_nonneg (l : ℕ) (hl : l < n) (h₁ : θ ≤ φ l) (h₂ : φ l ≤ θ + Real.pi) :
      0 ≤ H (l + 1) - H l := by
    obtain ⟨d, hd, h⟩ := hstep l hl
    rw [h]
    exact mul_nonneg hd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  have hstep_nonneg' (l : ℕ) (hl : l < n) (h : φ l ≤ θ - Real.pi) :
      0 ≤ H (l + 1) - H l := by
    obtain ⟨d, hd, h'⟩ := hstep l hl
    have := hlow l hl.le
    rw [h', ← Real.sin_add_two_pi]
    exact mul_nonneg hd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  have hstep_nonpos (l : ℕ) (hl : l < n) (h₁ : θ - Real.pi ≤ φ l) (h₂ : φ l ≤ θ) :
      H (l + 1) - H l ≤ 0 := by
    obtain ⟨d, hd, h⟩ := hstep l hl
    rw [h]
    exact mul_nonpos_of_nonneg_of_nonpos hd
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))
  have hstep_nonpos' (l : ℕ) (hl : l < n) (h : θ + Real.pi ≤ φ l) :
      H (l + 1) - H l ≤ 0 := by
    obtain ⟨d, hd, h'⟩ := hstep l hl
    have := hmono l n hl.le le_rfl
    rw [hlast] at this
    rw [h', ← Real.sin_sub_two_pi]
    exact mul_nonpos_of_nonneg_of_nonpos hd
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))
  obtain ⟨r₁, hr₁, hc₁⟩ := hclose₁
  obtain ⟨r₂, hr₂, hc₂⟩ := hclose₂
  -- The closing steps rise when the side points no further back than `-π`, and fall otherwise.
  have hclose_nonneg (h : -Real.pi ≤ θ) : 0 ≤ Hinf - H n ∧ 0 ≤ H 0 - Hinf := by
    have hsin : 0 ≤ Real.sin (-θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    exact ⟨hc₁ ▸ mul_nonneg hr₁ hsin, hc₂ ▸ mul_nonneg hr₂ hsin⟩
  have hclose_nonpos (h : θ ≤ -Real.pi) : Hinf - H n ≤ 0 ∧ H 0 - Hinf ≤ 0 := by
    have hsin : Real.sin (-θ) ≤ 0 := by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    exact ⟨hc₁ ▸ mul_nonpos_of_nonneg_of_nonpos hr₁ hsin,
      hc₂ ▸ mul_nonpos_of_nonneg_of_nonpos hr₂ hsin⟩
  have hvertex (k : ℕ) (hk : k ≤ n) : 0 ≤ H k := by
    rcases lt_or_ge i k with hik | hki
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      by_cases hshort : φ k ≤ θ + Real.pi
      · -- Every side from `i` up to vertex `k` turns by at most `π`: the height rises.
        have htel := Finset.sum_Ico_sub H (show i ≤ k + 1 by omega)
        rw [hHi, sub_zero] at htel
        rw [← htel]
        refine Finset.sum_nonneg fun l hl ↦ ?_
        rw [Finset.mem_Ico] at hl
        exact hstep_nonneg l (by omega) (hmono i l hl.1 (by omega))
          ((hmono l k (by omega) (by omega)).trans hshort)
      · -- Otherwise follow the boundary on through the closing side back to `i`: the height
        -- only falls, and it returns to zero.
        rw [not_le] at hshort
        have hθπ : θ < -Real.pi := by linarith [hmono k n (by omega) le_rfl]
        have h₁ : ∑ l ∈ Finset.Ico (k + 1) n, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos' l hl.2 (hshort.le.trans (hmono k l (by omega) hl.2.le))
        have h₂ : ∑ l ∈ Finset.Ico 0 i, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos l (by omega) (by linarith [hlow l (by omega)])
              (hmono l i hl.2.le hi.le)
        rw [Finset.sum_Ico_sub H hk, Finset.sum_Ico_sub H (Nat.zero_le i), hHi] at *
        linarith [hclose_nonpos hθπ.le]
    · by_cases hshort : θ - Real.pi ≤ φ k
      · -- Every side from vertex `k` up to `i` turns back by at most `π`: the height falls
        -- to zero.
        have h : ∑ l ∈ Finset.Ico k i, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos l (by omega) (hshort.trans (hmono k l hl.1 (by omega)))
              (hmono l i hl.2.le hi.le)
        rw [Finset.sum_Ico_sub H hki, hHi] at h
        linarith
      · -- Otherwise reach vertex `k` from `i` the other way round: the height only rises.
        rw [not_le] at hshort
        have hθπ : -Real.pi ≤ θ := by linarith [hlow k hk]
        have h₁ : 0 ≤ ∑ l ∈ Finset.Ico i n, (H (l + 1) - H l) :=
          Finset.sum_nonneg fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            have := hmono l n hl.2.le le_rfl
            exact hstep_nonneg l hl.2 (hmono i l hl.1 hl.2.le) (by linarith)
        have h₂ : 0 ≤ ∑ l ∈ Finset.Ico 0 k, (H (l + 1) - H l) :=
          Finset.sum_nonneg fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonneg' l (by omega)
              ((hmono l k hl.2.le hk).trans hshort.le)
        rw [Finset.sum_Ico_sub H hi.le, Finset.sum_Ico_sub H (Nat.zero_le k), hHi] at *
        linarith [hclose_nonneg hθπ]
  refine ⟨hvertex, ?_⟩
  rcases le_total (-Real.pi) θ with hθπ | hθπ
  · linarith [hvertex n le_rfl, (hclose_nonneg hθπ).1]
  · linarith [hvertex 0 (Nat.zero_le n), (hclose_nonpos hθπ).2]

end TauCeti
