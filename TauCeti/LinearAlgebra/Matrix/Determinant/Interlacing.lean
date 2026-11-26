/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Interlacing as a determinant of indicators

Two weakly decreasing sequences `x` and `y` of length `k` in a linear order *interlace* if
`x 0 > y 0 ≥ x 1 > y 1 ≥ ⋯ ≥ x (k - 1) > y (k - 1)`. This file shows that interlacing is detected
by a determinant: the `k × k` matrix with `(b, c)` entry `1` if `y c < x b` and `0` otherwise has
determinant `1` if `x` and `y` interlace, and `0` otherwise
(`Matrix.det_interlacing_indicator`).

In `TauCeti.MeasureTheory.Measure.Lebesgue.PieriCone` the statement turns the indicator of a cone
of interlacing inequalities into an alternating sum over permutations.

## Provenance

The statement and the expansion along the first column are adapted from the lemma
`New.det_interlacing_indicator` of grh-lean (https://github.com/lsernau/grh-lean,
`src/New/UpperBound/ElementaryDivisors/PieriCone.lean`, Apache 2.0, Copyright 2026 Anthropic,
PBC), there stated for real sequences and real matrices.
-/

public section

open Finset

namespace Matrix

variable {R α : Type*} [CommRing R] [LinearOrder α]

/-- For weakly decreasing `x` and `y` in `α ^ k`, the matrix with `(b, c)` entry `1` if
`y c < x b` and `0` otherwise has determinant `1` if the two interlace,
`x 0 > y 0 ≥ x 1 > y 1 ≥ ⋯`, and `0` otherwise. -/
theorem det_interlacing_indicator {k : ℕ} {x y : Fin k → α} (hx : Antitone x)
    (hy : Antitone y) :
    det (of fun b c : Fin k ↦ if y c < x b then (1 : R) else 0) =
      if (∀ b : Fin k, y b < x b) ∧ ∀ b c : Fin k, b.val + 1 = c.val → x c ≤ y b then 1
      else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨b, hb⟩ | h_none := exists_or_forall_not fun b : Fin k ↦ y 0 < x b.succ
    · -- If `y 0 < x b.succ`, rows `0` and `b.succ` consist of ones, and interlacing fails.
      have h_row_succ (c : Fin (k + 1)) : y c < x b.succ := (hy c.zero_le).trans_lt hb
      have h_row_zero (c : Fin (k + 1)) : y c < x 0 :=
        (h_row_succ c).trans_le (hx b.succ.zero_le)
      rw [ite_eq_right fun ⟨_, h_le⟩ ↦
        (h_row_succ b.castSucc).not_ge (h_le b.castSucc b.succ rfl)]
      exact det_zero_of_row_eq b.succ_ne_zero (funext fun c ↦ by simp [h_row_succ, h_row_zero])
    · -- Otherwise column `0` vanishes below the top: expand along it.
      have h_expand : det (of fun b c : Fin (k + 1) ↦ if y c < x b then (1 : R) else 0) =
          (if y 0 < x 0 then 1 else 0) *
            det (of fun b c : Fin k ↦ if y c.succ < x b.succ then (1 : R) else 0) := by
        simp [det_succ_column_zero, Fin.sum_univ_succ, h_none]
        -- The minor `(of f).submatrix Fin.succ Fin.succ` is, by the definitions of `submatrix`
        -- and `of`, the matrix `of fun b c ↦ f b.succ c.succ`.
        rfl
      rw [h_expand, ih (x := fun b ↦ x b.succ) (y := fun b ↦ y b.succ)
        (hx.comp_monotone (Fin.strictMono_succ).monotone)
        (hy.comp_monotone (Fin.strictMono_succ).monotone)]
      -- As every `x b.succ ≤ y 0`, interlacing is `y 0 < x 0` and interlacing of the tails.
      have h_split : ((∀ b : Fin (k + 1), y b < x b) ∧
            ∀ b c : Fin (k + 1), b.val + 1 = c.val → x c ≤ y b) ↔
          y 0 < x 0 ∧ (∀ b : Fin k, y b.succ < x b.succ) ∧
            ∀ b c : Fin k, b.val + 1 = c.val → x c.succ ≤ y b.succ := by
        simp [Fin.forall_fin_succ, fun b : Fin k ↦ not_lt.1 (h_none b), and_assoc]
      simp only [h_split, ite_zero_mul_ite_zero, mul_one]

end Matrix
