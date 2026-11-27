/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Windows covering a cylindrical end

Compactness theorems for Floer solutions on a domain with cylindrical ends, such as a pair of
pants or a PSS plane, are proved on countably many windows covering the domain. On an end with
coordinates `(s, t) ∈ ℝ × ℝ`, angular coordinate `t` of period one, the windows beyond height `T`
are the translates by `(m, 0)`, for `m ∈ ℕ`, of two end windows
`TauCeti.Floer.endWindow T b = (T + 1, T + 3) × (c - 2/5, c + 2/5)`, with `c = 0` for `b = false`
and `c = 1/2` for `b = true`.

This file records the bookkeeping that does not depend on a chart of the end: membership in an end
window is characterized by `TauCeti.Floer.mem_endWindow_iff`, the end windows are open, their
closures (`TauCeti.Floer.endWindow_closed_subset_Ioi_prod_Ioo`) and their translates by
`(m, 0)`, `m ≥ 0` (`TauCeti.Floer.endWindow_add_mem_Ioi_prod_Ioo`), lie beyond any `T' ≤ T` in a
band of angular width one, and every point `(s, t)` with `s > T + 1` is the translate of a point
of an end window by `(m, k)` for some `m ∈ ℕ` and `k ∈ ℤ`
(`TauCeti.Floer.exists_sub_mem_endWindow`). A chart of the end that is periodic of period one in
`t` then maps the translated end windows onto a neighbourhood of the end.
-/

public section

open Set

namespace TauCeti.Floer

/-- The end windows `(T + 1, T + 3) × (c - 2/5, c + 2/5)` of the coordinates `(s, t)` of a
cylindrical end, with `c = 0` for `b = false` and `c = 1/2` for `b = true`. -/
noncomputable def endWindow (T : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  Ioo (T + 1) (T + 3) ×ˢ
    Ioo ((bif b then 1 / 2 else 0) - 2 / 5) ((bif b then 1 / 2 else 0) + 2 / 5)

/-- Membership in an end window: `(s, t) ∈ endWindow T b` if and only if `T + 1 < s < T + 3`
and `c - 2/5 < t < c + 2/5`, with `c = 0` for `b = false` and `c = 1/2` for `b = true`. -/
@[simp]
theorem mem_endWindow_iff {T : ℝ} {b : Bool} {y : ℝ × ℝ} :
    y ∈ endWindow T b ↔ T + 1 < y.1 ∧ y.1 < T + 3 ∧
      (bif b then 1 / 2 else 0) - 2 / 5 < y.2 ∧ y.2 < (bif b then 1 / 2 else 0) + 2 / 5 := by
  rw [endWindow, mem_prod, mem_Ioo, mem_Ioo, and_assoc]

/-- The end windows are open. -/
theorem isOpen_endWindow (T : ℝ) (b : Bool) : IsOpen (endWindow T b) :=
  isOpen_Ioo.prod isOpen_Ioo

/-- The end windows lie in the closed windows `[T + 1, T + 3] × [c - 2/5, c + 2/5]`. -/
theorem endWindow_subset_Icc_prod_Icc (T : ℝ) (b : Bool) :
    endWindow T b ⊆ Icc (T + 1) (T + 3) ×ˢ
      Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5) ((bif b then 1 / 2 else 0) + 2 / 5) :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

/-- The closed end windows lie beyond any `T' ≤ T` in a band of angular width one. -/
theorem endWindow_closed_subset_Ioi_prod_Ioo {T' T : ℝ} (hT : T' ≤ T) (b : Bool) :
    Icc (T + 1) (T + 3) ×ˢ
        Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5) ((bif b then 1 / 2 else 0) + 2 / 5) ⊆
      Ioi T' ×ˢ
        Ioo ((bif b then 1 / 2 else 0) - 1 / 2) ((bif b then 1 / 2 else 0) - 1 / 2 + 1) := by
  rintro y ⟨⟨hs, -⟩, ht₁, ht₂⟩
  exact ⟨mem_Ioi.2 (by linarith), by linarith, by linarith⟩

/-- The translates by `(m, 0)`, `m ≥ 0`, of an end window beyond `T` lie beyond any `T' ≤ T` in
a band of angular width one. -/
theorem endWindow_add_mem_Ioi_prod_Ioo {T' T m : ℝ} (hT : T' ≤ T) (hm : 0 ≤ m) {b : Bool}
    {y : ℝ × ℝ} (hy : y ∈ endWindow T b) :
    y + (m, 0) ∈ Ioi T' ×ˢ
      Ioo ((bif b then 1 / 2 else 0) - 1 / 2) ((bif b then 1 / 2 else 0) - 1 / 2 + 1) := by
  obtain ⟨hs, -, ht₁, ht₂⟩ := mem_endWindow_iff.1 hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Prod.fst_add, mem_Ioi]; linarith
  · rw [Prod.snd_add, add_zero]; linarith
  · rw [Prod.snd_add, add_zero]; linarith

/-- **The translated end windows cover the end beyond `T + 1`.** Every point `(s, t)` with
`s > T + 1` is the translate by `(m, k)` of a point of an end window, for some `m ∈ ℕ` and
`k ∈ ℤ`. -/
theorem exists_sub_mem_endWindow {T s : ℝ} (hs : T + 1 < s) (t : ℝ) :
    ∃ (m : ℕ) (k : ℤ) (b : Bool), (s - m, t - k) ∈ endWindow T b := by
  -- Translate by the least natural number taking `s` to at most `T + 2`.
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, T + 1 < s - m ∧ s - m < T + 3 := by
    refine ⟨⌈s - (T + 2)⌉₊, ?_, by linarith [Nat.le_ceil (s - (T + 2))]⟩
    rcases le_or_gt (s - (T + 2)) 0 with h | h
    · rwa [Nat.ceil_eq_zero.2 h, Nat.cast_zero, sub_zero]
    · linarith [Nat.ceil_lt_add_one h.le]
  -- Shift the angular coordinate by an integer into one of the two windows.
  have hf₀ : 0 ≤ t - ⌊t⌋ := Int.self_sub_floor t ▸ Int.fract_nonneg t
  have hf₁ : t - ⌊t⌋ < 1 := Int.self_sub_floor t ▸ Int.fract_lt_one t
  by_cases h₁ : t - ⌊t⌋ < 2 / 5
  · exact ⟨m, ⌊t⌋, false, mem_endWindow_iff.2 ⟨hm₁, hm₂, by simp only [Bool.cond_false]; linarith,
      by simp only [Bool.cond_false]; linarith⟩⟩
  by_cases h₂ : t - ⌊t⌋ < 9 / 10
  · exact ⟨m, ⌊t⌋, true, mem_endWindow_iff.2 ⟨hm₁, hm₂, by simp only [Bool.cond_true]; linarith,
      by simp only [Bool.cond_true]; linarith⟩⟩
  · exact ⟨m, ⌊t⌋ + 1, false, mem_endWindow_iff.2 ⟨hm₁, hm₂,
      by push_cast; simp only [Bool.cond_false]; linarith,
      by push_cast; simp only [Bool.cond_false]; linarith⟩⟩

end TauCeti.Floer
