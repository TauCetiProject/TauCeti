/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Deduction terms and geometric summability for indexed Young diagrams

Given a family of Young diagrams `κ : Φ → ℕ → ℕ` (recording `κ τ h` columns of height `h` at each
index `τ : Φ`), a height cutoff `N`, a set `marked : Finset Φ` of marked indices, and a real base
`b`, we define the height-one column count, the low-column count, the low-box count, height-one
erasure (`eraseHeightOne`), and the per-pair deduction term (`deductionTerm`).

## Main definitions and results

* `TauCeti.YoungDeduction.heightOneColumns`, `lowColumnCount`, `lowBoxCount`: column and box
  counts below height `N`.
* `TauCeti.YoungDeduction.eraseHeightOne`: removes height-one columns at marked indices.
* `TauCeti.YoungDeduction.deductionTerm`: the per-pair deduction term at exponent `e`.
* `TauCeti.YoungDeduction.deductionTerm_eraseHeightOne`: marking `marked` equals erasing
  height-one columns on `marked` with empty marked set.
* `TauCeti.YoungDeduction.boxes_eq_sum`: decomposes total low-height boxes into height-one columns
  and low-column boxes.
* `TauCeti.YoungDeduction.deductionTerm_nonneg`: nonnegativity for `0 ≤ b`.
* `TauCeti.YoungDeduction.summable_sum_deductionTerm`: geometric summability in `e` for `1 < b`.

## Provenance

Adapted from `New.heightOneColumns`, `New.lowColumnCount`, `New.lowBoxCount`,
`New.eraseHeightOne`, `New.deductionTerm_eraseHeightOne`, `New.boxes_eq_sum`, and
`New.summable_deductionAt` in `src/New/Derivatives/Divisibility/Count.lean` and
`New.deductionTerm` in `src/New/Derivatives/Divisibility/NullFrames.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti.YoungDeduction

open Finset

section Definitions

variable {Φ : Type*} (κ : Φ → ℕ → ℕ) (N : ℕ)

/-- The number of columns of height `1` at `τ` among heights below `N`. -/
def heightOneColumns (τ : Φ) : ℕ :=
  ∑ h ∈ range N, if h = 1 then κ τ h else 0

/-- The number of columns of height other than `1` at `τ` among heights below `N`. -/
def lowColumnCount (τ : Φ) : ℕ :=
  ∑ h ∈ range N, if h = 1 then 0 else κ τ h

/-- The number of boxes in columns of height other than `1` at `τ` among heights below `N`. -/
def lowBoxCount (τ : Φ) : ℕ :=
  ∑ h ∈ range N, h * if h = 1 then 0 else κ τ h

/-- The diagram family `κ` with its height-one columns erased at all indices in `marked`. -/
def eraseHeightOne [DecidableEq Φ] (marked : Finset Φ) (τ : Φ) (h : ℕ) : ℕ :=
  if h = 1 ∧ τ ∈ marked then 0 else κ τ h

/-- The per-pair deduction term at base `b`, cutoff `N`, marked set `marked`, pair `(τ, τ')`,
and exponent `e`. -/
noncomputable def deductionTerm [DecidableEq Φ] (b : ℝ) (marked : Finset Φ) (τ τ' : Φ)
    (e : ℕ) : ℝ :=
  let oneCols (σ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 ∧ σ ∉ marked then κ σ h else 0
  let neOneCols (σ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 then 0 else κ σ h
  let neOneBoxes (σ : Φ) : ℕ := ∑ h ∈ range N, h * if h = 1 then 0 else κ σ h
  min (oneCols τ / b ^ e : ℝ) (neOneCols τ' + oneCols τ') + neOneCols τ / b ^ e +
    min (neOneBoxes τ / b ^ e : ℝ) (neOneBoxes τ')

end Definitions

section Theorems

variable {Φ : Type*} (κ : Φ → ℕ → ℕ) (N : ℕ)

/-- Marking the indices of `marked` has the same effect on `deductionTerm` as erasing their
columns of height one and taking the empty marked set. -/
theorem deductionTerm_eraseHeightOne [DecidableEq Φ] (b : ℝ) (marked : Finset Φ) (τ τ' : Φ)
    (e : ℕ) :
    deductionTerm (eraseHeightOne κ marked) N b ∅ τ τ' e =
      deductionTerm κ N b marked τ τ' e := by
  have h_one (σ : Φ) (h : ℕ) :
      (if h = 1 ∧ σ ∉ (∅ : Finset Φ) then eraseHeightOne κ marked σ h else 0) =
        if h = 1 ∧ σ ∉ marked then κ σ h else 0 := by
    by_cases h1 : h = 1 <;> by_cases hσ : σ ∈ marked <;> simp [eraseHeightOne, h1, hσ]
  have h_low (σ : Φ) (h : ℕ) :
      (if h = 1 then 0 else eraseHeightOne κ marked σ h) = if h = 1 then 0 else κ σ h := by
    by_cases h1 : h = 1 <;> simp [eraseHeightOne, h1]
  simp only [deductionTerm, h_one, h_low]

/-- The total number of boxes in columns of height below `N` decomposes as the sum of height-one
columns and low-column boxes. -/
theorem boxes_eq_sum [Fintype Φ] :
    (∑ τ : Φ, ∑ h ∈ range N, h * κ τ h : ℝ) =
      ∑ τ : Φ, (heightOneColumns κ N τ + lowBoxCount κ N τ : ℝ) := by
  have h_split (τ : Φ) (h : ℕ) :
      h * κ τ h = (if h = 1 then κ τ h else 0) + h * if h = 1 then 0 else κ τ h := by
    by_cases h1 : h = 1 <;> simp [h1]
  simp only [heightOneColumns, lowBoxCount, ← Nat.cast_add, ← Nat.cast_sum, ← Nat.cast_mul,
    ← sum_add_distrib, ← h_split]

/-- The deduction term is nonnegative whenever `0 ≤ b`. -/
theorem deductionTerm_nonneg [DecidableEq Φ] {b : ℝ} (hb : 0 ≤ b) (marked : Finset Φ)
    (τ τ' : Φ) (e : ℕ) :
    0 ≤ deductionTerm κ N b marked τ τ' e := by
  simp only [deductionTerm]
  positivity

/-- For any base `1 < b`, any partner map `pr : ℕ → Φ → Φ`, and any exponent predicate
`P : ℕ → Prop`, the filtered per-exponent sum of deduction terms is summable over `e : ℕ`. -/
theorem summable_sum_deductionTerm [Fintype Φ] [DecidableEq Φ] {b : ℝ} (hb : 1 < b)
    (P : ℕ → Prop) [DecidablePred P] (pr : ℕ → Φ → Φ) (marked : Finset Φ) :
    Summable fun e : ℕ ↦ if P e then ∑ τ : Φ, deductionTerm κ N b marked τ (pr e τ) e else 0 := by
  let c : ℝ := ∑ τ : Φ,
    (heightOneColumns κ N τ + lowColumnCount κ N τ + lowBoxCount κ N τ : ℝ)
  refine ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb)).mul_left c
    ).of_nonneg_of_le (fun e ↦ ?_) fun e ↦ ?_
  · split_ifs
    · exact sum_nonneg fun τ _ ↦ deductionTerm_nonneg κ N (by linarith) marked τ (pr e τ) e
    · exact le_rfl
  · split_ifs
    · rw [inv_pow, ← div_eq_mul_inv, sum_div]
      refine sum_le_sum fun τ _ ↦ ?_
      have h_one_le :
          (∑ h ∈ range N, if h = 1 ∧ τ ∉ marked then κ τ h else 0) ≤ heightOneColumns κ N τ :=
        sum_le_sum fun h _ ↦ by by_cases h1 : h = 1 <;> by_cases hτ : τ ∈ marked <;> simp [h1, hτ]
      simp only [deductionTerm, lowColumnCount, lowBoxCount, add_div]
      gcongr
      · exact (min_le_left _ _).trans (by gcongr)
      · exact min_le_left _ _
    · positivity

end Theorems

end TauCeti.YoungDeduction
