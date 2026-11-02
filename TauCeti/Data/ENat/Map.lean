/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Basic

/-!
# Comparing natural numbers with `ENat.map`

An element `k : ℕ∞` is often read in `WithTop α` through `ENat.map f` for a cast `f : ℕ → α`,
for example `ENat.map ((↑) : ℕ → ℝ)` reads a valuation with values in `ℕ∞` as one with values in
`WithTop ℝ`. These lemmas compare the image of a natural number `m` with `k.map f` by comparing
`m` with `k` in `ℕ∞`.

## Main results

* `ENat.coe_le_map_iff`: for strictly monotone `f`, `f m ≤ k.map f ↔ m ≤ k`.
* `ENat.coe_eq_map_iff`: for injective `f`, `f m = k.map f ↔ m = k`.
-/

public section

namespace ENat

variable {α : Type*} {f : ℕ → α} {m : ℕ} {k : ℕ∞}

/-- For a strictly monotone `f`, comparing `f m` with `k.map f` in `WithTop α` is comparing `m`
with `k` in `ℕ∞`. -/
theorem coe_le_map_iff [Preorder α] (hf : StrictMono f) :
    ((f m : α) : WithTop α) ≤ k.map f ↔ (m : ℕ∞) ≤ k := by
  induction k using ENat.recTopCoe <;> simp [hf.le_iff_le, ENat.natCast_le_natCast]

/-- For an injective `f`, `f m` equals `k.map f` in `WithTop α` exactly when `m` equals `k` in
`ℕ∞`. -/
theorem coe_eq_map_iff (hf : Function.Injective f) :
    ((f m : α) : WithTop α) = k.map f ↔ (m : ℕ∞) = k := by
  induction k using ENat.recTopCoe <;> simp [hf.eq_iff, ENat.natCast_inj]

end ENat
