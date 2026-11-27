/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Beth numbers: cofinality and iterated exponentials

The beth function `o ↦ ℶ_ o` is normal (`Cardinal.isNormal_beth`), and so is its composite with
`Cardinal.ord`. A normal function preserves the cofinality of limit ordinals, so at a limit
ordinal `o` the cofinality of `ℶ_ o` is that of `o`. In particular, indexing by the initial
ordinal of a regular cardinal `c` produces a strong limit cardinal `ℶ_ c.ord` of cofinality
exactly `c`; this is the standard way of producing strong limit cardinals of prescribed
cofinality, which is what size-bounding arguments with cutoff cardinals need.

The iterated exponential `ℶₙ(κ)`, with `ℶ₀(κ) = κ` and `ℶₙ₊₁(κ) = 2 ^ ℶₙ(κ)`, generalises the
finite steps of the beth function: `ℶₙ(ℶ_ o) = ℶ_ (o + n)`.

## Main definitions

* `Cardinal.iteratedTwoPow κ n`: the iterated exponential `ℶₙ(κ)`.

## Main results

* `Cardinal.isNormal_ord_beth`: `o ↦ (ℶ_ o).ord` is a normal function.
* `Cardinal.cof_ord_beth`: at a limit ordinal `o`, `(ℶ_ o).ord.cof = o.cof`.
* `Cardinal.IsRegular.cof_ord_beth_ord`: for a regular cardinal `c`, `(ℶ_ c.ord).ord.cof = c`.
* `Cardinal.isStrongLimit_beth_ord`: for an infinite cardinal `c`, `ℶ_ c.ord` is a strong limit.
* `Cardinal.le_iteratedTwoPow`: `κ ≤ ℶₙ(κ)`.
* `Cardinal.iteratedTwoPow_beth`: `ℶₙ(ℶ_ o) = ℶ_ (o + n)`.
-/

public section

universe u

open Ordinal Order

namespace Cardinal

/-- The ordinal-valued beth function `o ↦ (ℶ_ o).ord` is normal. -/
theorem isNormal_ord_beth : IsNormal fun o : Ordinal.{u} ↦ (ℶ_ o).ord :=
  isNormal_ord.comp isNormal_beth

/-- At a limit ordinal `o`, the beth number `ℶ_ o` has the same cofinality as `o`. -/
theorem cof_ord_beth {o : Ordinal.{u}} (ho : IsSuccLimit o) : (ℶ_ o).ord.cof = o.cof :=
  cof_map_of_isNormal isNormal_ord_beth ho

/-- For a regular cardinal `c`, the beth number indexed by the initial ordinal of `c` has
cofinality exactly `c`. -/
theorem IsRegular.cof_ord_beth_ord {c : Cardinal.{u}} (hc : c.IsRegular) :
    (ℶ_ c.ord).ord.cof = c := by
  rw [cof_ord_beth (isSuccLimit_ord hc.aleph0_le), hc.cof_ord]

/-- For an infinite cardinal `c`, the beth number indexed by the initial ordinal of `c` is a strong
limit cardinal. -/
theorem isStrongLimit_beth_ord {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) : IsStrongLimit (ℶ_ c.ord) :=
  isStrongLimit_beth.2 (isSuccLimit_ord hc).isSuccPrelimit

/-- The iterated exponential `ℶₙ(κ)`: `ℶ₀(κ) = κ` and `ℶₙ₊₁(κ) = 2 ^ ℶₙ(κ)`. -/
noncomputable def iteratedTwoPow (κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => κ
  | n + 1 => 2 ^ iteratedTwoPow κ n

@[simp]
theorem iteratedTwoPow_zero (κ : Cardinal.{u}) : iteratedTwoPow κ 0 = κ :=
  (rfl)

@[simp]
theorem iteratedTwoPow_succ (κ : Cardinal.{u}) (n : ℕ) :
    iteratedTwoPow κ (n + 1) = 2 ^ iteratedTwoPow κ n :=
  (rfl)

/-- The iterated exponential `ℶₙ(κ)` is at least `κ`. -/
theorem le_iteratedTwoPow (κ : Cardinal.{u}) (n : ℕ) : κ ≤ iteratedTwoPow κ n := by
  induction n with
  | zero => simp
  | succ n ih => exact ih.trans (by simpa using (cantor _).le)

/-- Iterating the exponential `n` times from `ℶ_ o` gives `ℶ_ (o + n)`. -/
theorem iteratedTwoPow_beth (o : Ordinal.{u}) (n : ℕ) : iteratedTwoPow (ℶ_ o) n = ℶ_ (o + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedTwoPow_succ, ih, Nat.cast_succ, ← add_assoc, beth_add_one]

end Cardinal
