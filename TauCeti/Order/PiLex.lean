/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex

/-!
# Comparisons on lexicographically ordered products

Mathlib equips `Lex (∀ i, β i)` with `<` defined via `Pi.Lex (· < ·) (· < ·)` wrapped in `id` to
prevent unwanted definitional reduction (`Mathlib.Order.PiLex`). This module provides explicit
iff characterizations `Pi.Lex.toLex_lt_toLex` and `Pi.Lex.toLex_le_toLex` relating `<` and `≤` on
`Lex (∀ i, β i)` to `Pi.Lex`, matching `Prod.Lex.toLex_lt_toLex` and `Prod.Lex.toLex_le_toLex`.

## Main results

* `Pi.Lex.toLex_lt_toLex`, `Pi.Lex.toLex_le_toLex`: explicit iff characterizations of
  `toLex x < toLex y` and `toLex x ≤ toLex y` in terms of `Pi.Lex`.
-/

public section

namespace Pi.Lex

variable {ι : Type*} {β : ι → Type*}

/-- Strict inequality on `Lex (∀ i, β i)` is `Pi.Lex (· < ·) (· < ·)`. -/
theorem toLex_lt_toLex [LT ι] [∀ i, LT (β i)] {x y : ∀ i, β i} :
    toLex x < toLex y ↔ Pi.Lex (· < ·) (· < ·) x y := (Iff.rfl)

/-- Nonstrict inequality on `Lex (∀ i, β i)` is equality or `Pi.Lex (· < ·) (· < ·)`. -/
theorem toLex_le_toLex [LinearOrder ι] [∀ i, PartialOrder (β i)] {x y : ∀ i, β i} :
    toLex x ≤ toLex y ↔ x = y ∨ Pi.Lex (· < ·) (· < ·) x y :=
  le_iff_eq_or_lt.trans (or_congr toLex_inj toLex_lt_toLex)

end Pi.Lex
