/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The `n`-th power classes of an algebraically closed field

For `n ≠ 0`, every unit of an algebraically closed field `F` is an `n`-th power, so the quotient
`Fˣ ⧸ (Fˣ)ⁿ` is trivial. This is the local count at a complex place of a number field.

## Main results

* `TauCeti.card_powerClasses_of_isAlgClosed`: `#(Fˣ ⧸ (Fˣ)ⁿ) = 1` for `n ≠ 0`.
-/

public section

namespace TauCeti

/-- **The `n`-th power classes of an algebraically closed field.** For `n ≠ 0`, every unit of an
algebraically closed field is an `n`-th power, so `Fˣ ⧸ (Fˣ)ⁿ` is trivial. -/
theorem card_powerClasses_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] {n : ℕ}
    (hn : n ≠ 0) : Nat.card (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range) = 1 := by
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) (Nat.pos_of_ne_zero hn)
  exact ⟨Units.mk0 y <| (pow_ne_zero_iff hn).1 <| hy ▸ x.ne_zero, Units.ext hy⟩

end TauCeti
