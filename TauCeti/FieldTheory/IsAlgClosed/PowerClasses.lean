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
  suffices h : (powMonoidHom n : Fˣ →* Fˣ).range = ⊤ by
    rw [← Subgroup.index_eq_card, h, Subgroup.index_top]
  refine MonoidHom.range_eq_top.2 fun x ↦ ?_
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) (Nat.pos_of_ne_zero hn)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by simpa [zero_pow hn] using hy.symm)
  exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

end TauCeti
