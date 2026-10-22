/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Interval

/-!
# Integer intervals bounded by a natural floor

The symmetric integer interval `[-⌊B⌋₊, ⌊B⌋₊]` has `2 * ⌊B⌋₊ + 1` elements, whose casts
remain distinct in characteristic zero. For `B ≥ 0`, every element has absolute value at most
`B`. These bounds describe the size and extent of finite integer grids.
-/

public section

namespace TauCeti

variable {K : Type*} [Semiring K] [LinearOrder K] [FloorSemiring K]

/-- The integer grid `[-⌊B⌋₊, ⌊B⌋₊]` has `2 * ⌊B⌋₊ + 1` distinct images in any
characteristic-zero additive group with one. -/
theorem card_intCast_Icc_floor {R : Type*} [AddGroupWithOne R] [CharZero R] (B : K) :
    ((Finset.Icc (-(⌊B⌋₊ : ℤ)) (⌊B⌋₊ : ℤ)).map
      ⟨(Int.cast : ℤ → R), Int.cast_injective⟩).card = 2 * ⌊B⌋₊ + 1 := by
  rw [Finset.card_map, Int.card_Icc]
  omega

/-- Every integer in `[-⌊B⌋₊, ⌊B⌋₊]` has absolute value at most the nonnegative bound `B`. -/
theorem natAbs_le_of_mem_Icc_floor {B : K} (hB : 0 ≤ B) {z : ℤ}
    (hz : z ∈ Finset.Icc (-(⌊B⌋₊ : ℤ)) (⌊B⌋₊ : ℤ)) : (z.natAbs : K) ≤ B := by
  obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.1 hz
  exact (FloorSemiring.natCast_le_iff.2 (by omega : z.natAbs ≤ ⌊B⌋₊)).trans (Nat.floor_le hB)

end TauCeti
