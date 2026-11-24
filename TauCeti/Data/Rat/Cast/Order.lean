/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Order properties of casts from `ℚ` into ordered fields

This module complements `Mathlib.Data.Rat.Cast.Order` by generalizing `Rat.cast_pos_of_pos` and
`Rat.cast_mono` from linearly ordered fields to partially ordered strictly ordered fields with
`PosMulReflectLT`.

In a linearly ordered field, the rational cast is monotone (`Rat.cast_mono`) and additive, so
it bundles as an order-preserving additive monoid homomorphism
`Rat.castOrderAddMonoidHom K : ℚ →+o K`. This lets APIs that change coefficients along a map
`K →+o L` move rational data to `K`, for example from `ℚ` to `ℝ`.

## Main results

* `Rat.cast_pos_of_partialOrder`: casting a positive rational into a partially ordered strictly
  ordered field with `PosMulReflectLT` preserves strict positivity.
* `Rat.cast_mono_of_partialOrder`: casting from `ℚ` into a partially ordered strictly ordered
  field with `PosMulReflectLT` is monotone.
* `Rat.castOrderAddMonoidHom`: the rational cast into a linearly ordered field, as an
  order-preserving additive monoid homomorphism.
-/

public section

namespace Rat

/-- Casting a positive rational into a partially ordered strictly ordered field with
`PosMulReflectLT` preserves strict positivity. -/
theorem cast_pos_of_partialOrder {K : Type*} [Field K] [PartialOrder K]
    [IsStrictOrderedRing K] [PosMulReflectLT K] {q : ℚ} (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.mpr hq).le
  have hn0 : 0 < n := Int.natCast_pos.mp (hn ▸ Rat.num_pos.mpr hq)
  rw [hn, Int.cast_natCast]
  exact div_pos (Nat.cast_pos.mpr hn0) (Nat.cast_pos.mpr q.pos)

/-- Casting from `ℚ` into a partially ordered strictly ordered field with `PosMulReflectLT` is
monotone. -/
theorem cast_mono_of_partialOrder {K : Type*} [Field K] [PartialOrder K]
    [IsStrictOrderedRing K] [PosMulReflectLT K] : Monotone ((↑) : ℚ → K) := by
  intro p q hpq
  rcases hpq.eq_or_lt with rfl | hlt
  · rfl
  · have hpos : (0 : K) < ((q - p : ℚ) : K) := cast_pos_of_partialOrder (sub_pos.mpr hlt)
    rw [Rat.cast_sub, sub_pos] at hpos
    exact hpos.le

section LinearOrder

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The rational cast into a linearly ordered field, as an order-preserving additive monoid
homomorphism. -/
def castOrderAddMonoidHom : ℚ →+o K :=
  .mk' Rat.cast cast_mono cast_add

@[simp]
theorem coe_castOrderAddMonoidHom : ⇑(castOrderAddMonoidHom K) = Rat.cast :=
  (rfl)

end LinearOrder

end Rat
