/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Squares of the form `1 + 4c` in a valuation ring

In a valuation ring `R` in which `2 ≠ 0`, the element `1 + 4c` is a square exactly when `c` has
the form `t ^ 2 + t`, the witness being `1 + 2t`. One direction is an identity valid in every
commutative ring. The other says that every square root `y` of `1 + 4c` satisfies `2 ∣ y - 1`,
which uses that divisibility in `R` is total.

Over the integer ring of a dyadic local field this reduces the question whether a unit of depth
`2 v(2)` is a square to the residue field, where `t ↦ t ^ 2 + t` is the Artin–Schreier map. This
is how the depth of the local square theorem is shown to be sharp.

## Main results

* `TauCeti.ValuationRing.isSquare_one_add_four_mul_iff`: `1 + 4c` is a square if and only if
  `c = t ^ 2 + t` for some `t`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

namespace ValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- In a valuation ring in which `2 ≠ 0`, the element `1 + 4c` is a square if and only if `c`
lies in the image of the quadratic map `t ↦ t ^ 2 + t`. -/
theorem isSquare_one_add_four_mul_iff (h2 : (2 : R) ≠ 0) {c : R} :
    IsSquare (1 + 4 * c) ↔ ∃ t, t ^ 2 + t = c := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨t, ht⟩ ↦ ⟨1 + 2 * t, by rw [← ht]; ring⟩⟩
  -- Write `y = 1 + z`, so that `z ^ 2 + 2 * z = 4 * c`. The point is that `2 ∣ z`.
  obtain ⟨t, ht⟩ : 2 ∣ y - 1 := by
    rcases _root_.ValuationRing.dvd_total 2 (y - 1) with h | ⟨w, hw⟩
    · exact h
    -- Otherwise `2 = z * w`, and cancelling `z ^ 2` from `z ^ 2 * (1 + w) = z ^ 2 * w ^ 2 * c`
    -- shows that `w` is a unit.
    have hz : y - 1 ≠ 0 := fun h ↦ h2 (by simpa [h] using hw)
    have hw' : 1 + w = w * w * c := mul_left_cancel₀ (mul_ne_zero hz hz) <| by
      linear_combination -hy - (y - 1 - ((y - 1) * w + 2) * c) * hw
    have hu : IsUnit w := IsUnit.of_mul_eq_one (w * c - 1) (by linear_combination -hw')
    exact ⟨↑hu.unit⁻¹, by rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  refine ⟨t, mul_left_cancel₀ (mul_ne_zero h2 h2) ?_⟩
  rw [sub_eq_iff_eq_add] at ht
  rw [ht] at hy
  linear_combination -hy

end ValuationRing

end TauCeti
