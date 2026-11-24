/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RingTheory.DennisStein.Basic

/-!
# A detector on the Dennis–Stein group of `ℤ/4`

Over `ℤ/4` a pair `(r, s)` is admissible exactly when `r * s` is even. The function `λ` on pairs
with values in `ℤ/2` given by `λ(2, 2) = λ(2, 3) = λ(3, 2) = 1` and `λ = 0` on all other pairs
satisfies the Dennis–Stein relations D1–D3 on admissible pairs, a finite check. It therefore
induces an additive map `D(ℤ/4) →+ ℤ/2`, which detects the symbol `⟨3, 2⟩`.

Consequently `D(ℤ/4)` is not zero, and the reduction map `D(ℤ/4) → D(ℤ/2)` is not injective:
it sends `⟨3, 2⟩` to `⟨1, 0⟩ = 0`. In the lift-change sequence for `ℤ/4 → ℤ/2`, whose kernel
`(2)` is the maximal ideal of the local ring `ℤ/4`, the image of the relative group is therefore
nonzero. Through the local Dennis–Stein presentation, `⟨3, 2⟩` is the symbol `{-1, -1}`
generating `K₂(ℤ/4) ≅ ℤ/2`.

## Main definitions and results

* `TauCeti.DennisSteinGroup.zmodFourDetector`: the map `D(ℤ/4) →+ ℤ/2` induced by `λ`.
* `TauCeti.DennisSteinGroup.symbol_three_two_ne_zero`: `⟨3, 2⟩ ≠ 0` in `D(ℤ/4)`.
* `TauCeti.DennisSteinGroup.ker_map_zmodFour_zmodTwo_ne_bot`: the reduction map
  `D(ℤ/4) → D(ℤ/2)` has nonzero kernel.

## References

* C. A. Weibel, *The K-book*, Graduate Studies in Mathematics 145, AMS (2013), Exercise III.5.13.
-/

public section

namespace TauCeti

namespace DennisSteinGroup

/-- In `ℤ/4` the units are exactly the elements squaring to `1`, which makes admissibility a
decidable condition. -/
private theorem isUnit_iff_mul_self_eq_one (x : ZMod 4) : IsUnit x ↔ x * x = 1 := by
  refine ⟨?_, fun h => IsUnit.of_mul_eq_one x h⟩
  rintro ⟨u, rfl⟩
  revert u
  decide

/-- The detector table on `ℤ/4`: `1` at `(2, 2)`, `(2, 3)` and `(3, 2)`, and `0` elsewhere. -/
private def zmodFourTable (r s : ZMod 4) : ZMod 2 :=
  if (r = 2 ∧ s = 2) ∨ (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) then 1 else 0

/-- The map `D(ℤ/4) →+ ℤ/2` sending `⟨2, 2⟩`, `⟨2, 3⟩` and `⟨3, 2⟩` to `1` and every other
admissible symbol to `0`. -/
noncomputable def zmodFourDetector : DennisSteinGroup (ZMod 4) →+ ZMod 2 :=
  lift zmodFourTable
    (by simp_rw [isUnit_iff_mul_self_eq_one]; decide)
    (by simp_rw [isUnit_iff_mul_self_eq_one]; decide)
    (by simp_rw [isUnit_iff_mul_self_eq_one]; decide)

/-- The detector takes the value `1` on `⟨2, 2⟩`. -/
@[simp]
theorem zmodFourDetector_symbol_two_two : zmodFourDetector (symbol (2 : ZMod 4) 2) = 1 := by
  rw [zmodFourDetector, lift_symbol _ _ _ _ (by rw [isUnit_iff_mul_self_eq_one]; decide)]
  decide

/-- The detector takes the value `1` on `⟨2, 3⟩`. -/
@[simp]
theorem zmodFourDetector_symbol_two_three : zmodFourDetector (symbol (2 : ZMod 4) 3) = 1 := by
  rw [zmodFourDetector, lift_symbol _ _ _ _ (by rw [isUnit_iff_mul_self_eq_one]; decide)]
  decide

/-- The detector takes the value `1` on `⟨3, 2⟩`. -/
@[simp]
theorem zmodFourDetector_symbol_three_two : zmodFourDetector (symbol (3 : ZMod 4) 2) = 1 := by
  rw [zmodFourDetector, lift_symbol _ _ _ _ (by rw [isUnit_iff_mul_self_eq_one]; decide)]
  decide

/-- The symbol `⟨3, 2⟩` is nonzero in `D(ℤ/4)`; in particular `D(ℤ/4)` is not trivial. -/
theorem symbol_three_two_ne_zero : symbol (3 : ZMod 4) 2 ≠ 0 := fun h => by
  simpa [h] using zmodFourDetector_symbol_three_two

/-- The reduction `ℤ/4 → ℤ/2` induces a map `D(ℤ/4) → D(ℤ/2)` with nonzero kernel: it kills
`⟨3, 2⟩`, whose image is `⟨1, 0⟩`. -/
theorem ker_map_zmodFour_zmodTwo_ne_bot :
    (map (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2))).ker ≠ ⊥ := by
  intro h
  refine symbol_three_two_ne_zero ((AddMonoidHom.ker_eq_bot_iff _).1 h ?_)
  rw [map_symbol _ (by rw [isUnit_iff_mul_self_eq_one]; decide), map_zero]
  have h₂ : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) 2 = 0 := by decide
  rw [h₂, symbol_zero_right]

end DennisSteinGroup

end TauCeti
