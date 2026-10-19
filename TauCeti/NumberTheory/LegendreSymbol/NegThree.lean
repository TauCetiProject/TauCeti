/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The Legendre symbol `(-3 | p)`

For an odd prime `p`, the supplementary law `(-1 | p) = (-1) ^ ((p - 1) / 2)` and quadratic
reciprocity `(3 | p) = (-1) ^ ((p - 1) / 2) (p | 3)` combine to `(-3 | p) = (p | 3)`. So whether
`-3` is a square modulo `p` depends only on `p` modulo `3`, alongside Mathlib's supplementary laws
`legendreSym.at_neg_one`, `legendreSym.at_two` and `legendreSym.at_neg_two`. The identity also
holds at `p = 3`, where both sides vanish, but not at `p = 2`, where `(-3 | 2) = 1` and
`(2 | 3) = -1`.

## Main results

* `TauCeti.legendreSym.at_neg_three`: `legendreSym p (-3) = legendreSym 3 p` for `p ≠ 2`.
-/

public section

namespace TauCeti

/-- **The Legendre symbol `(-3 | p)`.** For an odd prime `p`, `(-3 | p) = (p | 3)`. -/
theorem legendreSym.at_neg_three {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-3) = legendreSym 3 p := by
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  have hrec := _root_.legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by norm_num) hp
  push_cast at hrec
  rw [show (-3 : ℤ) = -1 * 3 by norm_num, _root_.legendreSym.mul,
    _root_.legendreSym.at_neg_one hp, hrec, ZMod.χ₄_eq_neg_one_pow hodd, ← mul_assoc, ← pow_add]
  norm_num [← two_mul, pow_mul]

/-! At `p = 2` the identity fails. -/

example : legendreSym 2 (-3) = 1 ∧ legendreSym 3 2 = -1 := by
  refine ⟨?_, ?_⟩
  · rw [legendreSym.mod]
    norm_num
  · rw [legendreSym.at_two (by norm_num)]
    rfl

end TauCeti
