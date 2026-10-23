/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Cup
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.NumberTheory.HilbertSymbol.Archimedean

/-!
# Kummer cup products over `ℝ`

The absolute Galois group of `ℝ` is `Gal(ℂ/ℝ)`, a group of order two. This file computes the
mod-two Kummer cup pairing

```text
ℝˣ/(ℝˣ)² × ℝˣ/(ℝˣ)² → H²(G_ℝ, 𝔽₂),   ([a], [b]) ↦ [a] ⌣ [b]
```

completely. By the cup-norm theorem, `[a] ⌣ [b]` vanishes exactly when `b = x² - a y²` is
solvable in `ℝ`, which happens unless both `a` and `b` are negative. In particular
`[-1] ⌣ [-1] ≠ 0`, since `-1` is not a sum of two real squares, that is, not a norm from `ℂ`.
This is the Galois form of the nonvanishing of the cup square of the nontrivial class of
`H¹(C₂, 𝔽₂)`, and the smallest example of a Kummer cup detecting a non-norm.

Since the real square-class group has only the classes `0` and `[-1]`, the pairing is
nondegenerate: `x ⌣ y = 0` exactly when `x = 0` or `y = 0`.

## Main results

* `TauCeti.cup_kummerClass_eq_zero_iff_real`: `(a) ∪ (b) = 0` over `ℝ` if and only if `a > 0` or
  `b > 0`.
* `TauCeti.cup_kummerClass_neg_one_neg_one_ne_zero_real`: `(-1) ∪ (-1) ≠ 0` in `H²(G_ℝ, 𝔽₂)`.
* `TauCeti.kummerCup_squareClass_real`: the full real cup table; `[a] ⌣ [b]` is
  `[-1] ⌣ [-1]` when `a` and `b` are both negative and `0` otherwise.
* `TauCeti.kummerCup_eq_zero_iff_real`: the real Kummer cup pairing is nondegenerate.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.1, for the real Hilbert symbol.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.2), for the Kummer cup pairing.
-/

public section

noncomputable section

namespace TauCeti

/-- Over `ℝ`, the cup `(a) ∪ (b)` of two Kummer classes vanishes if and only if `a` or `b` is
positive. -/
@[simp]
theorem cup_kummerClass_eq_zero_iff_real (a b : ℝˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℝ)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      0 < (a : ℝ) ∨ 0 < (b : ℝ) :=
  (cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one a b).trans (hilbertSymbol_real_eq_one_iff a b)

/-- **`(-1) ∪ (-1) ≠ 0` over `ℝ`.** The cup square of the Kummer class of `-1` is nonzero in
`H²(G_ℝ, 𝔽₂)`, because `-1` is not a sum of two real squares. -/
theorem cup_kummerClass_neg_one_neg_one_ne_zero_real :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℝ)).cup 1 1
      (kummerClass (-1 : ℝˣ)) (kummerClass (-1 : ℝˣ)) ≠ 0 := by
  rw [Ne, cup_kummerClass_eq_zero_iff_real]
  norm_num

/-- **The real Kummer cup table.** The cup `[a] ⌣ [b]` is the nonzero class `[-1] ⌣ [-1]` when
`a` and `b` are both negative, and vanishes otherwise. -/
theorem kummerCup_squareClass_real (a b : ℝˣ) :
    kummerCup ℝ (squareClass a) (squareClass b) =
      if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then
        kummerCup ℝ (squareClass (-1 : ℝˣ)) (squareClass (-1 : ℝˣ))
      else 0 := by
  split_ifs with h
  · rw [(Units.squareClass_eq_squareClass_neg_one_iff_neg a).2 h.1,
      (Units.squareClass_eq_squareClass_neg_one_iff_neg b).2 h.2]
  · rw [kummerCup_squareClass_squareClass, cup_kummerClass_eq_zero_iff_real]
    grind [a.ne_zero, b.ne_zero]

/-- **The real Kummer cup pairing is nondegenerate**: `x ⌣ y = 0` exactly when one of the
square classes `x`, `y` is trivial. -/
theorem kummerCup_eq_zero_iff_real (x y : SquareClassGroup ℝ) :
    kummerCup ℝ x y = 0 ↔ x = 0 ∨ y = 0 := by
  rw [← squareClass_toMul_out x, ← squareClass_toMul_out y,
    kummerCup_squareClass_squareClass, cup_kummerClass_eq_zero_iff_real,
    Units.squareClass_eq_zero_iff_pos, Units.squareClass_eq_zero_iff_pos]

end TauCeti
