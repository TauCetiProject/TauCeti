/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The invariant of an elliptic net

For an arbitrary sequence `W : ℤ → R`, this file defines the candidate numerator and denominator
of its invariant:

* `IsEllipticNet.invarNum W s n
    = (W (n + 2s) * W (n - s)² + W (n + s)² * W (n - 2s)) * W s² + W n³ * W (2s)²`;
* `IsEllipticNet.invarDenom W s n = W (n + s) * W n * W (n - s)`.

The numerator needs only an addition and a multiplicative monoid; the denominator needs only a
multiplication. Both commute with maps preserving the operations in their formulas, without any
requirement that the maps preserve `1`.

If `R` is a commutative ring and `W` is an elliptic net,
`IsEllipticNet.invarNum_mul_invarDenom` proves the cross-multiplication identity

`invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`.

Over a field, this implies that the ratio is constant wherever the denominator is nonzero.
The cross-multiplied form also applies when denominators vanish or are zero divisors. It supplies
the invariant identity used in the division-polynomial theory of Weierstrass curves.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `invarNum`, `invarDenom` and `invar_of_net`. That file credits David Kurniadi Angdinata
as its author. J. Xu is acknowledged for the surrounding LutzNagell development, including
`Universal.lean` and `DivisionPolynomialOmega.lean` at that revision.

The same declarations appear in Mathlib PR #13057. The name `invarNum_mul_invarDenom` follows its
sibling PR #13155. The proof is adapted to the current elliptic-net API: the source's `net`,
`addMulSub` and `rel₄` are now `IsEllipticNet.rel`, `IsEllipticNet.atom` and
`IsEllipticNet.atomRel`. The formulas themselves are unchanged.
-/

public section

namespace IsEllipticNet

variable {R S : Type*}

section Numerator

variable [Add R] [Monoid R] (W : ℤ → R)

/-- The candidate numerator of the invariant of an arbitrary sequence. For an elliptic net over a
commutative ring, it satisfies `invarNum_mul_invarDenom`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The defining formula for `invarNum`. -/
@[simp]
theorem invarNum_def (s n : ℤ) : invarNum W s n =
    (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
      + W n ^ 3 * W (2 * s) ^ 2 := (rfl)

/-- The numerator commutes with maps preserving addition and multiplication.

Since only positive powers occur, preservation of `1` is unnecessary. The named lemma permits
rewriting without expanding the formula. -/
theorem map_invarNum [Add S] [Monoid S] {F : Type*} [FunLike F R S]
    [AddHomClass F R S] [MulHomClass F R S] (f : F) (s n : ℤ) :
    f (invarNum W s n) = invarNum (f ∘ W) s n := by
  simp only [invarNum, sq, pow_three, map_add, map_mul, Function.comp_apply]

end Numerator

section Denominator

variable [Mul R] (W : ℤ → R)

/-- The denominator of the invariant of an elliptic net, `W (n + s) * W n * W (n - s)`. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

/-- The defining formula for `invarDenom`. -/
@[simp]
theorem invarDenom_def (s n : ℤ) : invarDenom W s n = W (n + s) * W n * W (n - s) := (rfl)

/-- The denominator commutes with maps preserving multiplication.

This lemma is useful for rewriting without expanding the formula; `simp` can instead use
`invarDenom_def` and `map_mul`. -/
theorem map_invarDenom [Mul S] {F : Type*} [FunLike F R S] [MulHomClass F R S]
    (f : F) (s n : ℤ) :
    f (invarDenom W s n) = invarDenom (f ∘ W) s n := by
  simp only [invarDenom, map_mul, Function.comp_apply]

end Denominator

section CommRing

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- `invarNum` and `invarDenom` cross-multiply symmetrically in `m` and `n` as soon as the elliptic
relator vanishes at these four arguments. -/
private theorem invarNum_mul_invarDenom_of_rel {s m n : ℤ}
    (h₀ : rel W m n s 0 = 0) (h₁ : rel W m n s s = 0)
    (h₂ : rel W (m - s) (n - s) s s = 0) (h₃ : rel W (n + s) n (n - s) (m - n) = 0) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [rel]; ring_nf))
    h₀ * W m * W n * W (2 * s) ^ 2
      - (h₁ * W (m - s) * W (n - s)
        + h₂ * W (m + s) * W (n + s)
        - h₃ * W (m - n) * W (2 * s)) * W s ^ 2

/-- **The invariance identity for an elliptic net**: `invarNum` and `invarDenom` cross-multiply
symmetrically in the two indices.

Over a field, when both `invarDenom W s m` and `invarDenom W s n` are nonzero, this implies
equality of the two ratios. Over a general commutative ring a denominator may vanish or be a zero
divisor. -/
theorem invarNum_mul_invarDenom (h : IsEllipticNet W) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invarNum_mul_invarDenom_of_rel (h ..) (h ..) (h ..) (h ..)

end CommRing

end IsEllipticNet
