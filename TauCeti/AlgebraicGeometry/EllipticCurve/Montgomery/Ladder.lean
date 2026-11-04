/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.DiffAdd

/-!
# The odd step of the Montgomery ladder

Adjacent multiples `[k + 1]P` and `[k]P` have difference `P` and sum `[2k + 1]P`.
Consequently differential addition of representatives of their coordinate pairs, using a
representative of `P` as the difference, computes the odd multiple `[2k + 1]P`.
`diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero` proves the cross-difference relation
for arbitrary representatives, with no characteristic restriction. Over a field with `2 ≠ 0`,
`diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero` gives the exact exceptional set for nonzero
representatives: the output is nonzero if and only if `P` is neither infinity nor the
distinguished point of order two. In particular the exceptional set does not depend on `k`.
Both results assume `B ≠ 0`; no ellipticity assumption is needed.

For the distinguished point of order two, `coordinates_nsmul_twoTorsionPoint` records the
alternation between infinity and `(0, 0)` on the curve. The differential-addition step is
always the zero raw pair, even though the odd multiple is the nonzero point `(0, 0)`.
The zero raw pair must therefore not be interpreted as a projective coordinate.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261: the binary ladder relations.
-/

public section

namespace TauCeti.Montgomery

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

/-- For `B ≠ 0`, the odd Montgomery-ladder step on arbitrary representatives has vanishing
cross difference with `[2k + 1]P`, including in characteristic two and at exceptional points. -/
theorem diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (k : ℕ) {SNext SCurrent SBase : Pair K}
    (hNextCross : SNext.cross (coordinates A B ((k + 1) • P)) = 0)
    (hCurrentCross : SCurrent.cross (coordinates A B (k • P)) = 0)
    (hBaseCross : SBase.cross (coordinates A B P) = 0) :
    (diffAdd SNext SCurrent SBase).cross (coordinates A B ((2 * k + 1) • P)) = 0 := by
  have hsub : (k + 1) • P - k • P = P := by simp [add_nsmul, add_comm]
  have hsum : (k + 1) • P + k • P = (2 * k + 1) • P := by
    rw [← add_nsmul]
    congr 1
    omega
  have hDiff : SBase.cross (coordinates A B ((k + 1) • P - k • P)) = 0 := by
    simpa only [hsub] using hBaseCross
  simpa only [hsum] using
    diffAdd_cross_eq_zero_of_cross_eq_zero hB hNextCross hCurrentCross hDiff

/-- Over a field with `2 ≠ 0` and for `B ≠ 0`, the odd Montgomery-ladder step on arbitrary
nonzero representatives is nonzero precisely when the fixed difference `P` is neither infinity
nor the distinguished point of order two. -/
theorem diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (k : ℕ) {SNext SCurrent SBase : Pair K}
    (hNext : SNext ≠ 0) (hCurrent : SCurrent ≠ 0) (hBase : SBase ≠ 0)
    (hNextCross : SNext.cross (coordinates A B ((k + 1) • P)) = 0)
    (hCurrentCross : SCurrent.cross (coordinates A B (k • P)) = 0)
    (hBaseCross : SBase.cross (coordinates A B P) = 0) :
    diffAdd SNext SCurrent SBase ≠ 0 ↔ P ≠ 0 ∧ P ≠ twoTorsionPoint A hB := by
  have hsub : (k + 1) • P - k • P = P := by simp [add_nsmul, add_comm]
  have hDiff : SBase.cross (coordinates A B ((k + 1) • P - k • P)) = 0 := by
    simpa only [hsub] using hBaseCross
  simpa only [hsub] using
    diffAdd_ne_zero_iff_of_cross_eq_zero h₂ hB hNext hCurrent hBase
      hNextCross hCurrentCross hDiff

/-- At the distinguished point of order two, the odd differential-addition step is the zero
raw pair for arbitrary representatives, including in characteristic two. -/
theorem diffAdd_eq_zero_of_cross_eq_zero_twoTorsionPoint (hB : B ≠ 0) (k : ℕ)
    {SNext SCurrent SBase : Pair K}
    (hNext : SNext.cross (coordinates A B ((k + 1) • twoTorsionPoint A hB)) = 0)
    (hCurrent : SCurrent.cross (coordinates A B (k • twoTorsionPoint A hB)) = 0)
    (hBase : SBase.cross (coordinates A B (twoTorsionPoint A hB)) = 0) :
    diffAdd SNext SCurrent SBase = 0 := by
  have hsub : (k + 1) • twoTorsionPoint A hB - k • twoTorsionPoint A hB =
      twoTorsionPoint A hB := by simp [add_nsmul, add_comm]
  exact diffAdd_eq_zero_of_cross_eq_zero hB hNext hCurrent
    (by simpa only [hsub] using hBase) (.inr hsub)

/-- At the distinguished point of order two the odd differential-addition step degenerates
to the zero raw pair for every index, although the odd multiple itself is not infinity.
No restriction on the characteristic is necessary. -/
-- Simplify before coordinates_twoTorsionPoint expands the fixed-difference argument.
@[simp↓]
theorem diffAdd_coordinates_nsmul_twoTorsionPoint (hB : B ≠ 0) (k : ℕ) :
    diffAdd (coordinates A B ((k + 1) • twoTorsionPoint A hB))
      (coordinates A B (k • twoTorsionPoint A hB))
      (coordinates A B (twoTorsionPoint A hB)) = 0 := by
  exact diffAdd_eq_zero_of_cross_eq_zero_twoTorsionPoint hB k
    (Pair.cross_self _) (Pair.cross_self _) (Pair.cross_self _)

end TauCeti.Montgomery
