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
`diffAdd_nsmul` proves this for arbitrary nonzero representatives and gives the exact
exceptional set: the output is nonzero if and only if `P` is neither infinity nor the
distinguished point of order two. In particular the exceptional set does not depend on `k`.
No ellipticity assumption is needed.

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

/-- The odd Montgomery-ladder step on arbitrary nonzero representatives. Its output represents
`[2k + 1]P` precisely when the fixed difference `P` is neither infinity nor the distinguished
point of order two. The cross difference vanishes even in the exceptional cases, when the
output is the zero raw pair. -/
theorem diffAdd_nsmul (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (k : ℕ) {SNext SCurrent SBase : Pair K}
    (hNext : SNext ≠ 0) (hCurrent : SCurrent ≠ 0) (hBase : SBase ≠ 0)
    (hNextCross : SNext.cross (coordinates A B ((k + 1) • P)) = 0)
    (hCurrentCross : SCurrent.cross (coordinates A B (k • P)) = 0)
    (hBaseCross : SBase.cross (coordinates A B P) = 0) :
    (diffAdd SNext SCurrent SBase).cross (coordinates A B ((2 * k + 1) • P)) = 0 ∧
      (diffAdd SNext SCurrent SBase ≠ 0 ↔ P ≠ 0 ∧ P ≠ twoTorsionPoint A hB) := by
  have hsub : (k + 1) • P - k • P = P := by simp [add_nsmul, add_comm]
  have hsum : (k + 1) • P + k • P = (2 * k + 1) • P := by
    rw [← add_nsmul]
    congr 1
    omega
  have hDiff : SBase.cross (coordinates A B ((k + 1) • P - k • P)) = 0 := by
    simpa only [hsub] using hBaseCross
  exact ⟨by simpa only [hsum] using
      diffAdd_cross_eq_zero_of_cross_eq_zero hB hNextCross hCurrentCross hDiff,
    by simpa only [hsub] using
      diffAdd_ne_zero_iff_of_cross_eq_zero h₂ hB hNext hCurrent hBase
        hNextCross hCurrentCross hDiff⟩

/-- The coordinate pairs of multiples of the distinguished point of order two alternate
between infinity and that point. This includes characteristic two. -/
@[simp]
theorem coordinates_nsmul_twoTorsionPoint (hB : B ≠ 0) (k : ℕ) :
    coordinates A B (k • twoTorsionPoint A hB) =
      if k % 2 = 0 then ⟨1, 0⟩ else ⟨0, B⟩ := by
  rw [← mod_addOrderOf_nsmul, addOrderOf_twoTorsionPoint]
  by_cases hk : k % 2 = 0
  · simp [hk]
  · have hk' : k % 2 = 1 := by omega
    simp [hk', twoTorsionPoint_def]

/-- At the distinguished point of order two the odd differential-addition step degenerates
to the zero raw pair for every index, although the odd multiple itself is not infinity.
No restriction on the characteristic is necessary. -/
-- Simplify before the coordinate-pair arguments expand into parity conditionals.
@[simp↓]
theorem diffAdd_coordinates_nsmul_twoTorsionPoint (hB : B ≠ 0) (k : ℕ) :
    diffAdd (coordinates A B ((k + 1) • twoTorsionPoint A hB))
      (coordinates A B (k • twoTorsionPoint A hB))
      (coordinates A B (twoTorsionPoint A hB)) = 0 := by
  have hT : coordinates A B (twoTorsionPoint A hB) = ⟨0, B⟩ := by
    simp [twoTorsionPoint_def]
  by_cases hk : k % 2 = 0
  · have hk' : (k + 1) % 2 ≠ 0 := by omega
    ext <;> simp [diffAdd_x, diffAdd_z, hT, hk, hk', Pair.cross_def]
  · have hk' : (k + 1) % 2 = 0 := by omega
    ext <;> simp [diffAdd_x, diffAdd_z, hT, hk, hk', Pair.cross_def]

end TauCeti.Montgomery
