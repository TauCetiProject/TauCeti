/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double

/-!
# The even Montgomery-ladder relation

Doubling any nonzero representative of the coordinate pair of `[k]P` gives a nonzero
representative of `[2k]P`. This is the even scalar-multiple relation underlying the
Montgomery ladder. The representative may be independently scaled at each step; no affine
normalization or ellipticity assumption is required. In particular, multiples that are
infinity or points of order two are included.

The hypotheses are exactly those of `double_coordinates_of_cross_eq_zero`. There is no
characteristic restriction beyond the scaled relation `4N = (A + 2)D` with `D ≠ 0`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261: the binary ladder relations.
-/

public section

namespace TauCeti.Montgomery

variable {K : Type*} [Field K] [DecidableEq K] {A B N D : K}

/-- The even Montgomery-ladder step for an arbitrary nonzero representative of `[k]P`.
Its output is always nonzero and represents `[2k]P`, including when `[k]P` is infinity or
has order two. No ellipticity assumption is needed. -/
theorem double_nsmul (hB : B ≠ 0) (hD : D ≠ 0) (h : 4 * N = (A + 2) * D)
    (P : (model A B).toAffine.Point) (k : ℕ) {S : Pair K} (hS : S ≠ 0)
    (hSP : S.cross (coordinates A B (k • P)) = 0) :
    double N D S ≠ 0 ∧
      (double N D S).cross (coordinates A B ((2 * k) • P)) = 0 := by
  simpa only [mul_nsmul, two_nsmul, nsmul_add] using
    double_coordinates_of_cross_eq_zero hB hD h hS hSP

end TauCeti.Montgomery
