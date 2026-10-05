/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# The lowest Taylor coefficient at a root

The Taylor expansion `taylor r p = p(X + r)` of a polynomial `p` at `r` starts in degree
`p.rootMultiplicity r`, and its first coefficient is the value at `r` of `p` divided by the
largest power of `X - r` dividing it. This is the coefficient that survives when `X - r` is
divided out of `p` as often as possible before evaluating at `r`; it is nonzero whenever `p` is
(`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`).

## Main results

* `Polynomial.natTrailingDegree_taylor`: the Taylor expansion at `r` starts in degree
  `p.rootMultiplicity r`.
* `Polynomial.coeff_taylor_rootMultiplicity`, `Polynomial.trailingCoeff_taylor`: its lowest
  coefficient is `(p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The Taylor expansion of `p` at `r` starts in degree `p.rootMultiplicity r`. -/
theorem natTrailingDegree_taylor (p : R[X]) (r : R) :
    (taylor r p).natTrailingDegree = p.rootMultiplicity r := by
  rw [rootMultiplicity_eq_natTrailingDegree, taylor_apply]

/-- The coefficient of `X ^ p.rootMultiplicity r` in the Taylor expansion of `p` at `r` is the
value at `r` of `p` divided by the largest power of `X - r` dividing it. -/
theorem coeff_taylor_rootMultiplicity (p : R[X]) (r : R) :
    (taylor r p).coeff (p.rootMultiplicity r) =
      (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  set m := p.rootMultiplicity r
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p r]
  simpa [taylor_mul, taylor_pow, taylor_coeff_zero] using
    coeff_X_pow_mul (taylor r (p /ₘ (X - C r) ^ m)) m 0

/-- The lowest nonzero coefficient of the Taylor expansion of `p` at `r` is the value at `r` of
`p` divided by the largest power of `X - r` dividing it. -/
theorem trailingCoeff_taylor (p : R[X]) (r : R) :
    (taylor r p).trailingCoeff = (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  rw [trailingCoeff, natTrailingDegree_taylor, coeff_taylor_rootMultiplicity]

end Polynomial
