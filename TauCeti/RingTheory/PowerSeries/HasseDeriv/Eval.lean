/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm

/-!
# Values of Hasse derivatives of restricted power series

Over a complete ultrametric normed commutative ring `R`, a series `q` restricted at a radius `c`
and all its Hasse derivatives `D⁽ᵗ⁾ q` can be evaluated at every point `b` with `‖b‖ ≤ c` of a
complete ultrametric normed `R`-algebra, and evaluation is a ring homomorphism on restricted
series. Evaluating the formal Leibniz rule `PowerSeries.hasseDeriv_succ_X_sub_C_mul` therefore
gives

```text
(D⁽ᵗ⁺¹⁾ ((X - a) * q))(b) = (b - a) * (D⁽ᵗ⁺¹⁾ q)(b) + (D⁽ᵗ⁾ q)(b).
```

This is how vanishing conditions on the Hasse derivatives of `(X - a) * q` pass to `q`, as in the
Schwarz lemma `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod`.

## Main results

* `PowerSeries.IsRestricted.evalAt_hasseDeriv_succ_X_sub_C_mul`: the evaluated Leibniz rule for
  `(X - a) * q`.
-/

public section

open TauCeti.PowerSeries

namespace PowerSeries

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A] {c : ℝ} {q : R⟦X⟧}

/-- **Evaluated Leibniz rule for `(X - a) * q`.** At a point `b` with `‖b‖ ≤ c`, the Hasse
derivative of order `t + 1` of `(X - a) * q`, for `q` restricted at `c`, takes the value
`(b - a) * (D⁽ᵗ⁺¹⁾ q)(b) + (D⁽ᵗ⁾ q)(b)`. -/
theorem IsRestricted.evalAt_hasseDeriv_succ_X_sub_C_mul (hq : q.IsRestricted c) (a : R) {b : A}
    (hb : ‖b‖ ≤ c) (t : ℕ) :
    (PowerSeries.hasseDeriv (t + 1) ((X - C a) * q)).evalAt b =
      (b - algebraMap R A a) * (PowerSeries.hasseDeriv (t + 1) q).evalAt b +
        (PowerSeries.hasseDeriv t q).evalAt b := by
  have hX := isRestricted_X_sub_C (c := c) a
  rw [hasseDeriv_succ_X_sub_C_mul, IsRestricted.evalAt_add (hX.mul (hq.hasseDeriv _))
    (hq.hasseDeriv _) hb, hX.evalAt_mul (hq.hasseDeriv _) hb, evalAt_X_sub_C]

end PowerSeries
