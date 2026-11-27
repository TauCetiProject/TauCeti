/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Convex.SchurInequality
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Schur's inequality

For `x, y, z > 0` and every real exponent `t`,

`0 ≤ x ^ t (x - y) (x - z) + y ^ t (y - z) (y - x) + z ^ t (z - x) (z - y)`,

with equality exactly when `x = y = z` (Mitrinović, *Analytic Inequalities*, §2.17, Thm 1,
p. 119). On `(0, ∞)` the weight `u ↦ u ^ t` is positive, monotone for `t ≥ 0` and antitone for
`t ≤ 0`, hence quasiconvex (`Real.quasiconvexOn_rpow_Ioi`), so both statements are cases of
`QuasiconvexOn.schur_inequality` and `QuasiconvexOn.schur_inequality_eq_zero_iff`. The forms
for natural exponents and nonnegative points in a linearly ordered commutative ring, including the
cubic case `t = 1`, are `TauCeti.schur_inequality_pow` and
`TauCeti.schur_inequality_pow_eq_zero_iff`.

## Main results

* `TauCeti.schur_inequality`: Schur's inequality for positive reals and a real exponent.
* `TauCeti.schur_inequality_eq_zero_iff`: its equality case.
-/

public section

namespace TauCeti

/-- **Schur's inequality**: for `x, y, z > 0` and real `t`,
`0 ≤ x ^ t (x - y) (x - z) + y ^ t (y - z) (y - x) + z ^ t (z - x) (z - y)`. -/
theorem schur_inequality {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (t : ℝ) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - z) * (y - x) + z ^ t * (z - x) * (z - y) :=
  (Real.quasiconvexOn_rpow_Ioi t).schur_inequality hx hy hz (Real.rpow_nonneg hx.le t)
    (Real.rpow_nonneg hy.le t) (Real.rpow_nonneg hz.le t)

/-- The equality case of **Schur's inequality**: for `x, y, z > 0` and real `t`,
`x ^ t (x - y) (x - z) + y ^ t (y - z) (y - x) + z ^ t (z - x) (z - y) = 0` exactly when
`x = y = z`. -/
theorem schur_inequality_eq_zero_iff {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (t : ℝ) :
    x ^ t * (x - y) * (x - z) + y ^ t * (y - z) * (y - x) + z ^ t * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z :=
  (Real.quasiconvexOn_rpow_Ioi t).schur_inequality_eq_zero_iff hx hy hz (Real.rpow_pos_of_pos hx t)
    (Real.rpow_pos_of_pos hy t) (Real.rpow_pos_of_pos hz t)

end TauCeti
