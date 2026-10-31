/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.AGM
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Trigonometric

/-!
# Gauss's AGM evaluation of the complete elliptic integral of the first kind

For a modulus `k` with `k ^ 2 < 1` and complementary modulus `k' = √(1 - k²)`, the identity
`1 - k² sin² θ = cos² θ + k'² sin² θ` writes the complete elliptic integral of the first kind as
the trigonometric AGM integral with axes `1` and `k'`. Its evaluation by the
arithmetic-geometric mean then gives **Gauss's theorem**
`K(k) = π / (2 M(1, k'))`, where `M = NNReal.agm`.

Since the AGM converges quadratically, this is the standard way to compute `K` numerically, and
it is the input to the AGM formulas for the lemniscate constant and for real periods of elliptic
curves.

## Main statements

* `TauCeti.Real.legendreK_eq_agmIntegral`: `K(k) = agmIntegral 1 √(1 - k²)`.
* `TauCeti.Real.legendreK_eq_pi_div_two_div_agm`: Gauss's theorem `K(k) = π / 2 / M(1, k')`.

## References

* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Theorem 1.1.
* NIST *Digital Library of Mathematical Functions*, §19.8, <https://dlmf.nist.gov/19.8>.
-/

public section

namespace TauCeti.Real

open _root_.Real NNReal

/-- The complete elliptic integral of the first kind is the AGM integral with axes `1` and the
complementary modulus `√(1 - k²)`. -/
theorem legendreK_eq_agmIntegral {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = agmIntegral 1 √(1 - k ^ 2) := by
  have hk' : √(1 - k ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [agmIntegral_def, ← integral_rpow_cos_sq_add_sin_sq_eq_integral_Ioi one_ne_zero hk',
    legendreK_def, legendreF_def, Real.sq_sqrt (by linarith)]
  congr 1 with θ
  rw [one_pow, one_mul, Real.cos_sq']
  ring_nf

/-- **Gauss's theorem**: for `k ^ 2 < 1`, the complete elliptic integral of the first kind is
`K(k) = π / (2 M(1, √(1 - k²)))`, where `M` is the arithmetic-geometric mean `NNReal.agm`. -/
theorem legendreK_eq_pi_div_two_div_agm {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = π / 2 / agm 1 (√(1 - k ^ 2)).toNNReal := by
  rw [legendreK_eq_agmIntegral hk, ← agmIntegral_eq_pi_div_two_div_agm, NNReal.coe_one,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _)]

end TauCeti.Real
