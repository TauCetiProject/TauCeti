/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Coefficient sup norm bounded by Mahler measure

Mathlib's `Polynomial.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure` bounds the coefficient
sup norm of a complex polynomial `p` by `(deg p).choose (deg p / 2) * p.mahlerMeasure`. Bounding the
middle binomial coefficient by `2 ^ deg p` yields the simpler exponential estimate
`p.supNorm ≤ 2 ^ p.natDegree * p.mahlerMeasure`
(`Polynomial.supNorm_le_two_pow_natDegree_mul_mahlerMeasure`), used in root-location bounds and
height comparisons.

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.2.
* J.-H. Evertse, *Diophantine Approximation* (2019), Chapter 6, Theorem 6.1.
-/

public section

namespace Polynomial

/-- The coefficient sup norm of a complex polynomial is at most `2 ^ deg p` times its Mahler
measure. -/
theorem supNorm_le_two_pow_natDegree_mul_mahlerMeasure (p : ℂ[X]) :
    p.supNorm ≤ 2 ^ p.natDegree * p.mahlerMeasure :=
  p.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure.trans
    (mul_le_mul_of_nonneg_right (mod_cast Nat.choose_le_two_pow _ _) p.mahlerMeasure_nonneg)

end Polynomial
