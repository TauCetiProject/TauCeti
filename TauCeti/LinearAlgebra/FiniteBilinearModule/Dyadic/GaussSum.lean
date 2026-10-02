/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo
public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum

/-!
# The Gauss sum of the dyadic hyperbolic generator

Nikulin's generator `u^{(2)}(2^k)` has quadratic form `q(x, y) = xy / 2^k` on
`(ℤ/2^k)²`. Its first coordinate axis is a quadratic Lagrangian, so the module is metabolic.
Consequently its Gauss sum is `2^k` and its Gauss-sum invariant is zero. These formulas also
hold at `k = 0`, where the module is trivial.

The calculation uses the explicit quadratic Lagrangian from
`TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo`. Isotropy for the polar pairing
alone would not suffice to determine the Gauss sum.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2, the value on `u^{(2)}(2^k)`.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298, for the Gauss sum of a metabolic quadratic module.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable (k : ℕ)

/-- **The Gauss sum of `u^{(2)}(2^k)` is `2^k`**, in the half-norm convention. -/
@[simp]
theorem gaussSum_dyadicU : (dyadicU k).gaussSum = (2 : ℂ) ^ k := by
  have hc : Nat.card ((⊤ : AddSubgroup (ZMod (2 ^ k))).prod
      (⊥ : AddSubgroup (ZMod (2 ^ k)))) = 2 ^ k := by
    rw [Nat.card_congr (AddSubgroup.prodEquiv (⊤ : AddSubgroup (ZMod (2 ^ k)))
      (⊥ : AddSubgroup (ZMod (2 ^ k)))).toEquiv]
    simp
  rw [gaussSum_eq_natCard_of_isLagrangian (isLagrangian_dyadicU_top_prod_bot k)]
  exact_mod_cast hc

/-- **Nikulin's Gauss-sum invariant of `u^{(2)}(2^k)` is zero.** -/
@[simp]
theorem gaussSign_dyadicU : (dyadicU k).gaussSign = 0 :=
  gaussSign_eq_zero_of_isMetabolic (isNondegenerate_dyadicU k) (isMetabolic_dyadicU k)

end TauCeti.FiniteQuadraticModule
