/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Cohomology.Cup.ModTwo

/-!
# The mod `2` cup square of real projective space

For `N ≥ 2` the integral homology `H₁(RPᴺ; ℤ)` is `ℤ/2`
(`TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd`), so every class of it is
killed by `2` (`TauCeti.RealProjectiveSpace.two_nsmul_singularHomology_one_eq_zero`). By
`TopCat.eq_zero_of_singularCup_self_eq_zero`, a class `w ∈ H¹(RPᴺ; 𝔽₂)` with `w ⌣ w = 0`
therefore vanishes: the nonzero class of `H¹(RPᴺ; 𝔽₂)` has nonzero square
(`TauCeti.RealProjectiveSpace.singularCup_self_ne_zero`). This is the first step of the
computation `H*(RPᴺ; 𝔽₂) = 𝔽₂[w] / (w ^ (N + 1))` of Hatcher, Theorem 3.12, and it separates the
mod `2` cup product from the zero pairing: odd-degree classes can have nonzero squares in
characteristic `2`.

For `N = 1` the conclusion fails, as it must: `H₁(RP¹; ℤ) = ℤ` and `H²(RP¹; 𝔽₂) = 0`.

## Main results

* `TauCeti.RealProjectiveSpace.singularCup_self_ne_zero`: a nonzero class of `H¹(RPᴺ; 𝔽₂)` has
  nonzero cup square, for `N ≠ 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.12, the mod `2` cohomology ring of real projective space.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

namespace TauCeti.RealProjectiveSpace

variable {N : ℕ}

/-- **The mod `2` cup square in real projective space.** For `N ≠ 1`, a nonzero class
`w ∈ H¹(RPᴺ; 𝔽₂)` has nonzero cup square `w ⌣ w ∈ H²(RPᴺ; 𝔽₂)`. Such a class exists for `N ≥ 2`
(`TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_two_eq_zero`), and not for `N = 0`. -/
theorem singularCup_self_ne_zero (hN : N ≠ 1)
    {w : (TopCat.of (RealProjectiveSpace N)).singularCohomology (𝟙_ (ModuleCat.{0} (ZMod 2)))
      (ZMod 2) (𝟙_ (ModuleCat (ZMod 2))) 1} (hw : w ≠ 0) :
    (TopCat.of (RealProjectiveSpace N)).singularCup (ZMod 2) (λ_ _).inv (λ_ _).hom 1 1 2 rfl w w ≠
      0 :=
  fun h ↦ hw
    (TopCat.eq_zero_of_singularCup_self_eq_zero _ (two_nsmul_singularHomology_one_eq_zero hN) h)

end TauCeti.RealProjectiveSpace
