/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Torus
public import TauCeti.Topology.CWComplex.Classical.ClosedAnnulus

/-!
# The Euler characteristic of a closed annulus

The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ` with `0 < r₁` is homeomorphic to `Circle × [r₁, r₂]`
by polar coordinates (`Complex.closedAnnulusHomeomorph`), so its Euler characteristic is
`χ(S¹) · χ([r₁, r₂]) = 0`. Its finite CW type is `TauCeti.finiteCWType_closedAnnulus`.

## Main declarations

* `TauCeti.eulerChar_closedAnnulus`: a closed annulus with `0 < r₁` has `χ = 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Complex

namespace TauCeti

variable {r₁ r₂ : ℝ}

/-- A closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁` has Euler characteristic zero, that of
`Circle × [r₁, r₂]`. -/
@[simp]
theorem eulerChar_closedAnnulus (h₀ : 0 < r₁) : eulerChar (closedAnnulus r₁ r₂) = 0 := by
  rw [(closedAnnulusHomeomorph h₀).eulerChar_eq, eulerChar_prod, eulerChar_circle, zero_mul]

end TauCeti
