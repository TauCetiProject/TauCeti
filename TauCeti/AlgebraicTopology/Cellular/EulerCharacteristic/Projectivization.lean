/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ComplexProjective
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# The Euler characteristic of the projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`

The projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`, the carrier of the affine complex atlas on `ℂℙⁿ`,
is homeomorphic to the sphere-quotient model `TauCeti.ComplexProjectiveSpace n`
(`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`). That model has a finite CW
structure with Euler characteristic `n + 1` (`TauCeti.eulerChar_complexProjectiveSpace`), and both
facts transport along the homeomorphism. For `n = 1` this gives `χ(ℂℙ¹) = 2`.

## Main declarations

* `TauCeti.finiteCWType_projectivization`: `ℙ ℂ (Fin (n + 1) → ℂ)` has finite CW type.
* `TauCeti.eulerChar_projectivization`: `χ(ℙ ℂ (Fin (n + 1) → ℂ)) = n + 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44, and Example 0.6.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- The complex projective space `ℙ ℂ (Fin (n + 1) → ℂ)` has finite CW type. -/
instance finiteCWType_projectivization (n : ℕ) : FiniteCWType (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  (ComplexProjectiveSpace.homeomorphProjectivization n).symm.finiteCWType

/-- **The Euler characteristic of complex projective space** on the projectivization carrier:
`χ(ℙ ℂ (Fin (n + 1) → ℂ)) = n + 1`. -/
@[simp]
theorem eulerChar_projectivization (n : ℕ) : eulerChar (ℙ ℂ (Fin (n + 1) → ℂ)) = n + 1 := by
  rw [← (ComplexProjectiveSpace.homeomorphProjectivization n).eulerChar_eq,
    eulerChar_complexProjectiveSpace]

end TauCeti
