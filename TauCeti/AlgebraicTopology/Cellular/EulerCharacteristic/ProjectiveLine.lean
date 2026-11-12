/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Euler characteristic of the projective line

The projective line `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` is homeomorphic to the Riemann sphere `OnePoint ℂ`
through the homeomorphism underlying `OnePoint.diffeomorphProjectivization`, and the one-point
compactification of the real plane has finite CW type and Euler characteristic
`1 + (-1) ^ 2 = 2` (`TauCeti.eulerChar_onePoint`). Transporting along the homeomorphism gives the
same for `ℂℙ¹`.

The finite CW type of `ℂℙ¹` is provided as a theorem and used as a local instance here, rather than
as a global instance, leaving room for a general instance on compact manifolds. Since
`FiniteCWType` is a `Prop`, the Euler characteristic statement below applies verbatim under any
other instance.

## Main declarations

* `TauCeti.ProjectiveLine.finiteCWType`: `ℂℙ¹` has finite CW type.
* `TauCeti.ProjectiveLine.eulerChar_eq_two`: `χ(ℂℙ¹) = 2`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

open Module
open scoped LinearAlgebra.Projectivization

namespace TauCeti

namespace ProjectiveLine

/-- The homeomorphism between the Riemann sphere `OnePoint ℂ` and the projective line `ℂℙ¹`,
underlying the biholomorphism `OnePoint.diffeomorphProjectivization`. -/
private noncomputable def onePointHomeomorph : OnePoint ℂ ≃ₜ ℙ ℂ (Fin 2 → ℂ) :=
  (OnePoint.diffeomorphProjectivization ℂ 0).toHomeomorph

/-- **The projective line has finite CW type**, being homeomorphic to the Riemann sphere
`OnePoint ℂ`. This is a theorem, not a global instance; use it as a local instance where needed. -/
theorem finiteCWType : FiniteCWType (ℙ ℂ (Fin 2 → ℂ)) :=
  onePointHomeomorph.symm.finiteCWType

attribute [local instance] finiteCWType

/-- **The Euler characteristic of the projective line.** `χ(ℂℙ¹) = 2`, transported from the
Riemann sphere `OnePoint ℂ` along their homeomorphism. The finite CW type is
`TauCeti.ProjectiveLine.finiteCWType`. -/
@[simp]
theorem eulerChar_eq_two : eulerChar (ℙ ℂ (Fin 2 → ℂ)) = 2 := by
  rw [← onePointHomeomorph.eulerChar_eq, eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

end ProjectiveLine

end TauCeti
