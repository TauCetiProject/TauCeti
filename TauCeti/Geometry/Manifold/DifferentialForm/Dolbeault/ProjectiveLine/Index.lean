/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ProjectiveLine.Cohomology
import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization

/-!
# The index of `∂bar` on the projective line is its Euler characteristic

The operator `∂bar` on smooth complex functions over `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` has kernel the
constants and cokernel zero, so its real index is `2`
(`TauCeti.dolbeaultCohomology.finrank_zero_zero_sub_finrank_zero_one_projectivization`). This file
identifies that `2` with the Euler characteristic `χ(ℂℙ¹)` of a finite CW model, the sphere
instance of the closed Riemann-Roch formula `ind_ℝ D = n χ(Σ) + 2 c₁(E)[Σ]` with `n = 1` and the
trivial bundle, `c₁ = 0`.

The projective line is homeomorphic to the Riemann sphere `OnePoint ℂ` through the homeomorphism
underlying `OnePoint.diffeomorphProjectivization`, and the one-point compactification of the real
plane has finite CW type and Euler characteristic `1 + (-1) ^ 2 = 2` (`TauCeti.eulerChar_onePoint`).

The finite CW type of `ℂℙ¹` is provided as a theorem and used as a local instance here, rather than
as a global instance, leaving room for a general instance on compact manifolds. Since
`FiniteCWType` is a `Prop`, the Euler characteristic statements below apply verbatim under any
other instance.

## Main declarations

* `TauCeti.ProjectiveLine.finiteCWType`: `ℂℙ¹` has finite CW type.
* `TauCeti.ProjectiveLine.eulerChar_eq_two`: `χ(ℂℙ¹) = 2`.
* `dolbeaultCohomology.finrank_zero_zero_sub_finrank_zero_one_projectivization_eq_eulerChar`:
  the index of `∂bar` on complex functions over `ℂℙ¹` is `χ(ℂℙ¹)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Theorem C.1.10.
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
theorem eulerChar_eq_two : eulerChar (ℙ ℂ (Fin 2 → ℂ)) = 2 := by
  rw [← onePointHomeomorph.eulerChar_eq, eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

end ProjectiveLine

namespace dolbeaultCohomology

attribute [local instance] ProjectiveLine.finiteCWType

/-- **The index of `∂bar` on the projective line is its Euler characteristic.** For complex
functions over `ℂℙ¹`, `dim_ℝ H^(0,0) - dim_ℝ H^(0,1) = χ(ℂℙ¹)`: both sides are `2`
(`finrank_zero_zero_sub_finrank_zero_one_projectivization` and
`TauCeti.ProjectiveLine.eulerChar_eq_two`). This is the sphere case of
`ind_ℝ D = n χ(Σ) + 2 c₁(E)[Σ]` for the trivial line bundle, `n = 1` and `c₁ = 0`. -/
theorem finrank_zero_zero_sub_finrank_zero_one_projectivization_eq_eulerChar :
    (finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 0) : ℤ) -
      finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 1) =
      eulerChar (ℙ ℂ (Fin 2 → ℂ)) := by
  rw [finrank_zero_zero_sub_finrank_zero_one_projectivization, ProjectiveLine.eulerChar_eq_two]

end dolbeaultCohomology

end TauCeti
