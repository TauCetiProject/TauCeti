/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ProjectiveLine
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ProjectiveLine.Cohomology

/-!
# The index of `∂bar` on the projective line is its Euler characteristic

The operator `∂bar` on smooth complex functions over `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` has kernel the
constants and cokernel zero, so its real index is `2`
(`TauCeti.dolbeaultCohomology.finrank_zero_zero_sub_finrank_zero_one_projectivization`). This file
identifies that `2` with the Euler characteristic `χ(ℂℙ¹)` of a finite CW model, the sphere
instance of the closed Riemann-Roch formula `ind_ℝ D = n χ(Σ) + 2 c₁(E)[Σ]` with `n = 1` and the
trivial bundle, `c₁ = 0`.

The Euler characteristic side, `χ(ℂℙ¹) = 2` (`TauCeti.ProjectiveLine.eulerChar_eq_two`), is
computed from the homeomorphism with the Riemann sphere `OnePoint ℂ`.

## Main declarations

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

namespace dolbeaultCohomology

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
