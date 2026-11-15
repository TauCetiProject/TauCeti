/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Stabilizer
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Subgroup

/-!
# The index of the proper local stabilizer

The proper local stabilizer is the determinant-one part of `K_p(L)`. Its index in
`K_p(L)` divides two, and is two exactly when `K_p(L)` contains an isometry of determinant
minus one. The statements use `Subgroup.relIndex`: the relative index of `SO(V_p)` in
`K_p(L)` is, by definition, the index of their intersection in `K_p(L)`.

Nondegeneracy is needed to ensure that every orthogonal determinant is `±1`. No parity,
positive rank or odd-prime hypothesis is imposed, so the criterion also applies at two
and on the zero space. It distinguishes full from proper stabilizers without assuming
that an improper isometry exists.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A.
-/

public section

open TauCeti.QuadraticMap QuadraticMap
open scoped TensorProduct

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (L : IntegralLattice V) [L.IsNondegenerate] (p : ℕ) [Fact p.Prime]

/-- The proper local stabilizer has index dividing two in the full local stabilizer. -/
theorem relIndex_localStabilizer_dvd_two :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) ∣ 2 := by
  have := L.finiteDimensional
  have hQ := QuadraticForm.Nondegenerate.baseChange (L := ℚ_[p]) L.nondegenerate_norm
  exact (L.localStabilizer p).relIndex_specialOrthogonalWithin_dvd_two
    (nondegenerate_polar_iff.mpr hQ).1

/-- The proper local stabilizer has index two exactly when the full local stabilizer
contains an isometry of determinant minus one. -/
theorem relIndex_localStabilizer_eq_two_iff :
    (specialOrthogonalWithin (L.norm.baseChange ℚ_[p])).relIndex (L.localStabilizer p) = 2 ↔
      ∃ g ∈ L.localStabilizer p, orthogonalDet (L.norm.baseChange ℚ_[p]) g = -1 := by
  have := L.finiteDimensional
  have hQ := QuadraticForm.Nondegenerate.baseChange (L := ℚ_[p]) L.nondegenerate_norm
  exact (L.localStabilizer p).relIndex_specialOrthogonalWithin_eq_two_iff
    (nondegenerate_polar_iff.mpr hQ).1

end TauCeti.IntegralLattice
