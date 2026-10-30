/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import TauCeti.LinearAlgebra.IntegralLattice.Unit

/-!
# Coordinate powers of the rank-one root lattice

The coordinate power of `A₁` over a finite index type has the same integral carrier as the
standard unit lattice, with twice its dot-product form. The resulting lattice equality also
covers the empty index type and identifies orthogonal sums of copies of `A₁` with scaled
standard coordinates.
-/

public section

namespace TauCeti.IntegralLattice

/-- An orthogonal sum of copies of `A₁` is the standard integer-coordinate lattice with
its form scaled by two. -/
theorem coordinatePower_a1_eq_smul_unitLattice (ι : Type*) [Fintype ι] :
    a1.coordinatePower ι = (2 : ℤ) • unitLattice ι := by
  apply IntegralLattice.ext
  · ext x
    simp only [mem_pi_carrier_iff, smul_carrier,
      mem_unitLattice_carrier_iff, mem_a1_carrier_iff]
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [pi_form, piForm_apply, a1_form_apply,
      smul_form, LinearMap.smul_apply, unitLattice_form_apply,
      smul_eq_mul, mul_assoc, Finset.mul_sum]
    norm_num

end TauCeti.IntegralLattice
