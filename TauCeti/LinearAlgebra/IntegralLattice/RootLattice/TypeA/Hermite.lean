/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Hermite
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic

/-!
# The root lattice `A₂` attains equality in Hermite's inequality

Hermite's inequality `min L ≤ (4 / 3) ^ ((n - 1) / 2) · (det L) ^ (1 / n)`
(`TauCeti.IntegralLattice.IsPosDef.minimum_le_rpow_mul_determinant_rpow`) is sharp in rank `2`:
the root lattice `A₂` has minimum `2` and determinant `3`, and
`2 = (4 / 3) ^ (1 / 2) · 3 ^ (1 / 2)`.

## Main results

* `TauCeti.IntegralLattice.minimum_typeARootLattice_two_eq_rpow_mul_determinant_rpow`: `A₂`
  attains equality in Hermite's inequality.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.5.
-/

public section

open Module

namespace TauCeti.IntegralLattice

/-- **`A₂` attains equality in Hermite's inequality.** The root lattice of type `A₂` has rank `2`,
minimum `2` and determinant `3`, and `2 = (4 / 3) ^ (1 / 2) · 3 ^ (1 / 2)`. -/
theorem minimum_typeARootLattice_two_eq_rpow_mul_determinant_rpow :
    ((typeARootLattice 2).minimum : ℝ) =
      (4 / 3 : ℝ) ^ (((finrank ℤ (typeARootLattice 2) : ℝ) - 1) / 2) *
        ((typeARootLattice 2).determinant : ℝ) ^ (1 / (finrank ℤ (typeARootLattice 2) : ℝ)) := by
  have hexp : ((2 : ℝ) - 1) / 2 = 1 / 2 := by norm_num
  have hbase : (4 / 3 * 3 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [finrank_eq_card_basis (typeASimpleRootBasis 2), minimum_typeARootLattice 2 two_ne_zero,
    determinant_typeARootLattice, Fintype.card_fin]
  push_cast
  rw [hexp, ← Real.mul_rpow (by norm_num) (by norm_num), hbase, ← Real.rpow_mul (by norm_num)]
  norm_num

end TauCeti.IntegralLattice
