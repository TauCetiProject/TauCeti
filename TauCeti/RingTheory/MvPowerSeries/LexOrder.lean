/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Basic
public import TauCeti.RingTheory.MvPowerSeries.Convolution

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Coefficient-subspace division for multivariate power series

Let `K` be a field, `A` a `K`-algebra, and `E` a `K`-submodule of `A`. For any variable type `σ`,
multiplying a formal power series `U : MvPowerSeries σ A` on the left by
`MvPowerSeries.map (algebraMap K A) D` for a nonzero scalar power series `D : MvPowerSeries σ K`
preserves and reflects membership of all coefficients in `E`.

This is the power-series coefficient-membership step of Bosch–Güntzer–Remmert,
*Non-Archimedean Analysis*, §5.3.2, Theorem 1. The reflection direction is the field case of
`MvPowerSeries.coeff_mem_of_coeff_map_mul_mem`, since every quotient of a `K`-vector space is
torsion-free.

## Main results

* `MvPowerSeries.forall_coeff_map_mul_mem_iff`: multiplying on the left by a nonzero scalar power
  series preserves and reflects coefficient membership in `E`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.3.2, Theorem 1.
-/

public section

namespace MvPowerSeries

variable {σ K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Multiplying on the left by a nonzero scalar power series `D : MvPowerSeries σ K` preserves and
reflects coefficient membership in `E : Submodule K A`. -/
theorem forall_coeff_map_mul_mem_iff {D : MvPowerSeries σ K} (hD : D ≠ 0)
    {U : MvPowerSeries σ A} {E : Submodule K A} :
    (∀ β, coeff β (MvPowerSeries.map (algebraMap K A) D * U) ∈ E) ↔ ∀ α, coeff α U ∈ E :=
  ⟨coeff_mem_of_coeff_map_mul_mem E hD, coeff_map_mul_mem D⟩

end MvPowerSeries
