/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The Jacobson radical of a multivariate power series ring

A multivariate power series over a ring is a unit exactly when its constant coefficient is
(`MvPowerSeries.isUnit_iff_constantCoeff`). Consequently, over a commutative ring, a power series
lies in the Jacobson radical of `MvPowerSeries σ R` exactly when its constant coefficient lies in
the Jacobson radical of `R` (`MvPowerSeries.mem_jacobson_iff`). In particular a constant lies in the
Jacobson radical of `MvPowerSeries σ R` exactly when it lies in that of `R`
(`MvPowerSeries.C_mem_jacobson_iff`).
-/

public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- A multivariate power series lies in the Jacobson radical of `MvPowerSeries σ R` exactly when
its constant coefficient lies in the Jacobson radical of `R`. -/
theorem mem_jacobson_iff {f : MvPowerSeries σ R} :
    f ∈ Ring.jacobson (MvPowerSeries σ R) ↔ constantCoeff f ∈ Ring.jacobson R := by
  simp only [Ring.mem_jacobson_iff, isUnit_iff_constantCoeff, map_add, map_mul, map_one]
  exact ⟨fun h r ↦ by simpa using h (C r), fun h g ↦ h _⟩

/-- A constant multivariate power series lies in the Jacobson radical of `MvPowerSeries σ R`
exactly when its coefficient lies in the Jacobson radical of `R`. -/
@[simp]
theorem C_mem_jacobson_iff {r : R} :
    C r ∈ Ring.jacobson (MvPowerSeries σ R) ↔ r ∈ Ring.jacobson R := by
  rw [mem_jacobson_iff, constantCoeff_C]

end MvPowerSeries
