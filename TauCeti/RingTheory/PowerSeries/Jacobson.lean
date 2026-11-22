/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Jacobson radical of a power series ring

A power series over a commutative ring is a unit exactly when its constant coefficient is
(`PowerSeries.isUnit_iff_constantCoeff`). Consequently a power series lies in the Jacobson radical
of `R⟦X⟧` exactly when its constant coefficient lies in the Jacobson radical of `R`
(`PowerSeries.mem_jacobson_iff`). In particular a constant lies in the Jacobson radical of `R⟦X⟧`
exactly when it lies in that of `R` (`PowerSeries.C_mem_jacobson_iff`); for instance `p` lies in
the Jacobson radical of `W(k)⟦X⟧` for a perfect ring `k` of characteristic `p`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A power series lies in the Jacobson radical of `R⟦X⟧` exactly when its constant coefficient
lies in the Jacobson radical of `R`. -/
theorem mem_jacobson_iff {f : R⟦X⟧} :
    f ∈ Ring.jacobson R⟦X⟧ ↔ constantCoeff f ∈ Ring.jacobson R := by
  simp only [Ring.mem_jacobson_iff, isUnit_iff_constantCoeff, map_add, map_mul, map_one]
  exact ⟨fun h r ↦ by simpa using h (C r), fun h g ↦ h _⟩

/-- A constant power series lies in the Jacobson radical of `R⟦X⟧` exactly when its coefficient
lies in the Jacobson radical of `R`. -/
@[simp]
theorem C_mem_jacobson_iff {r : R} : C r ∈ Ring.jacobson R⟦X⟧ ↔ r ∈ Ring.jacobson R := by
  rw [mem_jacobson_iff, constantCoeff_C]

end PowerSeries
