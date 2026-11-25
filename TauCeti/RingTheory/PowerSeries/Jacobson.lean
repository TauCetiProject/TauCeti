/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.MvPowerSeries.Jacobson

/-!
# The Jacobson radical of a power series ring

A power series over a commutative ring lies in the Jacobson radical of `R⟦X⟧` exactly when its
constant coefficient lies in the Jacobson radical of `R` (`PowerSeries.mem_jacobson_iff`), the
one-variable case of `MvPowerSeries.mem_jacobson_iff`. In particular a constant lies in the
Jacobson radical of `R⟦X⟧` exactly when it lies in that of `R` (`PowerSeries.C_mem_jacobson_iff`);
for instance `p` lies in the Jacobson radical of `W(k)⟦X⟧` for a perfect ring `k` of
characteristic `p`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A power series lies in the Jacobson radical of `R⟦X⟧` exactly when its constant coefficient
lies in the Jacobson radical of `R`. -/
theorem mem_jacobson_iff {f : R⟦X⟧} :
    f ∈ Ring.jacobson R⟦X⟧ ↔ constantCoeff f ∈ Ring.jacobson R :=
  MvPowerSeries.mem_jacobson_iff

/-- A constant power series lies in the Jacobson radical of `R⟦X⟧` exactly when its coefficient
lies in the Jacobson radical of `R`. -/
@[simp]
theorem C_mem_jacobson_iff {r : R} : C r ∈ Ring.jacobson R⟦X⟧ ↔ r ∈ Ring.jacobson R := by
  rw [mem_jacobson_iff, constantCoeff_C]

end PowerSeries
