/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.PadicTower.Reduction
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series unit lifts in the local cyclotomic tower

Every unit in the integral closure of `ℤ_p` at a cyclotomic level has a bounded polynomial
representative whose image in the formal power series ring is a unit. This is the finite
polynomial lift used in J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic
L-functions*, Essential Number Theory 4 (2025), Lemma 10.1, with a degree bound from the
cyclotomic power basis.
-/

public section

open Polynomial

namespace TauCeti.padicCyclotomicField

variable (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω]
  [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] [IsScalarTower ℤ_[p] ℚ_[p] Ω]

/-- Every integral cyclotomic unit has a bounded polynomial representative whose image as a
formal power series is a unit. The displayed evaluation is finite polynomial evaluation. -/
theorem exists_polynomial_lift_powerSeries_unit (n : ℕ)
    (u : (integralClosure ℤ_[p] (padicCyclotomicField p Ω n))ˣ) :
    ∃ f : ℤ_[p][X], f.natDegree < p ^ n * (p - 1) ∧
      aeval (integralRoot p Ω n - 1) f = u ∧ IsUnit (f : PowerSeries ℤ_[p]) := by
  obtain ⟨f, hdeg, hf, hunit⟩ := exists_polynomial_lift_unit p Ω n u
  exact ⟨f, hdeg, hf, PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hunit)⟩

end TauCeti.padicCyclotomicField
