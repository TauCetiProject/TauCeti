/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.LocalRing.PowerBasis
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series unit lifts for local power bases

A bounded polynomial representative with unit constant coefficient is a unit as a power series.
-/

public section

open IsLocalRing Polynomial

/-- A power basis with generator in the maximal ideal represents every unit by a polynomial
of natural degree below the basis dimension whose image in the power series ring is a unit. -/
theorem PowerBasis.exists_polynomial_lift_powerSeries_unit {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (pb : PowerBasis R S) (hgen : pb.gen ∈ maximalIdeal S) (u : Sˣ) :
    ∃ f : R[X], f.natDegree < pb.dim ∧ aeval pb.gen f = u ∧ IsUnit (f : PowerSeries R) := by
  obtain ⟨f, hdeg, hf, hunit⟩ := pb.exists_polynomial_lift_isUnit_coeff_zero hgen u
  exact ⟨f, hdeg, hf, PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hunit)⟩
