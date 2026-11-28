/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.PowerBasis
import TauCeti.RingTheory.Jacobson.Polynomial

/-!
# Bounded polynomial unit lifts

A power basis whose generator belongs to the Jacobson radical represents every unit by a
polynomial of natural degree below the basis dimension and with unit constant coefficient,
provided the scalar map reflects units.
-/

public section

open Polynomial

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Nontrivial S]

/-- A power basis with generator in the Jacobson radical represents every unit by a polynomial
of natural degree below the basis dimension and with unit constant coefficient. -/
theorem PowerBasis.exists_polynomial_lift_isUnit_coeff_zero
    (pb : PowerBasis R S) (hgen : pb.gen ∈ Ring.jacobson S) (u : Sˣ) :
    ∃ f : R[X], f.natDegree < pb.dim ∧ aeval pb.gen f = u ∧ IsUnit (f.coeff 0) := by
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval (u : S)
  exact ⟨f, hdeg, hf.symm,
    (f.isUnit_aeval_iff_isUnit_coeff_zero_of_mem_jacobson hgen).mp (hf ▸ u.isUnit)⟩
