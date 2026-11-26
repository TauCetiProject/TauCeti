/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerBasis

/-!
# Bounded polynomial unit lifts in local algebras

Evaluation at an element of the maximal ideal detects units by the constant coefficient.
When that element generates a power basis, this gives bounded polynomial representatives of units.
-/

public section

open IsLocalRing Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Evaluation at an element of the maximal ideal is a unit exactly when the polynomial's
constant coefficient is a unit. -/
theorem Polynomial.isUnit_aeval_iff_isUnit_coeff_zero_of_mem_maximalIdeal
    (f : R[X]) {x : S} (hx : x ∈ maximalIdeal S) :
    IsUnit (aeval x f) ↔ IsUnit (f.coeff 0) := by
  calc
    IsUnit (aeval x f) ↔ IsUnit (residue S (aeval x f)) := (isUnit_map_iff (residue S) _).symm
    _ ↔ IsUnit (aeval (residue S x) f) := by
      have h := aeval_algHom_apply (IsScalarTower.toAlgHom R S (ResidueField S)) x f
      simp only [IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq] at h
      rw [h]
    _ ↔ IsUnit (f.coeff 0) := by
      rw [(residue_eq_zero_iff x).mpr hx, ← coeff_zero_eq_aeval_zero',
        IsScalarTower.algebraMap_apply R S (ResidueField S), ResidueField.algebraMap_eq,
        isUnit_map_iff, isUnit_map_iff]

/-- A power basis with generator in the maximal ideal represents every unit by a polynomial
of natural degree below the basis dimension and with unit constant coefficient. -/
theorem PowerBasis.exists_polynomial_lift_isUnit_coeff_zero
    (pb : PowerBasis R S) (hgen : pb.gen ∈ maximalIdeal S) (u : Sˣ) :
    ∃ f : R[X], f.natDegree < pb.dim ∧ aeval pb.gen f = u ∧ IsUnit (f.coeff 0) := by
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval (u : S)
  exact ⟨f, hdeg, hf.symm,
    (f.isUnit_aeval_iff_isUnit_coeff_zero_of_mem_maximalIdeal hgen).mp (hf ▸ u.isUnit)⟩
