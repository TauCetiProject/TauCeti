/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Cyclic
public import TauCeti.FieldTheory.GaloisCohomology.Solvable
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Solvable
public import TauCeti.NumberTheory.LocalField.UnitFiltration.ValuationSequence

/-!
# The local second-cohomology bound from the unit Herbrand quotient

For a cyclic extension `L/K` of nonarchimedean local fields, Hilbert 90 and two-periodicity
identify the order of `H²(Gal(L/K), Lˣ)` with the Herbrand quotient of `Lˣ`. The equivariant
valuation sequence then gives the exact formula

`#H²(Gal(L/K), Lˣ) = [L : K] · h(U_L)`.

Consequently the unit calculation `h(U_L) = 1` gives equality with `[L : K]`. For a general
finite Galois extension, solvability of the local Galois group and the field-theoretic solvable
reduction propagate the resulting prime-degree cyclic bound. The final theorem in this file
isolates this propagation: its sole arithmetic input is the unit Herbrand-quotient calculation
for the intermediate prime-degree extensions.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter IX,
  §3 and Chapter XIII, §1.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §1.
-/

public noncomputable section

open Module ValuativeRel

namespace TauCeti

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- For a cyclic extension of local fields, the order of `H²(Gal(L/K), Lˣ)` is the degree
times the Herbrand quotient of the valuation-zero units. -/
theorem natCard_H2_units_eq_finrank_mul_herbrandQuotient_unitFiltration_zero
    [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) =
      finrank K L * TateCohomology.herbrandQuotient
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) := by
  rw [natCard_H2_units_eq_herbrandQuotient,
    herbrandQuotient_units_eq_finrank_mul]

/-- For a cyclic extension of local fields whose valuation-zero units have Herbrand quotient
one, `H²(Gal(L/K), Lˣ)` has order `[L : K]`. -/
theorem natCard_H2_units_eq_finrank_of_herbrandQuotient_unitFiltration_zero
    [IsCyclic (L ≃ₐ[K] L)]
    (hunit : TateCohomology.herbrandQuotient
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) = 1) :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) =
      finrank K L := by
  have h := natCard_H2_units_eq_finrank_mul_herbrandQuotient_unitFiltration_zero K L
  rw [hunit, mul_one] at h
  exact_mod_cast h

/-- **The local `H²` bound reduces to the unit Herbrand quotient in prime-degree
subextensions.** If the valuation-zero units have Herbrand quotient one in every prime-degree
Galois subextension of `L/K`, then the order of `H²(Gal(L/K), Lˣ)` divides `[L : K]`.

The intermediate fields carry their canonical spectral-norm local-field structures in the
hypothesis. This is precisely the form in which the local-unit calculation is consumed. -/
theorem natCard_H2_units_dvd_finrank_of_prime_unit_herbrandQuotient_eq_one
    (hunit : ∀ (E : IntermediateField K L) (F : IntermediateField E L)
      [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)], (finrank E F).Prime →
        letI := finiteIntermediateFieldValuativeRel K L E
        letI := finiteIntermediateFieldTopology K L E
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K L E
        letI := finiteIntermediateFieldValuativeRel E L F
        letI := finiteIntermediateFieldTopology E L F
        haveI := finiteIntermediateField_isNonarchimedeanLocalField E L F
        haveI := finiteIntermediateField_valuativeExtension E L F
        TateCohomology.herbrandQuotient
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitFiltration F 0)) = 1) :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) ∣
      finrank K L := by
  refine natCard_groupCohomology_two_units_dvd_finrank (K := K) (L := L) fun E F _ hp ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K L E
  let _ := finiteIntermediateFieldTopology K L E
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E
  have := finiteIntermediateField_valuativeExtension K L E
  let _ := finiteIntermediateFieldValuativeRel E L F
  let _ := finiteIntermediateFieldTopology E L F
  have := finiteIntermediateField_isNonarchimedeanLocalField E L F
  have := finiteIntermediateField_valuativeExtension E L F
  let _ : Fact (finrank E F).Prime := ⟨hp⟩
  let _ : IsCyclic (F ≃ₐ[E] F) :=
    isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank E F)
  rw [natCard_H2_units_eq_finrank_of_herbrandQuotient_unitFiltration_zero E F
    (hunit E F hp)]

end TauCeti
