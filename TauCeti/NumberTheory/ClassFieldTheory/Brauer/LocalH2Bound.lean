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
public import TauCeti.NumberTheory.LocalField.UnitFiltration.TateCohomology
public import TauCeti.NumberTheory.LocalField.UnitFiltration.ValuationSequence

/-!
# The local second-cohomology bound

For a cyclic extension `L/K` of nonarchimedean local fields, Hilbert 90 and two-periodicity
identify the order of `H²(Gal(L/K), Lˣ)` with the Herbrand quotient of `Lˣ`, and the equivariant
valuation sequence gives `h(Lˣ) = [L : K] · h(U_L)`. Since the valuation-zero units have Herbrand
quotient `h(U_L) = 1` (`TauCeti.TateCohomology.herbrandQuotient_unitFiltration_zero`), this gives

`#H²(Gal(L/K), Lˣ) = [L : K]`.

For a general finite Galois extension, the local Galois group is solvable, and the
field-theoretic solvable reduction propagates the prime-degree cyclic case to the bound
`#H²(Gal(L/K), Lˣ) ∣ [L : K]`. This bounds the relative Brauer group of a finite Galois layer;
compared with the unramified layer of the same degree, it shows that every local Brauer class is
split by an unramified extension.

## Main results

* `TauCeti.natCard_H2_units_eq_finrank`: `#H²(Gal(L/K), Lˣ) = [L : K]` for cyclic `L/K`.
* `TauCeti.natCard_H2_units_dvd_finrank`: `#H²(Gal(L/K), Lˣ) ∣ [L : K]` for every finite Galois
  `L/K`.

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

/-- **The local `H²` of a cyclic extension.** For a cyclic extension `L/K` of nonarchimedean
local fields, `H²(Gal(L/K), Lˣ)` has order `[L : K]`. -/
theorem natCard_H2_units_eq_finrank [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) = finrank K L := by
  have h := natCard_H2_units_eq_herbrandQuotient (K := K) (L := L)
  rw [herbrandQuotient_units_eq_finrank_mul, TateCohomology.herbrandQuotient_unitFiltration_zero,
    mul_one] at h
  exact_mod_cast h

/-- **The local `H²` bound.** For a finite Galois extension `L/K` of nonarchimedean local fields,
the order of `H²(Gal(L/K), Lˣ)` divides `[L : K]`. -/
theorem natCard_H2_units_dvd_finrank :
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
  rw [natCard_H2_units_eq_finrank E F]

end TauCeti
