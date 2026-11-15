/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClasses

import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.UnitQuotient
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# The direct norm-index calculation across all quadratic-defect cases

Over a nonarchimedean local field `K` with `2 ≠ 0`, every nonsquare radicand `a ∈ Kˣ` has a finite
quadratic defect exponent `d = defectExponent a`, and the index of `quadraticNormSubgroup (a : K)`
in `Kˣ` is `2` by a purely base-field calculation depending on the parity of `d`:

* **Even defect exponent** (`Even d`): `a` lies in the unramified quadratic square class
  (`TauCeti.unramified_class_iff_even_defectExponent`). Every valuation-one unit is a norm, so
  `unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K` has cardinality
  `2 * #𝓀[K] ^ v_K(2)` and index `1` in `unitSquareClasses K`, while a uniformizer shifts valuation
  parity and gives `(quadraticNormSubgroup (a : K)).index = 2`
  (`TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`).
* **Odd defect exponent** (`Odd d`): norms realize every integer valuation, identifying the full
  norm quotient with the unit-norm quotient
  (`TauCeti.index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent`),
  and the Eisenstein unit-norm parametrization shows `unitQuadraticNormSquareClasses (a : K)` has
  cardinality `#𝓀[K] ^ v_K(2)` and index `2` in `unitSquareClasses K`
  (`TauCeti.relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent`).

Together these yield `TauCeti.quadraticNormSubgroup_index_eq_two_of_defectExponent_eq` without
constructing a field extension or counting square classes of `K(√a)`.

## Main results

* `TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent`,
  `TauCeti.relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent`, and
  `TauCeti.natCard_unitQuadraticNormSquareClasses_of_even_defectExponent`: unit-norm square classes
  for finite even defect exponent.
* `TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent`,
  `TauCeti.relIndex_unitQuadraticNormSquareClasses_eq_one_iff_even_defectExponent`,
  `TauCeti.relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent`, and
  `TauCeti.relIndex_unitQuadraticNormSquareClasses_dvd_two`: parity dichotomy for unit-norm square
  classes.
* `TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`,
  `TauCeti.quadraticNormSubgroup_index_eq_two_of_defectExponent_eq`, and
  `TauCeti.quadraticNormSubgroup_index_eq_two_of_odd`: the direct norm-index theorems.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For a radicand of finite even quadratic defect exponent, every valuation-one unit is a norm, so
`unitQuadraticNormSquareClasses (a : K)` equals `unitSquareClasses K`. No `2 ≠ 0` hypothesis is
needed: `TauCeti.two_ne_zero_of_even_defectExponent` supplies it. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K := by
  have hu := (unramified_class_iff_even_defectExponent
    (two_ne_zero_of_even_defectExponent hd hev) hd).mpr hev
  refine (unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff _).mpr fun b hbv ↦ ?_
  rw [mem_quadraticNormSubgroup_iff_even_of_unramified_class hu,
    (normalizedValuation_eq_one_iff b).mpr hbv, toAdd_one]
  exact Even.zero

/-- For a radicand of finite even quadratic defect exponent,
`unitQuadraticNormSquareClasses (a : K)` has index `1` in `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 1 := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent hd hev,
    Subgroup.relIndex_self]

/-- For a radicand of finite even quadratic defect exponent,
`unitQuadraticNormSquareClasses (a : K)` has cardinality `2 * #𝓀[K] ^ natCastValuation K 2 h2`. -/
theorem natCard_unitQuadraticNormSquareClasses_of_even_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      2 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent hd hev,
    card_unitSquareClasses K h2]

/-- Over a nonarchimedean local field with `2 ≠ 0`, the unit-norm square classes of a nonsquare
radicand `a` of defect exponent `d` exhaust `unitSquareClasses K` if and only if `d` is even. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K ↔ Even d := by
  refine ⟨fun heq ↦ ?_,
    unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent hd⟩
  by_contra hnot
  have hidx := relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd
    (Int.not_even_iff_odd.mp hnot)
  rw [heq, Subgroup.relIndex_self] at hidx
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, a nonsquare radicand `a` of defect exponent `d`
has `(unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 1` if and only if
`d` is even. -/
theorem relIndex_unitQuadraticNormSquareClasses_eq_one_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 1 ↔ Even d := by
  refine ⟨fun hidx ↦ ?_, relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent hd⟩
  by_contra hnot
  have h2idx := relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd
    (Int.not_even_iff_odd.mp hnot)
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, a nonsquare radicand `a` of defect exponent `d`
has `(unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2` if and only if
`d` is odd. -/
theorem relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 ↔ Odd d := by
  refine ⟨fun hidx ↦ ?_, relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd⟩
  by_contra hnot
  have h1idx := relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent hd
    (Int.not_odd_iff_even.mp hnot)
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, the index of
`unitQuadraticNormSquareClasses (a : K)` inside `unitSquareClasses K` divides `2` for every
`a ∈ Kˣ`. -/
theorem relIndex_unitQuadraticNormSquareClasses_dvd_two (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) ∣ 2 := by
  by_cases ha : IsSquare a
  · have : Invertible (2 : K) := invertibleOfNonzero h2
    rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_isSquare ha, Subgroup.relIndex_self]
    exact one_dvd 2
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
    rcases Int.even_or_odd d with hev | hodd
    · rw [relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent hd.symm hev]
      exact one_dvd 2
    · rw [relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd.symm hodd]

/-- **Direct norm-index theorem for an even-defect radicand** (O'Meara §63A). For any `a ∈ Kˣ` of
finite even quadratic defect exponent, `quadraticNormSubgroup (a : K)` consists of the elements of
even normalized valuation and therefore has index `2` in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_even_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_unramified_class
    ((unramified_class_iff_even_defectExponent (two_ne_zero_of_even_defectExponent hd hev)
      hd).mpr hev)

/-- **Direct norm-index theorem across all quadratic-defect cases** (O'Meara §63A). Over a
nonarchimedean local field with `2 ≠ 0`, every radicand `a ∈ Kˣ` of finite quadratic defect
exponent `d` has `(quadraticNormSubgroup (a : K)).index = 2`:
* when `d` is even, `a` lies in the unramified square class and its norms are the elements of even
  valuation (`TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`);
* when `d` is odd, norms realize every valuation so the full norm index equals the unit-norm index
  (`TauCeti.index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent`),
  which equals `2` by counting Eisenstein unit-norm square classes in the base field
  (`TauCeti.relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent`). -/
theorem quadraticNormSubgroup_index_eq_two_of_defectExponent_eq (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rcases Int.even_or_odd d with hev | hodd
  · exact quadraticNormSubgroup_index_eq_two_of_even_defectExponent hd hev
  · rw [← index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent
      hd hodd, ← relIndex_unitQuadraticNormSquareClasses,
      relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd]

/-- For a radicand of odd normalized valuation, the quadratic norm subgroup has index two. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_defectExponent_eq h2 (defectExponent_of_odd ha)

end TauCeti
