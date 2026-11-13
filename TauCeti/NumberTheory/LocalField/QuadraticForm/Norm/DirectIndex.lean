/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClasses

import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Count
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Unit-norm square-class counts and indices across all quadratic defects

Let `K` be a nonarchimedean local field with `2 ≠ 0` and residue cardinality `q = #𝓀[K]`, and let
`a : Kˣ` be a radicand in `Kˣ`. The subgroup
`TauCeti.unitQuadraticNormSquareClasses (a : K) ≤ TauCeti.unitSquareClasses K` depends only on the
square class of `a`, and its size and index are determined by the quadratic defect of `a`, with no
integrality or unit-valuation hypothesis on `a`:

* When `a` has finite odd defect exponent `d` — covering both odd-valuation radicands (rescaled to a
  uniformizer) and even-valuation radicands of odd defect (rescaled to a valuation-one Eisenstein
  unit radicand) — `unitQuadraticNormSquareClasses (a : K)` has cardinality `q ^ v_K(2)` and index
  `2` inside `unitSquareClasses K`.
* When `a` is a square (`δ(a) = ⊤`) or a nonsquare of even defect exponent `d`, every integer-ring
  unit is a norm and `unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K`.

Combined with the valuation-coset reduction for odd-defect radicands and the even-valuation norm
criterion for the unramified class, these counts yield a purely base-field proof that
`quadraticNormSubgroup (a : K)` has index `2` in `Kˣ` for every nonsquare `a`.

## Main results

* `TauCeti.natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent`: `q ^ v_K(2)` unit-norm
  square classes for any `a : Kˣ` of odd defect exponent.
* `TauCeti.relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent`: index `2` inside
  `unitSquareClasses K` for any `a : Kˣ` of odd defect exponent.
* `TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent` and
  `TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff`: equality with
  `unitSquareClasses K` characterized by even (or infinite) defect exponent.
* `TauCeti.relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent` and
  `TauCeti.relIndex_unitQuadraticNormSquareClasses_eq_two_iff`: index `2` inside
  `unitSquareClasses K` characterized by finite odd defect exponent.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem natCard_unitQuadraticNormSquareClasses_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
  have hb : IsUniformizer K (a * c ^ 2) := by
    apply (isUniformizer_def _).mpr
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd]
    omega
  obtain ⟨π, hπ, hπa⟩ := (isUniformizer_iff_exists_irreducible K (a * c ^ 2)).mp hb
  have hcard : Nat.card (unitQuadraticNormSquareClasses (π : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
    calc
      Nat.card (unitQuadraticNormSquareClasses (π : K)) =
          (unitQuadraticNormSquareClasses (π : K) :
            Set (MultiplicativeSquareClassGroup K)).ncard :=
        Nat.card_coe_set_eq _
      _ = _ := by
        rw [coe_unitQuadraticNormSquareClasses_irreducible hπ]
        exact ncard_range_uniformizerNormSquareClass h2 hπ
  rwa [hπa, Units.val_mul, Units.val_pow_eq_pow_val,
    unitQuadraticNormSquareClasses_mul_sq] at hcard

/-- **Unit-norm square-class count for a radicand of odd quadratic defect.** Over a nonarchimedean
local field with `2 ≠ 0`, any `a : Kˣ` of odd defect exponent `d`, of any valuation, has
`#𝓀[K] ^ natCastValuation K 2 h2` unit-norm square classes. -/
theorem natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases Int.even_or_odd (normalizedValuation K a).toAdd with hev | hv
  · obtain ⟨c, hc, hcd⟩ := exists_defectExponent_mul_sq_eq_sub_of_even_valuation hd hev
    obtain ⟨t, c', ht, hc', -, -, heq⟩ :=
      exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd hc hcd
        (hodd.sub_even hev)
    have hcard : Nat.card (unitQuadraticNormSquareClasses ((a * c ^ 2 : Kˣ) : K)) =
        Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
      rw [heq, natCard_eisensteinNormSquareSubgroup h2 ht hc']
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      unitQuadraticNormSquareClasses_mul_sq] using hcard
  · exact natCard_unitQuadraticNormSquareClasses_of_odd h2 hv

/-- **Index of unit-norm square classes inside `unitSquareClasses K` for odd quadratic defect.**
Over a nonarchimedean local field with `2 ≠ 0`, for any `a : Kˣ` of odd defect exponent `d`,
`unitQuadraticNormSquareClasses (a : K)` has index `2` inside `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 := by
  have hmul := (unitQuadraticNormSquareClasses (a : K)).relIndex_mul_card (unitSquareClasses K)
  rw [inf_of_le_left (unitQuadraticNormSquareClasses_le_unitSquareClasses _),
    natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd,
    card_unitSquareClasses K h2] at hmul
  have hq : 0 < Nat.card 𝓀[K] := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

/-- For a nonsquare `a : Kˣ` of defect exponent `d` over a nonarchimedean local field with `2 ≠ 0`,
every unit square class is represented by a valuation-one norm from `K(√a)` if and only if `d` is
even. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K ↔ Even d := by
  refine ⟨fun heq ↦ ?_, fun hev ↦
    unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_unramified_class
      ((unramified_class_iff_even_defectExponent h2 hd).mpr hev)⟩
  by_contra hnev
  have hidx := relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd
    (Int.not_even_iff_odd.mp hnev)
  rw [heq, Subgroup.relIndex_self] at hidx
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, every unit square class is represented by a
valuation-one norm from `K[√a]` if and only if `a : Kˣ` has no odd finite defect exponent (that is,
`a` is a square or lies in the unramified quadratic square class). -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K ↔
      ∀ d : ℤ, defectExponent a = d → Even d := by
  by_cases ha : IsSquare a
  · refine ⟨fun _ _ hd ↦ ?_, fun _ ↦
      unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_isSquare h2 ha⟩
    rw [defectExponent_eq_top_iff.mpr ha] at hd
    exact absurd hd.symm WithTop.coe_ne_top
  · obtain ⟨d₀, hd₀⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
    rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent h2 hd₀.symm]
    refine ⟨fun hev d hd ↦ ?_, fun h ↦ h d₀ hd₀.symm⟩
    rw [← hd₀, WithTop.coe_inj] at hd
    exact hd ▸ hev

/-- For a nonsquare `a : Kˣ` of defect exponent `d` over a nonarchimedean local field with `2 ≠ 0`,
`unitQuadraticNormSquareClasses (a : K)` has index `2` inside `unitSquareClasses K` if and only if
`d` is odd. -/
theorem relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 ↔ Odd d := by
  refine ⟨fun hidx ↦ ?_, relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd⟩
  rw [← Int.not_even_iff_odd,
    ← unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent h2 hd]
  intro heq
  rw [heq, Subgroup.relIndex_self] at hidx
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, `unitQuadraticNormSquareClasses (a : K)` has
index `2` inside `unitSquareClasses K` if and only if `a : Kˣ` has a finite odd defect exponent. -/
theorem relIndex_unitQuadraticNormSquareClasses_eq_two_iff (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 ↔
      ∃ d : ℤ, defectExponent a = d ∧ Odd d := by
  refine ⟨fun hidx ↦ ?_, fun ⟨d, hd, hodd⟩ ↦
    relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd⟩
  have ha : ¬IsSquare a := by
    intro ha
    rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_isSquare h2 ha,
      Subgroup.relIndex_self] at hidx
    omega
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
  exact ⟨d, hd.symm,
    (relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent h2 hd.symm).mp hidx⟩

end TauCeti
