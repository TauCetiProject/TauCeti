/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
public import TauCeti.NumberTheory.LocalField.SquareClass
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.LocalField.PowerSubgroup
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddValuation
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.Algebra.Group.Units.Basic

/-!
# The Hilbert symbol of a unit and a uniformizer

Over a nonarchimedean local field of odd residue characteristic, the Hilbert symbol of an
integral unit and a uniformizer is the quadratic character of the unit's residue. The
unramified quadratic class detects the nonsquare residue class, while squares have positive
symbol. This calculation is one of the three values determining the local symbol on square
classes.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:11.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The residue field is finite for the quadratic character calculation. -/
noncomputable local instance instFintypeResidueField : Fintype 𝓀[K] := Fintype.ofFinite _

open Classical in
/-- The symbol of a unit and an element of odd valuation is positive exactly when the unit has
square residue, in odd residue characteristic. -/
theorem hilbertSymbol_unit_eq_ite_of_odd (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {b : Kˣ} (hb : Odd (normalizedValuation K b).toAdd) :
    hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) b =
      if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1 := by
  classical
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  let uK := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u
  have hsq : IsSquare uK ↔
      IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) :=
    isSquare_unitsMap_subtype_iff h2 u
  by_cases hu : IsSquare uK
  · simp only [(hsq.mp hu), ↓reduceIte]
    exact hilbertSymbol_eq_one_of_isSquare_left hu b
  · obtain ⟨Δ, hΔsq, hΔval, hΔ⟩ := exists_unramified_class (two_ne_zero_of_isUnit_two h2)
    have hΔeven : Even (normalizedValuation K Δ).toAdd := by
      rw [hΔval]
      exact ⟨0, by simp⟩
    have huval : Even (normalizedValuation K uK).toAdd := by
      rw [normalizedValuation_integerUnits]
      exact ⟨0, by simp⟩
    have husq : IsSquare (uK * Δ) :=
      (isSquare_or_isSquare_mul_of_isUnit_two h2 hΔeven hΔsq huval).resolve_left hu
    have hsym : hilbertSymbol uK b = -1 := by
      rw [hilbertSymbol_congr_sq uK Δ b b husq ⟨b, rfl⟩]
      exact (hilbertSymbol_comm Δ b).trans
        (hilbertSymbol_eq_neg_one_of_unramified_class_of_odd
          (two_ne_zero_of_isUnit_two h2) hΔ hb)
    simpa only [(hsq.not.mp hu), ↓reduceIte] using hsym

open Classical in
/-- The unit–odd-valuation symbol equals the quadratic residue character of the reduced unit. -/
theorem hilbertSymbol_unit_eq_quadraticChar_of_odd (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {b : Kˣ} (hb : Odd (normalizedValuation K b).toAdd) :
    ((hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) b : ℤˣ) : ℤ) =
      quadraticChar 𝓀[K] ((Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u : 𝓀[K]ˣ) : 𝓀[K]) := by
  classical
  rw [hilbertSymbol_unit_eq_ite_of_odd h2 u hb]
  by_cases hs : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u)
  · simp only [hs, ↓reduceIte]
    exact ((quadraticChar_one_iff_isSquare (Units.ne_zero _)).mpr
      (isSquare_units_val_iff.mpr hs)).symm
  · simp only [hs, ↓reduceIte]
    exact (quadraticChar_neg_one_iff_not_isSquare.mpr
      (isSquare_units_val_iff.not.mpr hs)).symm

open Classical in
/-- The symbol of a unit and a uniformizer is positive exactly when the unit has square residue.
This is the unit–uniformizer entry of the Hilbert-symbol table in odd residue characteristic. -/
theorem hilbertSymbol_unit_uniformizer_eq_ite (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {π : Kˣ} (hπ : IsUniformizer K π) :
    hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) π =
      if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1 := by
  apply hilbertSymbol_unit_eq_ite_of_odd h2 u
  rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
  exact odd_one

open Classical in
/-- The unit–uniformizer symbol equals the quadratic residue character of the reduced unit. -/
theorem hilbertSymbol_unit_uniformizer_eq_quadraticChar (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {π : Kˣ} (hπ : IsUniformizer K π) :
    ((hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) π : ℤˣ) : ℤ) =
      quadraticChar 𝓀[K] ((Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u : 𝓀[K]ˣ) : 𝓀[K]) := by
  apply hilbertSymbol_unit_eq_quadraticChar_of_odd h2 u
  rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
  exact odd_one

open Classical in
/-- For a valuation-zero element of `Kˣ`, the unit–uniformizer symbol is positive exactly
when that element is a square, in odd residue characteristic. -/
theorem hilbertSymbol_eq_one_iff_isSquare_of_valuation_zero_of_isUniformizer
    (h2 : IsUnit (2 : 𝒪[K])) {u π : Kˣ}
    (hu : (normalizedValuation K u).toAdd = 0) (hπ : IsUniformizer K π) :
    hilbertSymbol u π = 1 ↔ IsSquare u := by
  have hu0 : u ∈ unitFiltration K 0 := by
    apply (mem_unitFiltration_zero u).mpr
    apply (normalizedValuation_eq_one_iff u).mp
    exact Multiplicative.toAdd.injective (by simpa using hu)
  let v : 𝒪[K]ˣ := unitFiltrationZeroEquivIntegerUnits ⟨u, hu0⟩
  have hv : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) v = u := by
    apply Units.ext
    simp [v]
  rw [← hv, hilbertSymbol_unit_uniformizer_eq_ite h2 v hπ,
    isSquare_unitsMap_subtype_iff h2 v]
  by_cases hs : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) v) <;> simp [hs]

namespace Units

/-- The sign of the quadratic character of the reduction of an integral unit. -/
noncomputable def oddResidueSign (u : 𝒪[K]ˣ) : ℤˣ := by
  classical
  exact if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1

/-- The sign is one exactly when the reduced unit is a square. -/
theorem oddResidueSign_eq_one_iff (u : 𝒪[K]ˣ) :
    oddResidueSign u = 1 ↔
      IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) := by
  classical
  simp [oddResidueSign]

open Classical in
/-- As an integer, the residue sign is the usual quadratic character. -/
theorem oddResidueSign_int (u : 𝒪[K]ˣ) :
    ((oddResidueSign u : ℤˣ) : ℤ) =
      quadraticChar 𝓀[K] ((Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u : 𝓀[K]ˣ) :
        𝓀[K]) := by
  classical
  by_cases hs : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u)
  · simp only [oddResidueSign, hs, ↓reduceIte, Units.val_one]
    exact ((quadraticChar_one_iff_isSquare (Units.ne_zero _)).mpr
      (isSquare_units_val_iff.mpr hs)).symm
  · simp only [oddResidueSign, hs, ↓reduceIte, Units.val_neg, Units.val_one]
    exact (quadraticChar_neg_one_iff_not_isSquare.mpr
      (isSquare_units_val_iff.not.mpr hs)).symm

/-- The residue sign is multiplicative on integral units. -/
@[simp]
theorem oddResidueSign_mul (u v : 𝒪[K]ˣ) :
    oddResidueSign (u * v) = oddResidueSign u * oddResidueSign v := by
  classical
  apply Units.ext
  rw [oddResidueSign_int, Units.val_mul, oddResidueSign_int, oddResidueSign_int]
  simp only [map_mul, Units.val_mul]

/-- The residue sign of one is one. -/
@[simp] theorem oddResidueSign_one : oddResidueSign (1 : 𝒪[K]ˣ) = 1 := by
  classical
  simp [oddResidueSign]

/-- The residue sign of an inverse is the inverse sign. -/
@[simp]
theorem oddResidueSign_inv (u : 𝒪[K]ˣ) :
    oddResidueSign u⁻¹ = (oddResidueSign u)⁻¹ := by
  have h := oddResidueSign_mul u u⁻¹
  rw [mul_inv_cancel, oddResidueSign_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The residue sign of an integer power is the corresponding power of the sign. -/
@[simp]
theorem oddResidueSign_zpow (u : 𝒪[K]ˣ) (n : ℤ) :
    oddResidueSign (u ^ n) = oddResidueSign u ^ n := by
  let f : 𝒪[K]ˣ →* ℤˣ :=
    { toFun := oddResidueSign
      map_one' := oddResidueSign_one
      map_mul' := oddResidueSign_mul }
  exact map_zpow f u n

end Units

open _root_.TauCeti.Units

/-- The sign is the Hilbert symbol against any uniformizer. -/
theorem oddResidueSign_eq_hilbertSymbol (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {π : Kˣ} (hπ : IsUniformizer K π) :
    oddResidueSign u =
      hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) π := by
  classical
  by_cases hs : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u)
  · rw [hilbertSymbol_unit_uniformizer_eq_ite h2 u hπ]
    simp [oddResidueSign, hs]
  · rw [hilbertSymbol_unit_uniformizer_eq_ite h2 u hπ]
    simp [oddResidueSign, hs]

open Classical in
/-- The uniformizer diagonal sign is `(-1)^((q-1)/2)`, where `q` is the residue cardinality. -/
theorem oddResidueSign_neg_one (h2 : IsUnit (2 : 𝒪[K])) :
    oddResidueSign (-1 : 𝒪[K]ˣ) =
      (-1 : ℤˣ) ^ ((Fintype.card 𝓀[K] - 1) / 2) := by
  have h2res : (2 : 𝓀[K]) ≠ 0 := by
    exact_mod_cast (h2.map (residue 𝒪[K])).ne_zero
  have hchar : ringChar 𝓀[K] ≠ 2 := by
    intro hc
    exact h2res (by exact_mod_cast hc ▸ ringChar.Nat.cast_ringChar)
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  apply Units.ext
  rw [oddResidueSign_int]
  have hr : Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) (-1 : 𝒪[K]ˣ) =
      (-1 : 𝓀[K]ˣ) := by simp
  rw [hr]
  simp only [Units.val_neg, Units.val_one]
  rw [quadraticChar_neg_one hchar, ZMod.χ₄_eq_neg_one_pow hodd]
  congr 1
  omega

end TauCeti
