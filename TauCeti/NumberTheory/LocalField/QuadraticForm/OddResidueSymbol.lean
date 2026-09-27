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
import TauCeti.NumberTheory.LocalField.NatCastValuation
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

noncomputable local instance : Fintype 𝓀[K] := Fintype.ofFinite _

open Classical in
/-- The symbol of a unit and a uniformizer is positive exactly when the unit has square residue.
This is the unit–uniformizer entry of the Hilbert-symbol table in odd residue characteristic. -/
theorem hilbertSymbol_unit_uniformizer_eq_ite (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {π : Kˣ} (hπ : IsUniformizer K π) :
    hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) π =
      if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1 := by
  classical
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  let uK := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u
  have hsq : IsSquare uK ↔
      IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) :=
    isSquare_unitsMap_subtype_iff h2 u
  by_cases hu : IsSquare uK
  · simp only [(hsq.mp hu), ↓reduceIte]
    exact hilbertSymbol_eq_one_of_isSquare_left hu π
  · obtain ⟨Δ, hΔsq, hΔval, hΔ⟩ := exists_unramified_class (two_ne_zero_of_isUnit_two h2)
    have hΔeven : Even (normalizedValuation K Δ).toAdd := by
      rw [hΔval]
      exact ⟨0, by simp⟩
    have huval : Even (normalizedValuation K uK).toAdd := by
      rw [normalizedValuation_integerUnits]
      exact ⟨0, by simp⟩
    have husq : IsSquare (uK * Δ) :=
      (isSquare_or_isSquare_mul_of_isUnit_two h2 hΔeven hΔsq huval).resolve_left hu
    have hπodd : ¬ Even (normalizedValuation K π).toAdd := by
      rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
      exact Int.not_even_one
    have hsym : hilbertSymbol uK π = -1 := by
      rw [hilbertSymbol_congr_sq uK Δ π π husq ⟨π, rfl⟩,
        hilbertSymbol_unramified hΔ π]
      simp [hπodd]
    simpa only [(hsq.not.mp hu), ↓reduceIte] using hsym

open Classical in
/-- The unit–uniformizer symbol equals the quadratic residue character of the reduced unit. -/
theorem hilbertSymbol_unit_uniformizer_eq_quadraticChar (h2 : IsUnit (2 : 𝒪[K]))
    (u : 𝒪[K]ˣ) {π : Kˣ} (hπ : IsUniformizer K π) :
    ((hilbertSymbol (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) π : ℤˣ) : ℤ) =
      quadraticChar 𝓀[K] ((Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u : 𝓀[K]ˣ) : 𝓀[K]) := by
  classical
  rw [hilbertSymbol_unit_uniformizer_eq_ite h2 u hπ]
  simp only [quadraticChar_apply, quadraticCharFun, Units.ne_zero, ↓reduceIte]
  simp only [← isSquare_units_val_iff]
  split_ifs <;> simp

end TauCeti
