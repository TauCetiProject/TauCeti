/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.NumberTheory.LocalField.Uniformizer

import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.NumberTheory.LocalField.PowerSubgroup

/-!
# Square classes of a local field with odd residue characteristic

When two is invertible in the ring of integers of a nonarchimedean local field, its four square
classes are represented by `1`, a unit with nonsquare residue, a uniformizer, and their product.
This description supplies the coordinates used to compute the Hilbert symbol in odd residue
characteristic. The residue square test and the count of four square classes come from the local
field power subgroup theory.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63, for local square classes and the
  Hilbert symbol.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem normalizedValuation_even_of_isSquare {a : Kˣ} (ha : IsSquare a) :
    Even (normalizedValuation K a).toAdd := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨(normalizedValuation K b).toAdd, ?_⟩
  simp

/-- At odd residue characteristic there is an integer unit whose residue is nonsquare. -/
theorem exists_integerUnit_not_isSquare_residue (h2 : IsUnit (2 : 𝒪[K])) :
    ∃ u : 𝒪[K]ˣ, ¬IsSquare (Units.map ((residue 𝒪[K] : 𝒪[K] →+* 𝓀[K]).toMonoidHom) u) := by
  have h2res : (2 : 𝓀[K]) ≠ 0 := by
    exact_mod_cast (h2.map (residue 𝒪[K])).ne_zero
  have hchar : ringChar 𝓀[K] ≠ 2 := by
    intro hc
    exact h2res (by exact_mod_cast hc ▸ ringChar.Nat.cast_ringChar)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := fun h => ha (h ▸ by simp)
  let aunit : 𝓀[K]ˣ := Units.mk0 a ha0
  obtain ⟨u, hu⟩ := surjective_units_map_of_local_ringHom
    (residue 𝒪[K]) residue_surjective inferInstance aunit
  refine ⟨u, ?_⟩
  intro hs
  apply ha
  have hs' : IsSquare aunit := by simpa only [hu] using hs
  exact (isSquare_units_val_iff).mpr hs'

/-- A uniformizer has nonsquare class: its normalized valuation is odd. -/
theorem not_isSquare_uniformizer {π : Kˣ} (hπ : IsUniformizer (K := K) π) :
    ¬IsSquare π := by
  intro hs
  obtain ⟨n, hn⟩ := normalizedValuation_even_of_isSquare hs
  have hp : (normalizedValuation K π).toAdd = 1 := by
    rw [isUniformizer_def] at hπ
    simp [hπ]
  omega

/-- Multiplying an integer unit by a uniformizer gives another nonsquare class. -/
theorem not_isSquare_integerUnit_mul_uniformizer (u : 𝒪[K]ˣ) {π : Kˣ}
    (hπ : IsUniformizer (K := K) π) :
    ¬IsSquare (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u * π) := by
  intro hs
  obtain ⟨n, hn⟩ := normalizedValuation_even_of_isSquare hs
  have hu : normalizedValuation K
      (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u) = 1 :=
    normalizedValuation_integerUnits u
  have hp : (normalizedValuation K π).toAdd = 1 := by
    rw [isUniformizer_def] at hπ
    simp [hπ]
  simp only [map_mul, hu, one_mul] at hn
  omega

/-- **The four square classes at odd residue characteristic.** If `u` has nonsquare
residue and `π` is any uniformizer, the classes of `1`, `u`, `π`, and `uπ` exhaust the
square-class group. -/
theorem squareClass_eq_representative_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) (u : 𝒪[K]ˣ)
    (hu : ¬IsSquare (Units.map ((residue 𝒪[K] : 𝒪[K] →+* 𝓀[K]).toMonoidHom) u))
    {π : Kˣ} (hπ : IsUniformizer (K := K) π) (a : Kˣ) :
    squareClass a = 0 ∨
      squareClass a = squareClass
        (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u) ∨
      squareClass a = squareClass π ∨
      squareClass a = squareClass
        (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u * π) := by
  classical
  let uK : Kˣ := Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u
  have hu0 : squareClass uK ≠ 0 := by
    rw [ne_eq, squareClass_eq_zero_iff]
    exact (isSquare_unitsMap_subtype_iff h2 u).not.mpr hu
  have hp0 : squareClass π ≠ 0 := by
    rw [ne_eq, squareClass_eq_zero_iff]
    exact not_isSquare_uniformizer hπ
  have hup0 : squareClass (uK * π) ≠ 0 := by
    rw [ne_eq, squareClass_eq_zero_iff]
    exact not_isSquare_integerUnit_mul_uniformizer u hπ
  have hup : squareClass uK ≠ squareClass π := by
    intro h
    exact not_isSquare_integerUnit_mul_uniformizer u hπ
      ((squareClass_eq_iff_isSquare_mul uK π).mp h)
  have hupu : squareClass (uK * π) ≠ squareClass uK := by
    intro h
    rw [squareClass_mul] at h
    have hh := congrArg (fun z : SquareClassGroup K => z - squareClass uK) h
    exact hp0 (by simpa [add_comm] using hh)
  have hupp : squareClass (uK * π) ≠ squareClass π := by
    intro h
    rw [squareClass_mul] at h
    have hh := congrArg (fun z : SquareClassGroup K => z - squareClass π) h
    exact hu0 (by simpa using hh)
  -- These four distinct classes exhaust the square-class group, whose order is four.
  have : (Subgroup.square Kˣ).FiniteIndex := by
    rw [square_eq_powMonoidHom_two_range]
    exact finiteIndex_range_powMonoidHom_of_isUnit h2
  have : Finite (SquareClassGroup K) :=
    finite_multiplicativeSquareClassGroup_iff.mp
      (Subgroup.finiteIndex_iff_finite_quotient.mp inferInstance)
  let _ := Fintype.ofFinite (SquareClassGroup K)
  have hcard : Fintype.card (SquareClassGroup K) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← natCard_multiplicativeSquareClassGroup]
    simpa only [MultiplicativeSquareClassGroup, square_eq_powMonoidHom_two_range] using
      card_squareClasses_of_isUnit (K := K) h2
  let s : Finset (SquareClassGroup K) :=
    {0, squareClass uK, squareClass π, squareClass (uK * π)}
  have hs : s.card = 4 := by
    exact Finset.card_eq_four.mpr ⟨0, squareClass uK, squareClass π,
      squareClass (uK * π), hu0.symm, hp0.symm, hup0.symm, hup,
      hupu.symm, hupp.symm, rfl⟩
  have hsu : s = Finset.univ := Finset.eq_univ_of_card s (hs.trans hcard.symm)
  have hmem : squareClass a ∈ s := by rw [hsu]; simp
  simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hmem

/-- At odd residue characteristic, every uniformizer admits a unit with nonsquare residue
giving representatives for all four square classes. -/
theorem exists_squareClass_representatives_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K]))
    {π : Kˣ} (hπ : IsUniformizer (K := K) π) :
    ∃ u : 𝒪[K]ˣ,
      ¬IsSquare (Units.map ((residue 𝒪[K] : 𝒪[K] →+* 𝓀[K]).toMonoidHom) u) ∧
      (∀ a : Kˣ, squareClass a = 0 ∨
        squareClass a = squareClass
          (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u) ∨
        squareClass a = squareClass π ∨
        squareClass a = squareClass
          (Units.map ((Subring.subtype 𝒪[K] : 𝒪[K] →+* K).toMonoidHom) u * π)) := by
  classical
  obtain ⟨u, hu⟩ := exists_integerUnit_not_isSquare_residue h2
  exact ⟨u, hu, squareClass_eq_representative_of_isUnit_two h2 u hu hπ⟩

end TauCeti
