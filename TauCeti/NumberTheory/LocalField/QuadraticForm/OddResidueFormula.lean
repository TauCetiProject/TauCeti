/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidueSymbol
import TauCeti.NumberTheory.HilbertSymbol.Henselian
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The Hilbert symbol in odd residue characteristic

For a uniformizer `π`, every nonzero element of a nonarchimedean local field has a unique
expression `π ^ n * u` with `u` an integral unit. Bilinearity reduces the Hilbert symbol
of two such elements to the unit–unit, unit–uniformizer, and uniformizer–uniformizer values.
The first is one, while the last equals the unit–uniformizer value at `-1`. Thus the
formula below computes the symbol from the quadratic characters of three residue classes.

This is the odd-residue-characteristic formula of Serre, *A Course in Arithmetic*,
Chapter III, §1, Theorem 1, with the residue character expressed as a sign on units.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

noncomputable local instance : Fintype 𝓀[K] := Fintype.ofFinite _

/-- The sign of the quadratic character of the reduction of an integral unit. -/
noncomputable def oddResidueSign (u : 𝒪[K]ˣ) : ℤˣ :=
  by
    classical
    exact if IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) then 1 else -1

/-- The sign is one exactly when the reduced unit is a square. -/
theorem oddResidueSign_eq_one_iff (u : 𝒪[K]ˣ) :
    oddResidueSign u = 1 ↔
      IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) := by
  classical
  simp [oddResidueSign]

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
/-- As an integer, the residue sign is the usual quadratic character. -/
theorem oddResidueSign_int (h2 : IsUnit (2 : 𝒪[K])) (u : 𝒪[K]ˣ) :
    ((oddResidueSign u : ℤˣ) : ℤ) =
      quadraticChar 𝓀[K] ((Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u : 𝓀[K]ˣ) :
        𝓀[K]) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  rw [oddResidueSign_eq_hilbertSymbol h2 u hπ]
  exact hilbertSymbol_unit_uniformizer_eq_quadraticChar h2 u hπ

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
  rw [oddResidueSign_int h2]
  have hr : Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) (-1 : 𝒪[K]ˣ) =
      (-1 : 𝓀[K]ˣ) := by simp
  rw [hr]
  simp only [Units.val_neg, Units.val_one]
  rw [quadraticChar_neg_one hchar, ZMod.χ₄_eq_neg_one_pow hodd]
  congr 1
  omega

/-- The Hilbert symbol is multiplicative on integer powers of its second argument. -/
theorem hilbertSymbol_zpow_right (h2 : IsUnit (2 : 𝒪[K]))
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol a (b ^ n) = hilbertSymbol a b ^ n := by
  let f : Kˣ →* ℤˣ :=
    { toFun := hilbertSymbol a
      map_one' := hilbertSymbol_one_right a
      map_mul' := hilbertSymbol_mul_right h2 a }
  exact map_zpow f b n

/-- The Hilbert symbol is multiplicative on integer powers of its first argument. -/
theorem hilbertSymbol_zpow_left (h2 : IsUnit (2 : 𝒪[K]))
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol (a ^ n) b = hilbertSymbol a b ^ n := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [hilbertSymbol_comm, hilbertSymbol_zpow_right h2, hilbertSymbol_comm]

/-- The diagonal uniformizer value is the residue sign of `-1`. -/
theorem hilbertSymbol_uniformizer_self (h2 : IsUnit (2 : 𝒪[K]))
    {π : Kˣ} (hπ : IsUniformizer K π) :
    hilbertSymbol π π = oddResidueSign (-1 : 𝒪[K]ˣ) := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [hilbertSymbol_self, hilbertSymbol_comm]
  simpa using (oddResidueSign_eq_hilbertSymbol h2 (-1 : 𝒪[K]ˣ) hπ).symm

/-- Serre's formula in odd residue characteristic: the Hilbert symbol of
`π ^ α * u` and `π ^ β * v` is determined by the residue signs of `-1`, `u`, and `v`. -/
theorem hilbertSymbol_oddResidue_formula (h2 : IsUnit (2 : 𝒪[K]))
    {π : Kˣ} (hπ : IsUniformizer K π) (α β : ℤ) (u v : 𝒪[K]ˣ) :
    hilbertSymbol
        (π ^ α * Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u)
        (π ^ β * Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) v) =
      ((-1 : ℤˣ) ^ ((Fintype.card 𝓀[K] - 1) / 2)) ^ (α * β) *
        oddResidueSign u ^ β * oddResidueSign v ^ α := by
  let i : 𝒪[K]ˣ → Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)
  have huv : hilbertSymbol (i u) (i v) = 1 :=
    hilbertSymbol_units_map_eq_one h2 u v
  rw [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2,
    hilbertSymbol_mul_right h2, hilbertSymbol_zpow_left h2,
    hilbertSymbol_zpow_right h2, hilbertSymbol_zpow_right h2,
    hilbertSymbol_zpow_left h2, huv]
  rw [← zpow_mul, hilbertSymbol_uniformizer_self h2 hπ,
    oddResidueSign_neg_one h2]
  have hpu : hilbertSymbol (i u) π = oddResidueSign u :=
    (oddResidueSign_eq_hilbertSymbol h2 u hπ).symm
  have hpv : hilbertSymbol π (i v) = oddResidueSign v := by
    have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    rw [hilbertSymbol_comm]
    exact (oddResidueSign_eq_hilbertSymbol h2 v hπ).symm
  rw [hpu, hpv]
  simp [mul_comm, mul_left_comm]

end TauCeti
