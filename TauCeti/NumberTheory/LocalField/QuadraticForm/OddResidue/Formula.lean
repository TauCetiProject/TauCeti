/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Symbol
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

open _root_.TauCeti.Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

attribute [local instance] instFintypeResidueField

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
  have h2' : (2 : K) ≠ 0 := two_ne_zero_of_isUnit_two h2
  rw [hilbertSymbol_mul_left h2', hilbertSymbol_mul_right h2',
    hilbertSymbol_mul_right h2', hilbertSymbol_zpow_left h2',
    hilbertSymbol_zpow_right h2', hilbertSymbol_zpow_right h2',
    hilbertSymbol_zpow_left h2', huv]
  rw [← zpow_mul, hilbertSymbol_uniformizer_self h2 hπ,
    oddResidueSign_neg_one h2]
  have hpu : hilbertSymbol (i u) π = oddResidueSign u :=
    (oddResidueSign_eq_hilbertSymbol h2 u hπ).symm
  have hpv : hilbertSymbol π (i v) = oddResidueSign v := by
    have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    rw [hilbertSymbol_comm]
    exact (oddResidueSign_eq_hilbertSymbol h2 v hπ).symm
  rw [hpu, hpv]
  simp only [mul_one, mul_comm α β]
  ac_rfl

end TauCeti
