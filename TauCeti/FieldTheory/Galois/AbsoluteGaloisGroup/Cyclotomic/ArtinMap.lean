/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Cyclotomic value of a local Artin uniformizer

For a finite extension `K/ℚ_p`, the cyclotomic character of the arithmetic Artin symbol of a
uniformizer `ϖ` is the inverse of the unit part of `N_{K/ℚ_p}(ϖ)`. Thus the product of the
character value and the norm is `p` raised to the residue degree. The formula records the
uniformizer contribution to the image of the cyclotomic character, which need not be determined
by the Artin symbols of units.

The comparison uses `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm`
and `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_padic`, with the
normalized valuation of a norm supplying the residue degree.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- If `σ` represents the arithmetic Artin symbol of a uniformizer `ϖ` of `K`, then
`χ_cyc(σ) · N_{K/ℚ_p}(ϖ) = p ^ f(K/ℚ_p)` in `ℚ_pˣ`. -/
theorem localCyclotomicCharacter_artinMap_uniformizer (ϖ : Kˣ)
    (hϖ : IsUniformizer K ϖ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = ClassFieldTheory.artinMap K ϖ) :
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (localCyclotomicCharacter p K σ) *
        Algebra.normUnits ℚ_[p] ϖ =
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ^
        inertiaDegree ℚ_[p] K := by
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsSeparable ℚ_[p] K :=
    (inferInstance : Algebra.IsAlgebraic ℚ_[p] K).isSeparable_of_perfectField
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hval : (Algebra.normUnits ℚ_[p] ϖ : ℚ_[p]).valuation =
      (inertiaDegree ℚ_[p] K : ℤ) := by
    rw [← _root_.Padic.toAdd_normalizedValuation_eq_valuation,
      toAdd_normalizedValuation_norm, (isUniformizer_def ϖ).mp hϖ]
    simp
  obtain ⟨u, hu⟩ := _root_.Padic.exists_eq_zpow_valuation_mul
    (Units.ne_zero (Algebra.normUnits ℚ_[p] ϖ))
  have hu' : (Algebra.normUnits ℚ_[p] ϖ : ℚ_[p]) = (p : ℚ_[p]) ^
      (inertiaDegree ℚ_[p] K : ℤ) * u := by rwa [hval] at hu
  have hχ : localCyclotomicCharacter p K σ = u⁻¹ := by
    rw [← abelianizedLocalCyclotomicCharacter_mk, hσ,
      ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm ℚ_[p] p]
    exact ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_padic p hu'
  have hnorm : Algebra.normUnits ℚ_[p] ϖ =
      (Units.mk0 (p : ℚ_[p]) hp0) ^ inertiaDegree ℚ_[p] K *
        Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u := by
    apply Units.ext
    simpa [zpow_natCast] using hu'
  rw [hχ, hnorm, map_inv]
  simp

end TauCeti
