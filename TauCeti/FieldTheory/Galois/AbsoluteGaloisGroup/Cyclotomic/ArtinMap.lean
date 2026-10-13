/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-!
# The local cyclotomic character on Artin symbols of units

For a finite extension `K/ℚ_p`, local reciprocity is normalized so that a uniformizer maps to
arithmetic Frobenius. With this normalization, the local cyclotomic character on the Artin symbol
of a unit `u` is the inverse of its norm:

```text
χ_cyc(Art_K(u)) = N_{K/ℚ_p}(u)⁻¹.
```

The results in this file express the explicit reciprocity comparison
`ClassFieldTheory.cyclotomicCharacter_artinMap` in terms of
`TauCeti.localCyclotomicCharacter`. The specialization to `ℚ_p` records that the norm is the
identity there. These equalities fix both the arithmetic-Frobenius convention and the inverse
appearing in marked local Galois presentations.

## Main results

* `TauCeti.localCyclotomicCharacter_artinMap_unit`: the value at a unit of a finite extension of
  `ℚ_p`.
* `TauCeti.localCyclotomicCharacter_artinMap_padic`: the specialization to `ℚ_p`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- If `σ` represents the arithmetic Artin symbol of a unit `u` in a finite extension `K/ℚ_p`,
then its local cyclotomic character is the inverse of the norm of `u`. -/
theorem localCyclotomicCharacter_artinMap_unit (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
    [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
    (u : Kˣ) (hu : ValuativeRel.valuation K (u : K) = 1)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) =
      ClassFieldTheory.artinMap K u) :
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (localCyclotomicCharacter p K σ) =
      (Units.map (Algebra.norm ℚ_[p] : K →* ℚ_[p]) u)⁻¹ := by
  rw [localCyclotomicCharacter_apply]
  exact ClassFieldTheory.cyclotomicCharacter_artinMap p K u hu σ hσ

/-- If `σ` represents the arithmetic Artin symbol of `u ∈ ℤ_pˣ`, then its local cyclotomic
character is `u⁻¹`. -/
theorem localCyclotomicCharacter_artinMap_padic [IsNonarchimedeanLocalField ℚ_[p]]
    (u : ℤ_[p]ˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      ClassFieldTheory.artinMap ℚ_[p]
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    localCyclotomicCharacter p ℚ_[p] σ = u⁻¹ := by
  rw [localCyclotomicCharacter_apply]
  exact ClassFieldTheory.cyclotomicCharacter_artinMap_padic p u σ hσ

end TauCeti
