/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.RamificationIndex

/-!
# The absolute ramification index of a mixed-characteristic local field

Let `p` be prime and let `K` be a nonarchimedean local field carrying a `ℚ_[p]`-algebra
structure. This file defines the absolute ramification index

`TauCeti.absoluteRamificationIndex K p = e(K/ℚ_[p])`.

For a compatible extension, its characteristic calculation identifies it with the normalized
valuation of `p` in `K`. Consequently the index of `ℚ_[p]` itself is one, and in a tower over
`ℚ_[p]` the absolute index is multiplied by the relative ramification index.

The definition is confined to mixed characteristic by requiring an algebra structure over
`ℚ_[p]`; there is no artificial value for equal-characteristic local fields.

## Main definitions

* `TauCeti.absoluteRamificationIndex`: the ramification index of `K/ℚ_[p]`.

## Main results

* `TauCeti.absoluteRamificationIndex_eq_natCastValuation`: the absolute ramification index is
  the normalized valuation of `p` in `K`.
* `TauCeti.absoluteRamificationIndex_padic`: the absolute ramification index of `ℚ_[p]` is one.
* `TauCeti.absoluteRamificationIndex_tower`: the absolute index is multiplicative in a tower.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- The absolute ramification index of a nonarchimedean local field over `ℚ_[p]`.

For a finite compatible extension, this is the classical absolute ramification index. -/
def absoluteRamificationIndex (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] : ℕ :=
  ramificationIndex ℚ_[p] K

omit [ValuativeExtension ℚ_[p] K] in
/-- The absolute ramification index is the ramification index over `ℚ_[p]`. -/
theorem absoluteRamificationIndex_def :
    absoluteRamificationIndex K p = ramificationIndex ℚ_[p] K := by
  rw [absoluteRamificationIndex]

/-- The absolute ramification index is the normalized valuation of the residue prime `p` in
`K`. -/
@[simp]
theorem absoluteRamificationIndex_eq_natCastValuation :
    absoluteRamificationIndex K p = natCastValuation K p
      (by
        simpa only [map_natCast] using
          (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
            (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℚ_[p]) ≠ 0)) := by
  rw [absoluteRamificationIndex_def]
  let hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let hpK : (p : K) ≠ 0 :=
    by simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr hp
  have hmap : Units.map (algebraMap ℚ_[p] K : ℚ_[p] →* K) (Units.mk0 (p : ℚ_[p]) hp) =
      Units.mk0 (p : K) hpK := by
    ext
    simp
  have h := toAdd_normalizedValuation_algebraMap (K := ℚ_[p]) (L := K)
    (Units.mk0 (p : ℚ_[p]) hp)
  rw [hmap, normalizedValuation_natCast K p hpK,
    normalizedValuation_natCast ℚ_[p] p hp, Padic.natCastValuation_self] at h
  simpa using h.symm

/-- The absolute ramification index of `ℚ_[p]` is one. -/
theorem absoluteRamificationIndex_padic : absoluteRamificationIndex ℚ_[p] p = 1 := by
  rw [absoluteRamificationIndex_eq_natCastValuation, Padic.natCastValuation_self]

/-- In a tower `L/K/ℚ_[p]`, the absolute ramification index of `L` is the product of the
relative ramification index of `L/K` and the absolute ramification index of `K`. -/
theorem absoluteRamificationIndex_tower (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [Algebra ℚ_[p] L]
    [IsScalarTower ℚ_[p] K L] [ValuativeExtension K L] :
    absoluteRamificationIndex L p =
      ramificationIndex K L * absoluteRamificationIndex K p := by
  simpa only [absoluteRamificationIndex_def, Nat.mul_comm] using
    ramificationIndex_tower (K := ℚ_[p]) (L := K) L

end TauCeti
