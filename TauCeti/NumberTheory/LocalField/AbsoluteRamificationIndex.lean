/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# The absolute ramification index of a mixed-characteristic local field

Let `p` be prime and let `K` be a nonarchimedean local field carrying the structure of a finite
compatible extension of `ℚ_[p]`. This file defines the absolute ramification index

`TauCeti.absoluteRamificationIndex K p = e(K/ℚ_[p])`.

For a compatible extension, its characteristic calculation identifies it with the normalized
valuation of `p` in `K`. Consequently the index of `ℚ_[p]` itself is one, and in a tower over
`ℚ_[p]` the absolute index is multiplied by the relative ramification index.

The definition is confined to mixed characteristic by requiring an algebra structure over
`ℚ_[p]`; there is no artificial value for equal-characteristic local fields.

## Main definitions

* `TauCeti.FinitePadicExtension`: a bundled finite compatible extension structure over `ℚ_[p]`.
* `TauCeti.absoluteRamificationIndex`: the ramification index of `K/ℚ_[p]`.

## Main results

* `TauCeti.absoluteRamificationIndex_pos`: the absolute ramification index is positive.
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

/-- A nonarchimedean local field equipped as a finite compatible extension of `ℚ_[p]`.

The algebra structure is bundled so that the finiteness and compatibility conditions constrain
the domain of `absoluteRamificationIndex` without becoming unused arguments of its definition. -/
class FinitePadicExtension (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] where
  /-- The `ℚ_[p]`-algebra structure on the extension. -/
  algebra : Algebra ℚ_[p] K
  /-- The extension has finite degree over `ℚ_[p]`. -/
  [toModuleFinite : letI := algebra; Module.Finite ℚ_[p] K]
  /-- The algebra map is compatible with the valuative relations. -/
  [toValuativeExtension : letI := algebra; ValuativeExtension ℚ_[p] K]

namespace FinitePadicExtension

attribute [instance] toModuleFinite toValuativeExtension

@[instance_reducible]
instance toAlgebra (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [h : FinitePadicExtension K p] :
    Algebra ℚ_[p] K := h.algebra

/-- Package existing finite compatible extension instances as a `FinitePadicExtension`. -/
instance ofInstances (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K]
    [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K] : FinitePadicExtension K p where
  algebra := inferInstance
  toModuleFinite := inferInstance
  toValuativeExtension := inferInstance

end FinitePadicExtension

instance finitePadicExtensionPadic (p : ℕ) [Fact p.Prime] :
    FinitePadicExtension ℚ_[p] p where
  algebra := inferInstance
  toModuleFinite := inferInstance
  toValuativeExtension := ⟨fun a b ↦ by simp⟩

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The absolute ramification index of a finite compatible extension of `ℚ_[p]`. -/
def absoluteRamificationIndex (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] : ℕ :=
  ramificationIndex ℚ_[p] K

/-- The absolute ramification index is positive. -/
theorem absoluteRamificationIndex_pos : 0 < absoluteRamificationIndex K p := by
  exact ramificationIndex_pos (K := ℚ_[p]) (L := K)

/-- The absolute ramification index is the normalized valuation of the residue prime `p` in
`K`. -/
@[simp]
theorem absoluteRamificationIndex_eq_natCastValuation :
    absoluteRamificationIndex K p = natCastValuation K p
      (by
        simpa only [map_natCast] using
          (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
            (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℚ_[p]) ≠ 0)) := by
  rw [absoluteRamificationIndex]
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
-- Not `@[simp]`: the preceding comparison and the p-adic valuation API already simplify this
-- statement, so `simpNF` rejects the redundant attribute.
theorem absoluteRamificationIndex_padic : absoluteRamificationIndex ℚ_[p] p = 1 := by
  rw [absoluteRamificationIndex_eq_natCastValuation, Padic.natCastValuation_self]

/-- In a tower `L/K/ℚ_[p]`, the absolute ramification index of `L` is the product of the
relative ramification index of `L/K` and the absolute ramification index of `K`. -/
theorem absoluteRamificationIndex_tower (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [FinitePadicExtension L p] [Algebra K L]
    [IsScalarTower ℚ_[p] K L] [ValuativeExtension K L] :
    absoluteRamificationIndex L p =
      ramificationIndex K L * absoluteRamificationIndex K p := by
  simpa only [absoluteRamificationIndex, Nat.mul_comm] using
    ramificationIndex_tower (K := ℚ_[p]) (L := K) L

end TauCeti
