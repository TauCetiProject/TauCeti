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

* `TauCeti.FinitePadicExtension.charZero`: a finite extension of `ℚ_[p]` has characteristic zero.
* `TauCeti.absoluteRamificationIndex_pos`: the absolute ramification index is positive.
* `TauCeti.absoluteRamificationIndex_eq_natCastValuation`: the absolute ramification index is
  the normalized valuation of `p` in `K`.
* `TauCeti.natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat`: the valuation of a
  natural-number cast in a finite extension of `ℚ_[p]`.
* `TauCeti.valuation_natCast_eq_pow_mul_padicValNat`: the same valuation, as a power of the
  valuation of a uniformizer.
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

/-- A finite extension of `ℚ_[p]` has characteristic zero. This is not an instance: `p` is not
determined by `CharZero K`. -/
theorem charZero (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] :
    CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

end FinitePadicExtension

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

/-- In a finite extension `K/ℚ_[p]`, the normalized valuation of a nonzero natural number is the
absolute ramification index times its `p`-adic valuation. -/
theorem natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat
    (n : ℕ) (hn : n ≠ 0) :
    natCastValuation K n
        (by
          have := FinitePadicExtension.charZero K p
          exact Nat.cast_ne_zero.mpr hn) =
      absoluteRamificationIndex K p * padicValNat p n := by
  rw [natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) n (Nat.cast_ne_zero.mpr hn),
    Padic.natCastValuation_eq_padicValNat, absoluteRamificationIndex]

variable {K} in
/-- In a finite extension `K/ℚ_[p]`, the valuation of a nonzero natural number `n` is
`v(π) ^ (e * v_p(n))` for any uniformizer `π`, where `e` is the absolute ramification index. -/
theorem valuation_natCast_eq_pow_mul_padicValNat {π : 𝒪[K]} (hπ : Irreducible π)
    {n : ℕ} (hn : n ≠ 0) :
    valuation K (n : K) =
      valuation K (π : K) ^ (absoluteRamificationIndex K p * padicValNat p n) := by
  have := FinitePadicExtension.charZero K p
  rw [valuation_natCast_eq_pow hπ n (Nat.cast_ne_zero.mpr hn),
    natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p n hn]

/-- The absolute ramification index is the normalized valuation of the residue prime `p` in
`K`. -/
@[simp]
theorem absoluteRamificationIndex_eq_natCastValuation :
    absoluteRamificationIndex K p = natCastValuation K p
      (by
        have := FinitePadicExtension.charZero K p
        exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) := by
  have hpval : padicValNat p p = 1 := by
    simpa only [Padic.natCastValuation_eq_padicValNat] using
      (Padic.natCastValuation_self (p := p))
  rw [natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p p
    (Fact.out : p.Prime).ne_zero, hpval, Nat.mul_one]

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
