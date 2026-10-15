/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# Power classes of local units

For a nonarchimedean local field `K`, the unit group of its integer ring has
`#μ_n(K) · q ^ v_K(n)` classes modulo `n`-th powers, provided `n` is nonzero in `K`.
The valuation splitting `unitsEquivIntProd` separates the factor `n` in the existing
field power-class count `card_powerClasses` from the contribution of the units.

In particular, away from the residue characteristic the unit power-class count is
`#μ_n(K)`, and it is `n` when `K` contains the `n`-th roots of unity. This is the local
count used in comparing an S-unit quotient with a product of local unit quotients.

## References

* J. S. Milne, *Class Field Theory*, VII, proof of Lemma 6.9.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Power classes of local units.** For `n` nonzero in `K`, the unit group of the integer
ring has `#μ_n(K) · q ^ v_K(n)` classes modulo `n`-th powers. -/
theorem card_integerUnitPowerClasses {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ natCastValuation K n hn := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
  let e : Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ :=
    (unitsEquivIntProd K ϖ hϖ).toMulEquiv.trans
      (MulEquiv.prodCongr (.refl _) unitFiltrationZeroEquivIntegerUnits)
  have hprod : (powMonoidHom n : Multiplicative ℤ × 𝒪[K]ˣ →* _) =
      (powMonoidHom n).prodMap (powMonoidHom n) := by
    ext x <;> simp
  have hZ : (powMonoidHom n : Multiplicative ℤ →* _).range.index = n := by
    have hker : (powMonoidHom n : Multiplicative ℤ →* _).ker = ⊥ := by
      ext
      simp [hn0]
    simpa [hker, (AddEquiv.additiveMultiplicative ℤ).toIntLinearEquiv.finrank_eq] using
      Subgroup.index_range_powMonoidHom_of_fg (Multiplicative ℤ) hn0
  have hcount : Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_map_equiv _ e,
      e.map_range_powMonoidHom n, hprod, MonoidHom.range_prodMap, Subgroup.index_prod,
      hZ, Subgroup.index_eq_card]
  rw [card_powerClasses hn, mul_assoc] at hcount
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) hcount.symm

/-- For `n` nonzero in `K`, the `n`-th powers of the integer-ring units have finite index. -/
theorem finiteIndex_range_powMonoidHom_integerUnits {n : ℕ} (hn : (n : K) ≠ 0) :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.FiniteIndex := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hn⟩
  refine ⟨?_⟩
  rw [Subgroup.index_eq_card, card_integerUnitPowerClasses hn]
  exact mul_ne_zero Nat.card_pos.ne' (pow_ne_zero _ Nat.card_pos.ne')

/-- For `n` nonzero in `K`, the power-map range on integer-ring units has finite index. -/
instance instFiniteIndexRangePowMonoidHomIntegerUnits {n : ℕ} [NeZero (n : K)] :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.FiniteIndex :=
  finiteIndex_range_powMonoidHom_integerUnits (NeZero.ne (n : K))

/-- For `n` nonzero in `K`, the power-class quotient of the integer-ring units is finite. -/
instance finite_powerClassQuotient_integerUnits {n : ℕ} [NeZero (n : K)] :
    Finite (powerClassQuotient 𝒪[K]ˣ n) :=
  have : (powerSubgroup 𝒪[K]ˣ n).FiniteIndex :=
    powerSubgroup_eq_range_powMonoidHom 𝒪[K]ˣ n ▸
      finiteIndex_range_powMonoidHom_integerUnits (NeZero.ne (n : K))
  Subgroup.finite_quotient_of_finiteIndex

/-- Away from the residue characteristic, the unit group has as many `n`-th power classes
as there are `n`-th roots of unity in the field. -/
theorem card_integerUnitPowerClasses_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (rootsOfUnity n K) := by
  rw [card_integerUnitPowerClasses (natCast_ne_zero_of_isUnit hn),
    natCastValuation_eq_zero_of_isUnit K _ hn, pow_zero, mul_one]

end TauCeti
