/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import Mathlib.GroupTheory.IndexNSmul
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
    have hpow : (powMonoidHom n : Multiplicative ℤ →* _) =
        AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ℤ) n) := by
      ext
      simp
    rw [hpow, MonoidHom.coe_toMultiplicative_range, AddSubgroup.index_toSubgroup,
      AddSubgroup.index_range_nsmul]
    simp
  have hcount : Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_map_equiv _ e,
      e.map_range_powMonoidHom n, hprod, MonoidHom.range_prodMap, Subgroup.index_prod,
      hZ, Subgroup.index_eq_card]
  rw [card_powerClasses hn, mul_assoc] at hcount
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) hcount.symm

/-- Away from the residue characteristic, the unit group has as many `n`-th power classes
as there are `n`-th roots of unity in the field. -/
theorem card_integerUnitPowerClasses_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (rootsOfUnity n K) := by
  rw [card_integerUnitPowerClasses (natCast_ne_zero_of_isUnit hn),
    natCastValuation_eq_zero_of_isUnit K _ hn, pow_zero, mul_one]

/-- If `K` contains the `n`-th roots of unity and `n` is invertible in its integer ring,
then its units have exactly `n` classes modulo `n`-th powers. -/
theorem card_integerUnitPowerClasses_of_hasEnoughRootsOfUnity {n : ℕ}
    [HasEnoughRootsOfUnity K n] (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) = n := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hn⟩
  rw [card_integerUnitPowerClasses_of_isUnit hn,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity K n]

end TauCeti
