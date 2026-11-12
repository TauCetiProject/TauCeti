/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
import TauCeti.Data.Int.MulPred

/-!
# Characteristic vectors in unimodular lattices

The norm of an integral lattice is additive modulo two. For a unimodular lattice its
mod-two character is represented by pairing with a lattice vector. All such representatives
form one coset of twice the carrier, so their norms agree modulo eight.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

/-- Every unimodular integral lattice has a characteristic vector. -/
theorem IsUnimodular.exists_isCharacteristicVector {L : IntegralLattice V}
    (hL : L.IsUnimodular) : ∃ w : L, L.IsCharacteristicVector w := by
  have := hL.isPerfPair_integralForm
  simpa only [isCharacteristicVector_iff_isCharacteristic] using
    L.isSymm_integralForm.exists_isCharacteristic Int.two_dvd_sq_sub_self

/-- Two characteristic vectors of a unimodular lattice differ by twice a lattice vector. -/
theorem IsUnimodular.exists_characteristicVector_sub_eq_two_smul {L : IntegralLattice V}
    (hL : L.IsUnimodular) {w₁ w₂ : L}
    (h₁ : L.IsCharacteristicVector w₁) (h₂ : L.IsCharacteristicVector w₂) :
    ∃ v : L, w₁ - w₂ = (2 : ℤ) • v := by
  have := hL.isPerfPair_integralForm
  simpa only [sub_eq_iff_eq_add'] using
    ((L.isCharacteristicVector_iff_isCharacteristic w₂).1 h₂).exists_eq_add_two_smul
      ((L.isCharacteristicVector_iff_isCharacteristic w₁).1 h₁)

/-- The characteristic vectors of a unimodular lattice form a single coset of twice its
carrier. -/
theorem IsUnimodular.isCharacteristicVector_iff {L : IntegralLattice V}
    (hL : L.IsUnimodular) {w₀ : L} (hw₀ : L.IsCharacteristicVector w₀)
    (w : L) :
    L.IsCharacteristicVector w ↔ ∃ v : L, w = w₀ + (2 : ℤ) • v := by
  constructor
  · intro hw
    obtain ⟨v, hv⟩ := hL.exists_characteristicVector_sub_eq_two_smul hw hw₀
    exact ⟨v, (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)⟩
  · rintro ⟨v, rfl⟩
    exact hw₀.add_two_smul v

/-- Characteristic vectors of a unimodular lattice have the same norm modulo eight. -/
theorem IsUnimodular.characteristicVector_integralNorm_modEq {L : IntegralLattice V}
    (hL : L.IsUnimodular) {w₁ w₂ : L}
    (h₁ : L.IsCharacteristicVector w₁) (h₂ : L.IsCharacteristicVector w₂) :
    L.integralNorm w₁ ≡ L.integralNorm w₂ [ZMOD 8] := by
  have := hL.isPerfPair_integralForm
  refine (Int.modEq_iff_dvd.2 ?_).symm
  rw [L.integralNorm_apply, L.integralNorm_apply]
  exact ((L.isCharacteristicVector_iff_isCharacteristic w₂).1
    h₂).eight_dvd_apply_self_sub_apply_self L.isSymm_integralForm
      ((L.isCharacteristicVector_iff_isCharacteristic w₁).1 h₁)

end IntegralLattice

end TauCeti
