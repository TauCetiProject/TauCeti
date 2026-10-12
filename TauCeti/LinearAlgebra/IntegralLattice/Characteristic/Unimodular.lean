/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

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
  let _ : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  let b := Module.Free.chooseBasis ℤ L
  let f : Module.Dual ℤ L := b.constr ℤ (fun i ↦ L.integralNorm (b i))
  have hparity :
      (Int.castAddHom (ZMod 2)).toIntLinearMap.comp f =
        (normParity L).toIntLinearMap := by
    apply b.ext
    intro i
    simp [f]
  refine ⟨(L.integralPairingEquiv hL).symm f, ?_⟩
  rw [L.isCharacteristicVector_iff_forall_integralForm_eq_normParity]
  intro x
  have hx := LinearMap.congr_fun hparity x
  have hnorm : ((f x : ℤ) : ZMod 2) = L.normParity x := by
    simpa using hx
  have hpair := LinearMap.congr_fun (L.integralPairingEquiv_toLinearMap hL)
    ((L.integralPairingEquiv hL).symm f)
  have heval := congrArg (fun p : Module.Dual ℤ L => p x) hpair
  rw [← heval]
  have hident : (L.integralPairingEquiv hL).toLinearMap
      ((L.integralPairingEquiv hL).symm f) = f :=
    (L.integralPairingEquiv hL).apply_symm_apply f
  rw [hident]
  exact hnorm

/-- Two characteristic vectors of a unimodular lattice differ by twice a lattice vector. -/
theorem IsUnimodular.exists_characteristicVector_sub_eq_two_smul {L : IntegralLattice V}
    (hL : L.IsUnimodular) {w₁ w₂ : L}
    (h₁ : L.IsCharacteristicVector w₁) (h₂ : L.IsCharacteristicVector w₂) :
    ∃ v : L, w₁ - w₂ = (2 : ℤ) • v := by
  let _ : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  let b := Module.Free.chooseBasis ℤ L
  choose c hc using fun i ↦ h₁.even_integralForm_sub h₂ (b i)
  let f : Module.Dual ℤ L := b.constr ℤ c
  have hf : (2 : ℤ) • f = L.integralPairingEquiv hL (w₁ - w₂) := by
    apply b.ext
    intro i
    simp only [LinearMap.smul_apply, f, b.constr_basis]
    have hpair := LinearMap.congr_fun (L.integralPairingEquiv_toLinearMap hL) (w₁ - w₂)
    have heval := congrArg (fun p : Module.Dual ℤ L => p (b i)) hpair
    calc
      (2 : ℤ) • c i = L.integralForm (w₁ - w₂) (b i) := by
        rw [Int.zsmul_eq_mul, two_mul]
        exact (hc i).symm
      _ = (L.integralPairingEquiv hL (w₁ - w₂)) (b i) := heval.symm
  refine ⟨(L.integralPairingEquiv hL).symm f, ?_⟩
  apply (L.integralPairingEquiv hL).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  exact hf.symm

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
  obtain ⟨v, hv⟩ := (hL.isCharacteristicVector_iff h₂ w₁).mp h₁
  rw [hv]
  exact h₂.integralNorm_add_two_smul_modEq v

end IntegralLattice

end TauCeti
