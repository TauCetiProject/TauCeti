/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

/-!
# Diagonal rescaling automorphisms of a quantized enveloping algebra

For `c : ι → Kˣ`, the assignments `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, `K_y ↦ K_y` define a group
homomorphism `TauCeti.QuantizedEnvelopingAlgebra.rescale : (ι → Kˣ) →* (U ≃ₐ[K] U)` with no
hypotheses on `q` or `ι`. When `q ≠ 0`, conjugation by `K_y` equals `rescale` at
`i ↦ q^⟨αᵢ, y⟩`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, GSM 6, AMS, 1996, §4.6.
* Generalizes `TauCeti.QuantumGroups.UqSl2.Rescale` (`TauCeti.UqSl2.rescale`,
  `TauCeti.UqSl2.toAlgEquiv_conjAct_kUnit`).
-/

public section

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  (D : CartanDatum ι X Y) (q : K)

private noncomputable def rescaleAlgHom (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := (c i : K) • e D q i, f i := (c i : K)⁻¹ • f D q i, k y := k D q y
      k_zero := k_zero, k_mul_k := k_mul_k
      k_mul_e y i := by rw [mul_smul_comm, k_mul_e, smul_mul_assoc, smul_comm]
      k_mul_f y i := by rw [mul_smul_comm, k_mul_f, smul_mul_assoc, smul_comm]
      e_mul_f_sub_f_mul_e_self i := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
          inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self]
      e_mul_f_sub_f_mul_e_of_ne hij := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c _ : K)⁻¹, ← smul_sub,
          e_mul_f_sub_f_mul_e_of_ne hij, smul_zero]
      serre_e hij := by rw [serre_smul, serre_e hij, smul_zero]
      serre_f hij := by rw [serre_smul, serre_f hij, smul_zero] }

private theorem rescaleAlgHom_one :
    rescaleAlgHom D q 1 = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp [rescaleAlgHom]

private theorem rescaleAlgHom_mul (c₁ c₂ : ι → Kˣ) :
    rescaleAlgHom D q (c₁ * c₂) = (rescaleAlgHom D q c₁).comp (rescaleAlgHom D q c₂) := by
  ext <;> simp [rescaleAlgHom, smul_smul, mul_comm]

/-- The diagonal rescaling automorphisms `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, `K_y ↦ K_y` of
`QuantizedEnvelopingAlgebra D q`, as a group homomorphism from `ι → Kˣ`. -/
noncomputable def rescale :
    (ι → Kˣ) →* (QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q) where
  toFun c := AlgEquiv.ofAlgHom (rescaleAlgHom D q c) (rescaleAlgHom D q c⁻¹)
    (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])
  map_one' := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_one D q)
  map_mul' c₁ c₂ := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_mul D q c₁ c₂)

variable {D q}

@[simp] theorem rescale_e (c : ι → Kˣ) (i : ι) :
    rescale D q c (e D q i) = (c i : K) • e D q i := by
  rw [rescale, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.ofAlgHom_apply]; exact lift_e _ i

@[simp] theorem rescale_f (c : ι → Kˣ) (i : ι) :
    rescale D q c (f D q i) = (c i : K)⁻¹ • f D q i := by
  rw [rescale, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.ofAlgHom_apply]; exact lift_f _ i

@[simp] theorem rescale_k (c : ι → Kˣ) (y : Y) :
    rescale D q c (k D q y) = k D q y := by
  rw [rescale, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.ofAlgHom_apply]; exact lift_k _ y

/-- For `q ≠ 0`, conjugation by `kUnit D q y` equals `rescale` at `i ↦ q^⟨αᵢ, y⟩`. -/
theorem toAlgEquiv_conjAct_kUnit {q : K} (hq : q ≠ 0) (y : Y) :
    MulSemiringAction.toAlgEquiv K (QuantizedEnvelopingAlgebra D q)
        (ConjAct.toConjAct (kUnit D q y)) =
      rescale D q (fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) y) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext i
  · simp [ConjAct.units_smul_def, k_mul_e_mul_k_neg]
  · simp [ConjAct.units_smul_def, k_mul_f_mul_k_neg, zpow_neg]
  · simp [ConjAct.units_smul_def, k_mul_k]

end TauCeti.QuantizedEnvelopingAlgebra
