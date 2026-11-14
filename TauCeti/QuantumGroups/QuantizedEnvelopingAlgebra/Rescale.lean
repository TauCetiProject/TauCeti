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

For any family of invertible scalars `c : ι → Kˣ`, the assignments `Eᵢ ↦ cᵢ • Eᵢ`,
`Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, `K_y ↦ K_y` preserve the presentation of `QuantizedEnvelopingAlgebra D q`.
Indeed, in `Eᵢ Fᵢ - Fᵢ Eᵢ` the scalars `cᵢ` and `cᵢ⁻¹` cancel, while for `i ≠ j` every term of the
divided-power Serre polynomial `∑_{r + s = 1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(s)` scales uniformly by
`cᵢ^(1 - aᵢⱼ) cⱼ` (and its `F` analogue by `(cᵢ⁻¹)^(1 - aᵢⱼ) cⱼ⁻¹`).

These automorphisms assemble into a group homomorphism
`TauCeti.QuantizedEnvelopingAlgebra.rescale : (ι → Kˣ) →* (U ≃ₐ[K] U)` with no hypotheses on `q` or
`ι`. When `q ≠ 0`, conjugation by `K_y` is the rescaling automorphism with parameter
`i ↦ q^⟨αᵢ, y⟩`.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.rescale`: the diagonal rescaling automorphism group
  homomorphism `(ι → Kˣ) →* (QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q)`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.toAlgEquiv_conjAct_kUnit`: for `q ≠ 0`, conjugation by
  `kUnit D q y` equals `rescale D q (fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) y)`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.6.
-/

public section

open Finset

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  (D : CartanDatum ι X Y) (q : K)

private noncomputable def rescaleAlgHom (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := (c i : K) • e D q i
      f i := (c i : K)⁻¹ • f D q i
      k y := k D q y
      k_zero := k_zero
      k_mul_k := k_mul_k
      k_mul_e y i := by rw [mul_smul_comm, k_mul_e, smul_mul_assoc, smul_comm]
      k_mul_f y i := by rw [mul_smul_comm, k_mul_f, smul_mul_assoc, smul_comm]
      e_mul_f_sub_f_mul_e_self i := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
          inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self]
      e_mul_f_sub_f_mul_e_of_ne hij := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c _ : K)⁻¹, ← smul_sub,
          e_mul_f_sub_f_mul_e_of_ne hij, smul_zero]
      serre_e {i j} hij := by
        have hterm : ∀ r ∈ range (serreLength D i j + 1),
            (-1 : K) ^ r •
              (quantumDividedPower (q ^ D.symmetrizer i) ((c i : K) • e D q i) r *
                ((c j : K) • e D q j) *
                quantumDividedPower (q ^ D.symmetrizer i) ((c i : K) • e D q i)
                  (serreLength D i j - r)) =
            ((c i : K) ^ serreLength D i j * c j) •
              ((-1 : K) ^ r •
                (eDividedPower D q i r * e D q j * eDividedPower D q i (serreLength D i j - r))) :=
          fun r hr ↦ by
            have hr' : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
            rw [quantumDividedPower_smul, quantumDividedPower_smul, smul_mul_smul_comm,
              smul_mul_smul_comm, smul_comm ((-1 : K) ^ r)]
            congr 1
            rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hr']
        rw [sum_congr rfl hterm, ← smul_sum, serre_e hij, smul_zero]
      serre_f {i j} hij := by
        have hterm : ∀ r ∈ range (serreLength D i j + 1),
            (-1 : K) ^ r •
              (quantumDividedPower (q ^ D.symmetrizer i) ((c i : K)⁻¹ • f D q i) r *
                ((c j : K)⁻¹ • f D q j) *
                quantumDividedPower (q ^ D.symmetrizer i) ((c i : K)⁻¹ • f D q i)
                  (serreLength D i j - r)) =
            (((c i : K)⁻¹) ^ serreLength D i j * (c j : K)⁻¹) •
              ((-1 : K) ^ r •
                (fDividedPower D q i r * f D q j * fDividedPower D q i (serreLength D i j - r))) :=
          fun r hr ↦ by
            have hr' : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
            rw [quantumDividedPower_smul, quantumDividedPower_smul, smul_mul_smul_comm,
              smul_mul_smul_comm, smul_comm ((-1 : K) ^ r)]
            congr 1
            rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hr']
        rw [sum_congr rfl hterm, ← smul_sum, serre_f hij, smul_zero] }

@[simp]
private theorem rescaleAlgHom_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (e D q i) = (c i : K) • e D q i :=
  lift_e _ i

@[simp]
private theorem rescaleAlgHom_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (f D q i) = (c i : K)⁻¹ • f D q i :=
  lift_f _ i

@[simp]
private theorem rescaleAlgHom_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgHom D q c (k D q y) = k D q y :=
  lift_k _ y

private theorem rescaleAlgHom_one :
    rescaleAlgHom D q 1 = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

private theorem rescaleAlgHom_mul (c₁ c₂ : ι → Kˣ) :
    rescaleAlgHom D q (c₁ * c₂) = (rescaleAlgHom D q c₁).comp (rescaleAlgHom D q c₂) := by
  ext <;> simp [smul_smul, mul_comm]

/-- The diagonal rescaling automorphisms `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, `K_y ↦ K_y` of
`QuantizedEnvelopingAlgebra D q`, as a group homomorphism from `ι → Kˣ` to the `K`-algebra
automorphism group. -/
noncomputable def rescale :
    (ι → Kˣ) →* (QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q) where
  toFun c := AlgEquiv.ofAlgHom (rescaleAlgHom D q c) (rescaleAlgHom D q c⁻¹)
    (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])
  map_one' := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_one D q)
  map_mul' c₁ c₂ := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_mul D q c₁ c₂)

variable {D q}

@[simp]
theorem rescale_e (c : ι → Kˣ) (i : ι) :
    rescale D q c (e D q i) = (c i : K) • e D q i :=
  rescaleAlgHom_e D q c i

@[simp]
theorem rescale_f (c : ι → Kˣ) (i : ι) :
    rescale D q c (f D q i) = (c i : K)⁻¹ • f D q i :=
  rescaleAlgHom_f D q c i

@[simp]
theorem rescale_k (c : ι → Kˣ) (y : Y) :
    rescale D q c (k D q y) = k D q y :=
  rescaleAlgHom_k D q c y

/-- For `q ≠ 0`, conjugation by `kUnit D q y` equals the diagonal rescaling automorphism with
parameter `i ↦ q^⟨αᵢ, y⟩`. -/
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
