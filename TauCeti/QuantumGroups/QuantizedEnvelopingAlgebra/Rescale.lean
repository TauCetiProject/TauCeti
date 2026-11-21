/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

/-!
# Conjugation action of toral units on a quantized enveloping algebra

When `q ≠ 0`, conjugation by the toral unit `kUnitsHom D q (.ofAdd y)` equals the diagonal
rescaling automorphism `TauCeti.QuantizedEnvelopingAlgebra.rescale D q` at
`i ↦ Units.mk0 q hq ^ D.pairing (D.root i) y`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.toAlgEquiv_conjAct_kUnitsHom`: conjugation by `K_y` equals
  `rescale D q (fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) y)` for `q ≠ 0`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, GSM 6, AMS, 1996, §4.6.
* Generalizes `TauCeti.UqSl2.toAlgEquiv_conjAct_kUnit`.
-/

public section

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  {D : CartanDatum ι X Y} {q : K}

/-- For `q ≠ 0`, conjugation by `kUnitsHom D q (.ofAdd y)` equals `rescale` at
`i ↦ q^⟨αᵢ, y⟩`. -/
theorem toAlgEquiv_conjAct_kUnitsHom (hq : q ≠ 0) (y : Y) :
    MulSemiringAction.toAlgEquiv K (QuantizedEnvelopingAlgebra D q)
        (ConjAct.toConjAct (kUnitsHom D q (.ofAdd y))) =
      rescale D q (fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) y) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply hom_ext <;> intro a
  · simp [ConjAct.units_smul_def, k_mul_e_mul_k_neg]
  · simp [ConjAct.units_smul_def, k_mul_f_mul_k_neg, zpow_neg]
  · simp [ConjAct.units_smul_def, k_mul_k]

end TauCeti.QuantizedEnvelopingAlgebra
