/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Tensor
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics

/-!
# The algebraic coefficients `V_(a,b)` of `GL₂`

For integers `a ≥ b`, the algebraic representation `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`
(`TauCeti.gl2CoefficientRep k a b`) is the coefficient system of weight `(a, b)`. This file gives
its coordinate description over a field `k`:

* it has dimension `a - b + 1`;
* a scalar matrix `z` acts by `z ^ (a + b)`;
* when the weight characters of `k` separate weights (for instance over an infinite field,
  `TauCeti.weightChar_injective`), its weights are the `(a - i, b + i)` for `0 ≤ i ≤ a - b`, each
  of multiplicity one, and in particular `(a, b)` is a weight.

The weights are read off from those of the symmetric power
(`TauCeti.RepresentationTheory.ClassicalGroups.Weight.SymmetricPower`) and the translation of
weights by the determinant twist (`TauCeti.weightSpace_tprod_detPowerRep`).

## Main definitions

* `TauCeti.GL2CoefficientSpace k a b`: its carrier `Sym^{a-b}(k²) ⊗ k`.
* `TauCeti.gl2CoefficientRep k a b`: the representation `Sym^{a-b}(Std) ⊗ det^b` of `GL₂(k)`.

## Main results

* `TauCeti.finrank_gl2CoefficientRep`: `dim V_(a,b) = a - b + 1`.
* `TauCeti.weightSpace_gl2CoefficientRep_ne_bot_iff`: the weights of `V_(a,b)` are the `l` with
  `b ≤ l 0`, `b ≤ l 1` and `l 0 + l 1 = a + b`.
* `TauCeti.finrank_weightSpace_gl2CoefficientRep`: each weight has multiplicity one.
* `TauCeti.gl2CoefficientRep_scalar`: a scalar matrix `z` acts by `z ^ (a + b)`.
-/

public section

noncomputable section

open Matrix Module
open scoped TensorProduct

namespace TauCeti

variable (k : Type) [Field k] (a b : ℤ)

/-- The carrier `Sym^{a-b}(k²) ⊗ k` of the coefficient `V_(a,b)`. -/
abbrev GL2CoefficientSpace : Type := Sym[k]^(a - b).toNat (Fin 2 → k) ⊗[k] k

/-- The **algebraic coefficient** `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`, for integers
`a ≥ b` (for `a < b` the symmetric power has exponent `0`). -/
abbrev gl2CoefficientRep : Representation k (GL (Fin 2) k) (GL2CoefficientSpace k a b) :=
  (symPowerRep k 2 (a - b).toNat).tprod (detPowerRep k 2 b)

variable {k a b}

/-- **`dim V_(a,b) = a - b + 1`.** -/
theorem finrank_gl2CoefficientRep (hab : b ≤ a) :
    (finrank k (GL2CoefficientSpace k a b) : ℤ) = a - b + 1 := by
  simp [finrank_tensorProduct, SymmetricPower.finrank_eq, Nat.multichoose_two,
    Int.toNat_of_nonneg (sub_nonneg.mpr hab)]

/-- **The weights of `V_(a,b)`** are the `l` with `b ≤ l 0`, `b ≤ l 1` and `l 0 + l 1 = a + b`,
that is, the `(a - i, b + i)` for `0 ≤ i ≤ a - b`. -/
theorem weightSpace_gl2CoefficientRep_ne_bot_iff
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l ≠ ⊥ ↔
      b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b := by
  rw [weightSpace_tprod_detPowerRep, Submodule.comap_equiv_eq_map_symm, Ne,
    Submodule.map_eq_bot_iff, ← Ne, weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq hchar]
  simp only [Fin.forall_fin_two, Fin.sum_univ_two, Pi.sub_apply,
    Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  omega

/-- **The highest weight `(a, b)` is a weight** of `V_(a,b)`. -/
theorem weightSpace_gl2CoefficientRep_highest_ne_bot
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) ![a, b] ≠ ⊥ :=
  (weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab _).2 ⟨by simpa using hab, by simp, by simp⟩

/-- **Every weight of `V_(a,b)` has multiplicity one.** -/
theorem finrank_weightSpace_gl2CoefficientRep
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) {l : Fin 2 → ℤ}
    (hl : b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b) :
    finrank k (weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l) = 1 := by
  obtain ⟨s, hs⟩ := (exists_sym_weightOfMultiset_eq_iff (d := (a - b).toNat)
    (l - fun _ ↦ b)).2 ⟨by simp only [Fin.forall_fin_two, Pi.sub_apply]; omega, by
      simp only [Fin.sum_univ_two, Pi.sub_apply, Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
      omega⟩
  rw [weightSpace_tprod_detPowerRep, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.finrank_map_eq, ← hs, finrank_weightSpace_symPowerRep hchar s]

/-- **A scalar matrix `z` acts on `V_(a,b)` by `z ^ (a + b)`.** -/
theorem gl2CoefficientRep_scalar (hab : b ≤ a) (z : kˣ) (x : GL2CoefficientSpace k a b) :
    gl2CoefficientRep k a b (GeneralLinearGroup.scalar (Fin 2) z) x =
      ((z ^ (a + b) : kˣ) : k) • x := by
  have hz : ((z ^ 2) ^ b : kˣ) * (z : k) ^ (a - b).toNat = ((z ^ (a + b) : kˣ) : k) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast z 2,
      ← zpow_natCast z (a - b).toNat, ← _root_.zpow_mul, ← _root_.zpow_add,
      Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    congr 2
    omega
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul v c =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, symPowerRep_scalar, detPowerRep_apply,
      GeneralLinearGroup.det_scalar, Fintype.card_fin, ← smul_eq_mul, TensorProduct.tmul_smul,
      ← TensorProduct.smul_tmul', ← mul_smul, hz]

end TauCeti
