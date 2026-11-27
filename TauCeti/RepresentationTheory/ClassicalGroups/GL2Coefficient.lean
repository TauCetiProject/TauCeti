/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Tensor
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Dual
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics

/-!
# The algebraic coefficients `V_(a,b)` of `GL₂`

For integers `a ≥ b`, the algebraic representation `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`
(`TauCeti.gl2CoefficientRep k a b`) is the coefficient system of weight `(a, b)`. This file gives
its coordinate description:

* a scalar matrix `z` acts by `z ^ (a + b)`, over any commutative ring `k`;
* over a field `k`, it has dimension `a - b + 1`;
* over a nontrivial commutative ring `k` without zero divisors whose weight characters separate
  weights (for instance an infinite field, `TauCeti.weightChar_injective`), its weights are the
  `(a - i, b + i)` for `0 ≤ i ≤ a - b`, and in particular `(a, b)` is a weight;
* over such a field, each weight has multiplicity one;
* its contragredient has scalar weight `-(a + b)` and, over such a field, the weights of
  `V_(-b,-a)` with the same multiplicities, so its highest weight is `(-b, -a)`.

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
* `TauCeti.gl2CoefficientRep_dual_scalar`: on the contragredient, by `z ^ (-(a + b))`.
* `TauCeti.finrank_weightSpace_dual_gl2CoefficientRep`: the weight multiplicities of the
  contragredient of `V_(a,b)` are those of `V_(-b,-a)`.
* `TauCeti.weightSpace_dual_gl2CoefficientRep_highest_ne_bot`: `(-b, -a)` is a weight of the
  contragredient of `V_(a,b)`.
* `TauCeti.isRationalRep_gl2CoefficientRep`: `V_(a,b)` is a rational representation of `GL₂(ℂ)`.
-/

public section

noncomputable section

open Matrix Module
open scoped TensorProduct

namespace TauCeti

section CommRing

variable (k : Type) [CommRing k] (a b : ℤ)

/-- The carrier `Sym^{a-b}(k²) ⊗ k` of the coefficient `V_(a,b)`. -/
abbrev GL2CoefficientSpace : Type := Sym[k]^(a - b).toNat (Fin 2 → k) ⊗[k] k

/-- The **algebraic coefficient** `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`, for integers
`a ≥ b` (for `a < b` the symmetric power has exponent `0`). -/
abbrev gl2CoefficientRep : Representation k (GL (Fin 2) k) (GL2CoefficientSpace k a b) :=
  (symPowerRep k 2 (a - b).toNat).tprod (detPowerRep k 2 b)

variable {k a b}

/-- **A scalar matrix `z` acts on `V_(a,b)` by `z ^ (a + b)`.** -/
theorem gl2CoefficientRep_scalar (hab : b ≤ a) (z : kˣ) (x : GL2CoefficientSpace k a b) :
    gl2CoefficientRep k a b (GeneralLinearGroup.scalar (Fin 2) z) x =
      ((z ^ (a + b) : kˣ) : k) • x := by
  have hz : (z ^ 2) ^ b * z ^ (a - b).toNat = z ^ (a + b) := by
    rw [← zpow_natCast z (a - b).toNat, Int.toNat_sub_of_le hab]
    group
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul v c =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, symPowerRep_scalar, ← hz,
      Units.val_mul, Units.val_pow_eq_pow_val]
    simp only [detPowerRep_apply, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← smul_eq_mul,
      TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]

/-- **A scalar matrix `z` acts on the contragredient of `V_(a,b)` by `z ^ (-(a + b))`.** -/
theorem gl2CoefficientRep_dual_scalar (hab : b ≤ a) (z : kˣ)
    (f : Dual k (GL2CoefficientSpace k a b)) :
    (gl2CoefficientRep k a b).dual (GeneralLinearGroup.scalar (Fin 2) z) f =
      ((z ^ (-(a + b)) : kˣ) : k) • f := by
  refine LinearMap.ext fun x ↦ ?_
  rw [Representation.dual_apply, Dual.transpose_apply, LinearMap.comp_apply, ← map_inv,
    gl2CoefficientRep_scalar hab, map_smul, LinearMap.smul_apply, _root_.inv_zpow']

/-- The weight spaces of `V_(a,b)` span it. -/
theorem iSup_weightSpace_gl2CoefficientRep_eq_top :
    ⨆ l : Fin 2 → ℤ, weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l =
      ⊤ :=
  iSup_weightSpace_tprod_eq_top iSup_weightSpace_symPowerRep_eq_top
    (top_le_iff.mp ((weightSpace_detPowerRep b).symm.le.trans (le_iSup _ _)))

end CommRing

section IsCancelMulZero

variable {k : Type} [CommRing k] [IsCancelMulZero k] [Nontrivial k] {a b : ℤ}

/-- **The weights of `V_(a,b)`**, when the weight characters of `k` separate weights (for
instance over an infinite field, `TauCeti.weightChar_injective`), are the `l` with `b ≤ l 0`,
`b ≤ l 1` and `l 0 + l 1 = a + b`, that is, the `(a - i, b + i)` for `0 ≤ i ≤ a - b`. -/
theorem weightSpace_gl2CoefficientRep_ne_bot_iff
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l ≠ ⊥ ↔
      b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b := by
  rw [weightSpace_tprod_detPowerRep, Submodule.comap_equiv_eq_map_symm, Ne,
    Submodule.map_eq_bot_iff, ← Ne, weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq hchar]
  simp only [Fin.forall_fin_two, Fin.sum_univ_two, Pi.sub_apply, Int.toNat_sub_of_le hab]
  omega

/-- **The highest weight `(a, b)` is a weight** of `V_(a,b)`, when the weight characters of `k`
separate weights (for instance over an infinite field, `TauCeti.weightChar_injective`). -/
theorem weightSpace_gl2CoefficientRep_highest_ne_bot
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) ![a, b] ≠ ⊥ :=
  (weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab _).2 ⟨by simpa using hab, by simp, by simp⟩

end IsCancelMulZero

section Field

variable {k : Type} [Field k] {a b : ℤ}

/-- **`dim V_(a,b) = a - b + 1`.** -/
theorem finrank_gl2CoefficientRep (hab : b ≤ a) :
    (finrank k (GL2CoefficientSpace k a b) : ℤ) = a - b + 1 := by
  simp [finrank_tensorProduct, SymmetricPower.finrank_eq, Nat.multichoose_two,
    Int.toNat_sub_of_le hab]

/-- **Every weight of `V_(a,b)` has multiplicity one**, when the weight characters of `k`
separate weights (for instance over an infinite field, `TauCeti.weightChar_injective`). -/
theorem finrank_weightSpace_gl2CoefficientRep
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) {l : Fin 2 → ℤ}
    (hl : b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b) :
    finrank k (weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l) = 1 := by
  have hab : b ≤ a := by omega
  obtain ⟨s, hs⟩ := (exists_sym_weightOfMultiset_eq_iff (d := (a - b).toNat)
    (l - fun _ ↦ b)).2 ⟨by simp only [Fin.forall_fin_two, Pi.sub_apply]; omega, by
      simp only [Fin.sum_univ_two, Pi.sub_apply, Int.toNat_sub_of_le hab]
      omega⟩
  rw [weightSpace_tprod_detPowerRep, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.finrank_map_eq, ← hs, finrank_weightSpace_symPowerRep hchar s]

/-- The weight multiplicities of `V_(a,b)`: one on the weights `(a - i, b + i)`, zero
elsewhere. -/
theorem finrank_weightSpace_gl2CoefficientRep_eq_ite
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ)
    [Decidable (b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b)] :
    finrank k (weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l) =
      if b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b then 1 else 0 := by
  split_ifs with hl
  · exact finrank_weightSpace_gl2CoefficientRep hchar hl
  · rw [← (weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab l).not, not_not] at hl
    rw [hl, finrank_bot]

/-- **The contragredient of `V_(a,b)` has the weights of `V_(-b,-a)`, with the same
multiplicities**, when the weight characters of `k` separate weights (for instance over an
infinite field, `TauCeti.weightChar_injective`). -/
theorem finrank_weightSpace_dual_gl2CoefficientRep
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ) :
    finrank k (weightSpace (gl2CoefficientRep k a b).dual l) =
      finrank k (weightSpace (W := GL2CoefficientSpace k (-b) (-a))
        (gl2CoefficientRep k (-b) (-a)) l) := by
  classical
  rw [finrank_weightSpace_dual hchar iSup_weightSpace_gl2CoefficientRep_eq_top,
    finrank_weightSpace_gl2CoefficientRep_eq_ite hchar hab,
    finrank_weightSpace_gl2CoefficientRep_eq_ite hchar (neg_le_neg hab)]
  simp only [Pi.neg_apply]
  congr 1
  apply propext
  omega

/-- **The weights of the contragredient of `V_(a,b)`** are those of `V_(-b,-a)`: the `l` with
`l 0 ≤ -b`, `l 1 ≤ -b` and `l 0 + l 1 = -(a + b)`, when the weight characters of `k` separate
weights. -/
theorem weightSpace_dual_gl2CoefficientRep_ne_bot_iff
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ) :
    weightSpace (gl2CoefficientRep k a b).dual l ≠ ⊥ ↔
      -a ≤ l 0 ∧ -a ≤ l 1 ∧ l 0 + l 1 = -b + -a := by
  rw [weightSpace_dual_ne_bot_iff hchar iSup_weightSpace_gl2CoefficientRep_eq_top,
    weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab]
  simp only [Pi.neg_apply]
  omega

/-- **The highest weight `(-b, -a)` is a weight** of the contragredient of `V_(a,b)`, when the
weight characters of `k` separate weights. -/
theorem weightSpace_dual_gl2CoefficientRep_highest_ne_bot
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) :
    weightSpace (gl2CoefficientRep k a b).dual ![-b, -a] ≠ ⊥ :=
  (weightSpace_dual_gl2CoefficientRep_ne_bot_iff hchar hab _).2
    ⟨by simpa using hab, by simp, by simp⟩

end Field

/-- **`V_(a,b)` is a rational representation of `GL₂(ℂ)`**: it is the tensor product of a
symmetric power of the standard representation, which is polynomial, and a power of the
determinant. -/
theorem isRationalRep_gl2CoefficientRep (a b : ℤ) : IsRationalRep (gl2CoefficientRep ℂ a b) :=
  (isPolynomialRep_symPowerRep 2 _).isRationalRep.tprod (isRationalRep_detPowerRep b)

end TauCeti
