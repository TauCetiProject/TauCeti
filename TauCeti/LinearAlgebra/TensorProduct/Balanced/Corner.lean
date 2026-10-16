/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import TauCeti.RingTheory.Idempotents.Hom

/-!
# Balanced tensor products of idempotent ideals

For idempotents `e, f` of a possibly noncommutative `k`-algebra `A`, multiplication
identifies `eA ⊗[A] Af` with the corner `eAf`. The right ideal `eA` is represented by
`Ideal.span {op e}` in the opposite algebra. The inverse inserts `e` in the first
factor. In particular the tensor product vanishes exactly when the corner vanishes.

This calculation is the middle-factor identification in products of the bimodules
`Ae ⊗[k] eA` used in complexes of projective bimodules.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras*, Vol. 1, Section I.4.
-/

public section

namespace TauCeti

open MulOpposite

variable (k : Type*) [CommRing k] {A : Type*} [Ring A] [Algebra k A]
  {e f : A}

private def idempotentIdealPairing (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (Ideal.span {op e} : Ideal Aᵐᵒᵖ) →ₗ[k]
      (Ideal.span {f} : Ideal A) →ₗ[k] cornerSubmodule k e f where
  toFun m :=
    { toFun n := ⟨unop (m : Aᵐᵒᵖ) * (n : A), by
        rw [mem_cornerSubmodule_iff k he hf]
        have heop : IsIdempotentElem (op e) := by
          rw [IsIdempotentElem, ← op_mul, he.eq]
        have hm := congrArg unop ((mem_span_singleton_iff_mul_eq_self heop).1 m.2)
        simp only [unop_mul, unop_op] at hm
        rw [← mul_assoc, hm, mul_assoc,
          (mem_span_singleton_iff_mul_eq_self hf).1 n.2]⟩
      map_add' n n' := Subtype.ext (by simp [mul_add])
      map_smul' r n := Subtype.ext (by simp) }
  map_add' m m' := LinearMap.ext fun n ↦ Subtype.ext (by simp [add_mul])
  map_smul' r m := LinearMap.ext fun n ↦ Subtype.ext (by simp)

@[simp]
private theorem coe_idempotentIdealPairing_apply
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    (idempotentIdealPairing k he hf m n : A) = unop (m : Aᵐᵒᵖ) * (n : A) := rfl

private theorem idempotentIdealPairing_balanced
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (a : A)
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    idempotentIdealPairing k he hf (op a • m) n =
      idempotentIdealPairing k he hf m (a • n) := by
  apply Subtype.ext
  simp [unop_mul, mul_assoc]

private def cornerToSpanSingleton (hf : IsIdempotentElem f) :
    cornerSubmodule k e f →ₗ[k] (Ideal.span {f} : Ideal A) where
  toFun x := ⟨(x : A), mem_span_singleton_of_mem_cornerSubmodule hf x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem coe_cornerToSpanSingleton_apply (hf : IsIdempotentElem f)
    (x : cornerSubmodule k e f) : (cornerToSpanSingleton k hf x : A) = x := rfl

/-- Multiplication identifies the balanced tensor product `eA ⊗[A] Af` with `eAf`.
The first ideal is taken in the opposite algebra to represent its right action. -/
def spanSingletonBalancedTensorProductEquivCorner
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    BalancedTensorProduct k A (Ideal.span {op e} : Ideal Aᵐᵒᵖ)
      (Ideal.span {f} : Ideal A) ≃ₗ[k] cornerSubmodule k e f :=
  LinearEquiv.ofLinearMap
    (BalancedTensorProduct.lift (idempotentIdealPairing k he hf)
      (idempotentIdealPairing_balanced k he hf))
    ((BalancedTensorProduct.mk k A (spanSingletonGenerator (op e))).comp
      (cornerToSpanSingleton k hf))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simpa using
        mul_eq_self_of_mem_cornerSubmodule he x.2)
    (by
      apply BalancedTensorProduct.hom_ext
      intro m n
      have heop : IsIdempotentElem (op e) := by
        rw [IsIdempotentElem, ← op_mul, he.eq]
      have hm : op (unop (m : Aᵐᵒᵖ)) • spanSingletonGenerator (op e) = m :=
        smul_spanSingletonGenerator heop m
      have hn : (unop (m : Aᵐᵒᵖ)) • n =
          cornerToSpanSingleton k hf (idempotentIdealPairing k he hf m n) :=
        Subtype.ext (by simp)
      simpa only [LinearMap.comp_apply, BalancedTensorProduct.lift_tmul,
        BalancedTensorProduct.mk_apply, LinearMap.id_apply, hn, hm] using
          (BalancedTensorProduct.balance k A (unop (m : Aᵐᵒᵖ))
            (spanSingletonGenerator (op e)) n).symm)

/-- On pure tensors the corner identification is multiplication in `A`. -/
@[simp]
theorem coe_spanSingletonBalancedTensorProductEquivCorner_tmul
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    (spanSingletonBalancedTensorProductEquivCorner k he hf
      (BalancedTensorProduct.tmul k A m n) : A) = unop (m : Aᵐᵒᵖ) * (n : A) := by
  simp [spanSingletonBalancedTensorProductEquivCorner, BalancedTensorProduct.lift_tmul]

/-- The inverse corner identification inserts the right-ideal generator `e`. -/
@[simp]
theorem spanSingletonBalancedTensorProductEquivCorner_symm_apply
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (x : cornerSubmodule k e f) :
    (spanSingletonBalancedTensorProductEquivCorner k he hf).symm x =
      BalancedTensorProduct.tmul k A (spanSingletonGenerator (op e))
        ⟨(x : A), mem_span_singleton_of_mem_cornerSubmodule hf x.2⟩ := by
  have hx : cornerToSpanSingleton k hf x =
      ⟨(x : A), mem_span_singleton_of_mem_cornerSubmodule hf x.2⟩ :=
    Subtype.ext (coe_cornerToSpanSingleton_apply k hf x)
  simpa [spanSingletonBalancedTensorProductEquivCorner] using
    congrArg (BalancedTensorProduct.tmul k A (spanSingletonGenerator (op e))) hx

/-- The tensor product of two idempotent ideals vanishes exactly when their corner does. -/
theorem subsingleton_spanSingleton_balancedTensorProduct_iff_cornerSubmodule_eq_bot
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Subsingleton (BalancedTensorProduct k A (Ideal.span {op e} : Ideal Aᵐᵒᵖ)
      (Ideal.span {f} : Ideal A)) ↔ cornerSubmodule k e f = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot]
  exact (spanSingletonBalancedTensorProductEquivCorner k he hf).toEquiv.subsingleton_congr

end TauCeti
