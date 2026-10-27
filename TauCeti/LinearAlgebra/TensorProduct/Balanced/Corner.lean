/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import TauCeti.RingTheory.Idempotents.Hom

/-!
# Balanced tensor products with an idempotent ideal

For an idempotent `e` and an arbitrary element `f` of a possibly noncommutative
`k`-algebra `A`, multiplication identifies `eA ⊗[A] Af` with the corner `eAf`.
The right ideal `eA` is represented by `Ideal.span {op e}` in the opposite algebra.
The inverse inserts `e` in the first factor. In particular the tensor product vanishes
exactly when the corner vanishes.

This calculation is the middle-factor identification in products of the bimodules
`Ae ⊗[k] eA` used in complexes of projective bimodules.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras*, Vol. 1, Section I.4.
-/

public section

namespace TauCeti

open MulOpposite

section Semiring

variable (k : Type*) [CommSemiring k] {A : Type*} [Semiring A] [Algebra k A]
  {e f : A}

private def spanSingletonPairing :
    (Ideal.span {op e} : Ideal Aᵐᵒᵖ) →ₗ[k]
      (Ideal.span {f} : Ideal A) →ₗ[k] cornerSubmodule k e f where
  toFun m :=
    { toFun n := ⟨unop (m : Aᵐᵒᵖ) * (n : A), by
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp m.2
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp n.2
        rw [cornerSubmodule_def, LinearMap.mem_range]
        refine ⟨unop a * b, ?_⟩
        simp only [LinearMap.mulLeftRight_apply, ← ha, ← hb, unop_mul, unop_op,
          mul_assoc]⟩
      map_add' n n' := Subtype.ext (by simp [mul_add])
      map_smul' r n := Subtype.ext (by simp) }
  map_add' m m' := LinearMap.ext fun n ↦ Subtype.ext (by simp [add_mul])
  map_smul' r m := LinearMap.ext fun n ↦ Subtype.ext (by simp)

@[simp]
private theorem coe_spanSingletonPairing_apply
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    (spanSingletonPairing k m n : A) = unop (m : Aᵐᵒᵖ) * (n : A) := (rfl)

private theorem spanSingletonPairing_balanced (a : A)
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    spanSingletonPairing k (op a • m) n =
      spanSingletonPairing k m (a • n) := by
  apply Subtype.ext
  simp [unop_mul, mul_assoc]

private def cornerToSpanSingleton :
    cornerSubmodule k e f →ₗ[k] (Ideal.span {f} : Ideal A) where
  toFun x := ⟨(x : A), mem_span_singleton_of_mem_cornerSubmodule x.2⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
private theorem coe_cornerToSpanSingleton_apply
    (x : cornerSubmodule k e f) : (cornerToSpanSingleton k x : A) = x := (rfl)

end Semiring

section Ring

variable (k : Type*) [CommRing k] {A : Type*} [Ring A] [Algebra k A]
  {e f : A}

/-- For an idempotent `e` and arbitrary `f`, multiplication identifies the balanced tensor
product `eA ⊗[A] Af` with `eAf`. The first ideal is taken in the opposite algebra to represent
its right action. -/
def spanSingletonBalancedTensorProductEquivCorner
    (he : IsIdempotentElem e) :
    BalancedTensorProduct k A (Ideal.span {op e} : Ideal Aᵐᵒᵖ)
      (Ideal.span {f} : Ideal A) ≃ₗ[k] cornerSubmodule k e f :=
  LinearEquiv.ofLinearMap
    (BalancedTensorProduct.lift (spanSingletonPairing k)
      (spanSingletonPairing_balanced k))
    ((BalancedTensorProduct.mk k A (spanSingletonGenerator (op e))).comp
      (cornerToSpanSingleton k))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simpa only [LinearMap.comp_apply, BalancedTensorProduct.lift_tmul,
        BalancedTensorProduct.mk_apply, coe_spanSingletonPairing_apply,
        coe_spanSingletonGenerator, unop_op, coe_cornerToSpanSingleton_apply,
        LinearMap.id_apply] using mul_eq_self_of_mem_cornerSubmodule he x.2)
    (by
      apply BalancedTensorProduct.hom_ext
      intro m n
      have heop : IsIdempotentElem (op e) := by
        rw [IsIdempotentElem, ← op_mul, he.eq]
      have hm : op (unop (m : Aᵐᵒᵖ)) • spanSingletonGenerator (op e) = m :=
        smul_spanSingletonGenerator heop m
      have hn : (unop (m : Aᵐᵒᵖ)) • n =
          cornerToSpanSingleton k (spanSingletonPairing k m n) :=
        Subtype.ext (by simp)
      simpa only [LinearMap.comp_apply, BalancedTensorProduct.lift_tmul,
        BalancedTensorProduct.mk_apply, LinearMap.id_apply, hn, hm] using
          (BalancedTensorProduct.balance k A (unop (m : Aᵐᵒᵖ))
            (spanSingletonGenerator (op e)) n).symm)

/-- On pure tensors the corner identification is multiplication in `A`. -/
@[simp]
theorem coe_spanSingletonBalancedTensorProductEquivCorner_tmul
    (he : IsIdempotentElem e)
    (m : (Ideal.span {op e} : Ideal Aᵐᵒᵖ)) (n : (Ideal.span {f} : Ideal A)) :
    (spanSingletonBalancedTensorProductEquivCorner k he
      (BalancedTensorProduct.tmul k A m n) : A) = unop (m : Aᵐᵒᵖ) * (n : A) := by
  simp only [spanSingletonBalancedTensorProductEquivCorner, LinearEquiv.coe_ofLinearMap,
    BalancedTensorProduct.lift_tmul, coe_spanSingletonPairing_apply]

/-- The inverse corner identification inserts the right-ideal generator `e`. -/
@[simp]
theorem spanSingletonBalancedTensorProductEquivCorner_symm_apply
    (he : IsIdempotentElem e) (x : cornerSubmodule k e f) :
    (spanSingletonBalancedTensorProductEquivCorner k he).symm x =
      BalancedTensorProduct.tmul k A (spanSingletonGenerator (op e))
        ⟨(x : A), mem_span_singleton_of_mem_cornerSubmodule x.2⟩ := by
  simp only [spanSingletonBalancedTensorProductEquivCorner, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.coe_ofLinearMap, LinearMap.comp_apply, BalancedTensorProduct.mk_apply]
  exact congrArg (BalancedTensorProduct.tmul k A (spanSingletonGenerator (op e)))
    (Subtype.ext (coe_cornerToSpanSingleton_apply k x))

/-- For an idempotent `e` and arbitrary `f`, the tensor product `eA ⊗[A] Af` vanishes exactly
when the corner `eAf` does. -/
theorem subsingleton_spanSingleton_balancedTensorProduct_iff_cornerSubmodule_eq_bot
    (he : IsIdempotentElem e) :
    Subsingleton (BalancedTensorProduct k A (Ideal.span {op e} : Ideal Aᵐᵒᵖ)
      (Ideal.span {f} : Ideal A)) ↔ cornerSubmodule k e f = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot]
  exact (spanSingletonBalancedTensorProductEquivCorner k he).toEquiv.subsingleton_congr

end Ring

end TauCeti
