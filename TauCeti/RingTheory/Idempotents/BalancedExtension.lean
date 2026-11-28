/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Balanced extension of principal idempotent ideals

Along any ring homomorphism `f : R →+* S` of possibly noncommutative rings, the balanced extension
of scalars `TauCeti.BalancedExtension f (Ideal.span {e})` of the principal left ideal `Re` generated
by an idempotent `e : R` is `S`-linearly isomorphic to the principal left ideal `S f(e)`
(`IsIdempotentElem.balancedExtensionSpanSingletonEquiv`).
-/

public section

namespace TauCeti.BalancedExtension

universe u₁ u₂

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

private def balancedExtensionSpanSingletonFwd {e : R} (he : IsIdempotentElem e) :
    (Ideal.span {e} : Ideal R) →ₛₗ[f] (Ideal.span {f e} : Ideal S) where
  toFun x := ⟨f x.val, (TauCeti.mem_span_singleton_iff_mul_eq_self (he.map f)).2 <| by
    rw [← map_mul, (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 x.property]⟩
  map_add' x y := Subtype.ext (_root_.map_add f x.val y.val)
  map_smul' r x := Subtype.ext (map_mul f r x.val)

private theorem coe_balancedExtensionSpanSingletonFwd {e : R} (he : IsIdempotentElem e)
    (x : (Ideal.span {e} : Ideal R)) :
    (balancedExtensionSpanSingletonFwd f he x : S) = f x.val := (rfl)

private noncomputable def balancedExtensionSpanSingletonInv (e : R) :
    (Ideal.span {f e} : Ideal S) →ₗ[S]
      TauCeti.BalancedExtension f (Ideal.span {e} : Ideal R) :=
  (LinearMap.toSpanSingleton S _
    (TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e))).comp
    (Ideal.span {f e} : Ideal S).subtype

private theorem balancedExtensionSpanSingletonInv_apply (e : R)
    (y : (Ideal.span {f e} : Ideal S)) :
    balancedExtensionSpanSingletonInv f e y =
      y.val • TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e) :=
  (rfl)

/-- Along any ring homomorphism `f : R →+* S`, balanced extension of scalars sends the principal
left ideal `Re` of an idempotent `e` to `S f(e)`. -/
noncomputable def _root_.IsIdempotentElem.balancedExtensionSpanSingletonEquiv
    {e : R} (he : IsIdempotentElem e) :
    TauCeti.BalancedExtension f (Ideal.span {e} : Ideal R) ≃ₗ[S]
      (Ideal.span {f e} : Ideal S) :=
  LinearEquiv.ofLinearMap
    (TauCeti.BalancedExtension.lift (balancedExtensionSpanSingletonFwd f he))
    (balancedExtensionSpanSingletonInv f e)
    (LinearMap.ext fun y ↦ Subtype.ext <| by
      simp only [LinearMap.comp_apply, LinearMap.id_apply,
        balancedExtensionSpanSingletonInv_apply, map_smul, TauCeti.BalancedExtension.lift_tmul,
        one_smul, SetLike.val_smul, smul_eq_mul, coe_balancedExtensionSpanSingletonFwd,
        TauCeti.coe_spanSingletonGenerator]
      exact (TauCeti.mem_span_singleton_iff_mul_eq_self (he.map f)).1 y.property)
    (TauCeti.BalancedExtension.hom_ext fun x ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, TauCeti.BalancedExtension.lift_tmul,
        one_smul, balancedExtensionSpanSingletonInv_apply, coe_balancedExtensionSpanSingletonFwd]
      rw [TauCeti.BalancedExtension.smul_tmul, mul_one, ← one_mul (f x.val),
        ← TauCeti.BalancedExtension.tmul_smul, TauCeti.smul_spanSingletonGenerator he x])

@[simp]
theorem _root_.IsIdempotentElem.coe_balancedExtensionSpanSingletonEquiv_tmul
    {e : R} (he : IsIdempotentElem e) (s : S) (x : (Ideal.span {e} : Ideal R)) :
    (he.balancedExtensionSpanSingletonEquiv f (TauCeti.BalancedExtension.tmul f s x) : S) =
      s * f x.val := by
  simp [IsIdempotentElem.balancedExtensionSpanSingletonEquiv,
    coe_balancedExtensionSpanSingletonFwd]

@[simp]
theorem _root_.IsIdempotentElem.balancedExtensionSpanSingletonEquiv_symm_apply
    {e : R} (he : IsIdempotentElem e) (y : (Ideal.span {f e} : Ideal S)) :
    (he.balancedExtensionSpanSingletonEquiv f).symm y =
      y.val • TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e) :=
  balancedExtensionSpanSingletonInv_apply f e y

end TauCeti.BalancedExtension
