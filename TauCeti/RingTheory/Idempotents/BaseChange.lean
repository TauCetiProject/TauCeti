/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Base change along a decomposition by idempotents

A complete orthogonal family of idempotents `f i` of a commutative ring `T` decomposes `T` into
the product of its components `T ⧸ (1 - f i)` (`CompleteOrthogonalIdempotents.bijective_pi`).
Tensoring with a `T`-algebra `X` splits `X` accordingly into the product of its base changes to
the components (`CompleteOrthogonalIdempotents.tensorProductEquiv`). Hence properties of `X` that
are compatible with finite products and with restriction of scalars along `T → T ⧸ (1 - f i)` can
be checked on each component; this file records it for module finiteness
(`TauCeti.Module.Finite.of_completeOrthogonalIdempotents`).

## Main declarations

* `CompleteOrthogonalIdempotents.tensorProductEquiv`: the splitting
  `X ≃ₐ[T] Π i, (T ⧸ (1 - f i)) ⊗[T] X`.
* `CompleteOrthogonalIdempotents.moduleTensorProductEquiv`: the module splitting
  `M ≃ₗ[T] Π i, (T ⧸ (1 - f i)) ⊗[T] M`.
* `TauCeti.Module.Finite.of_completeOrthogonalIdempotents`: a module is finite if its base
  change to every component is.
-/

public section

open TensorProduct

variable {T : Type*} [CommRing T]

namespace CompleteOrthogonalIdempotents

variable {ι : Type*} [Fintype ι] {f : ι → T}

/-- A complete orthogonal family of idempotents `f i` of `T` splits every `T`-algebra `X` into
the product of its base changes to the components `T ⧸ (1 - f i)`. -/
noncomputable def tensorProductEquiv (hf : CompleteOrthogonalIdempotents f) (X : Type*)
    [Semiring X] [Algebra T X] :
    X ≃ₐ[T] Π i, (T ⧸ Ideal.span {1 - f i}) ⊗[T] X :=
  open scoped Classical in
  (Algebra.TensorProduct.lid T X).symm.trans <|
    (Algebra.TensorProduct.congr
      (AlgEquiv.ofBijective (AlgHom.pi fun _ ↦ Ideal.Quotient.mkₐ T _) hf.bijective_pi)
      AlgEquiv.refl).trans <|
    (Algebra.TensorProduct.comm T _ X).trans <|
    (Algebra.TensorProduct.piRight T T X fun i ↦ T ⧸ Ideal.span {1 - f i}).trans <|
    AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.comm T X _

/-- Each component of the splitting sends `x` to `1 ⊗ₜ x`. -/
@[simp]
theorem tensorProductEquiv_apply (hf : CompleteOrthogonalIdempotents f) {X : Type*}
    [Semiring X] [Algebra T X] (x : X) (i : ι) :
    hf.tensorProductEquiv X x i = 1 ⊗ₜ x := by
  simp [tensorProductEquiv]

/-- A complete orthogonal family of idempotents `f i` of `T` splits every `T`-module `M` into
the product of its base changes to the components `T ⧸ (1 - f i)`. -/
noncomputable def moduleTensorProductEquiv (hf : CompleteOrthogonalIdempotents f) (M : Type*)
    [AddCommMonoid M] [Module T M] :
    M ≃ₗ[T] Π i, (T ⧸ Ideal.span {1 - f i}) ⊗[T] M :=
  open scoped Classical in
  (TensorProduct.lid T M).symm ≪≫ₗ
    TensorProduct.congr
      (AlgEquiv.ofBijective (AlgHom.pi fun _ ↦ Ideal.Quotient.mkₐ T _)
        hf.bijective_pi).toLinearEquiv
      (LinearEquiv.refl T M) ≪≫ₗ
    TensorProduct.piLeft (R := T) (N := M) (fun i ↦ T ⧸ Ideal.span {1 - f i})

/-- Each component of the module splitting sends `m` to `1 ⊗ₜ m`. -/
@[simp]
theorem moduleTensorProductEquiv_apply (hf : CompleteOrthogonalIdempotents f) {M : Type*}
    [AddCommMonoid M] [Module T M] (m : M) (i : ι) :
    hf.moduleTensorProductEquiv M m i = 1 ⊗ₜ m := by
  simp [moduleTensorProductEquiv]

end CompleteOrthogonalIdempotents

/-- Module finiteness is local for a decomposition of the base by complete orthogonal
idempotents: if the base change of `M` to every component `T ⧸ (1 - f i)` is finite, then `M` is
finite over `T`. -/
theorem TauCeti.Module.Finite.of_completeOrthogonalIdempotents {M : Type*} [AddCommMonoid M]
    [Module T M] {ι : Type*} [Fintype ι] {f : ι → T} (hf : CompleteOrthogonalIdempotents f)
    (h : ∀ i, Module.Finite (T ⧸ Ideal.span {1 - f i}) ((T ⧸ Ideal.span {1 - f i}) ⊗[T] M)) :
    Module.Finite T M := by
  have (i : ι) : Module.Finite T ((T ⧸ Ideal.span {1 - f i}) ⊗[T] M) := by
    have := h i
    exact Module.Finite.trans (T ⧸ Ideal.span {1 - f i}) _
  exact .equiv (hf.moduleTensorProductEquiv M).symm

namespace IsIdempotentElem

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {e : R}

private def balancedExtensionSpanSingletonFwd (he : IsIdempotentElem e) :
    (Ideal.span {e} : Ideal R) →ₛₗ[f] (Ideal.span {f e} : Ideal S) where
  toFun x := ⟨f x.val, (TauCeti.mem_span_singleton_iff_mul_eq_self (he.map f)).2 <| by
    rw [← map_mul, (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 x.property]⟩
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_smul' r x := Subtype.ext (map_mul f r x.val)

private theorem coe_balancedExtensionSpanSingletonFwd (he : IsIdempotentElem e)
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
noncomputable def balancedExtensionSpanSingletonEquiv (he : IsIdempotentElem e) :
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
theorem coe_balancedExtensionSpanSingletonEquiv_tmul (he : IsIdempotentElem e)
    (s : S) (x : (Ideal.span {e} : Ideal R)) :
    (he.balancedExtensionSpanSingletonEquiv f (TauCeti.BalancedExtension.tmul f s x) : S) =
      s * f x.val := by
  simp [balancedExtensionSpanSingletonEquiv, coe_balancedExtensionSpanSingletonFwd]

@[simp]
theorem balancedExtensionSpanSingletonEquiv_symm_apply (he : IsIdempotentElem e)
    (y : (Ideal.span {f e} : Ideal S)) :
    (he.balancedExtensionSpanSingletonEquiv f).symm y =
      y.val • TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e) :=
  balancedExtensionSpanSingletonInv_apply f e y

end Ring

end IsIdempotentElem
