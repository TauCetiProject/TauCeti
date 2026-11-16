/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TensorProduct.Pi

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
