/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensor products of equivalent quadratic forms

This file shows that tensor products preserve isometric equivalences and equivalence of quadratic
forms. It complements Mathlib's tensor product of quadratic-form isometries.

## Main definitions

* `QuadraticMap.IsometryEquiv.tmul`: the tensor product of two isometric equivalences.
* `QuadraticMap.Equivalent.tmul`: tensor products preserve equivalence of quadratic forms.
* `QuadraticForm.IsometryEquiv.tmulProd`: tensor product distributes over orthogonal product.
-/

public section

namespace TauCeti

open scoped TensorProduct
open QuadraticMap

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Tensor product of isometric equivalences of quadratic forms. -/
def _root_.QuadraticMap.IsometryEquiv.tmul
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {S₁ : QuadraticForm R N₁} {S₂ : QuadraticForm R N₂}
    (e : Q₁.IsometryEquiv Q₂) (f : S₁.IsometryEquiv S₂) :
    (Q₁.tmul S₁).IsometryEquiv (Q₂.tmul S₂) where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  map_app' x := QuadraticForm.tmul_tensorMap_apply e.toIsometry f.toIsometry x

/-- The tensor product of two isometric equivalences acts componentwise on pure tensors. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.tmul_tmul
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {S₁ : QuadraticForm R N₁} {S₂ : QuadraticForm R N₂}
    (e : Q₁.IsometryEquiv Q₂) (f : S₁.IsometryEquiv S₂) (x : M₁) (y : N₁) :
    e.tmul f (x ⊗ₜ[R] y) = e x ⊗ₜ[R] f y :=
  TensorProduct.congr_tmul e.toLinearEquiv f.toLinearEquiv x y

/-- Tensor product preserves equivalence of quadratic forms. -/
theorem _root_.QuadraticMap.Equivalent.tmul
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {S₁ : QuadraticForm R N₁} {S₂ : QuadraticForm R N₂}
    (hQ : Q₁.Equivalent Q₂) (hS : S₁.Equivalent S₂) :
    (Q₁.tmul S₁).Equivalent (Q₂.tmul S₂) :=
  Nonempty.map2 QuadraticMap.IsometryEquiv.tmul hQ hS

/-- Tensor product distributes over the orthogonal product of quadratic forms. -/
def _root_.QuadraticForm.IsometryEquiv.tmulProd
    {M N P : Type*}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (Q : QuadraticForm R M) (S : QuadraticForm R N) (T : QuadraticForm R P) :
    (Q.tmul (S.prod T)).IsometryEquiv ((Q.tmul S).prod (Q.tmul T)) where
  toLinearEquiv := TensorProduct.prodRight R R M N P
  map_app' x := by
    rw [← associated_eq_self_apply (S := R), ← associated_eq_self_apply (S := R)]
    have hassoc :
        (associated ((Q.tmul S).prod (Q.tmul T))).compl₁₂
            (TensorProduct.prodRight R R M N P).toLinearMap
            (TensorProduct.prodRight R R M N P).toLinearMap =
          associated (Q.tmul (S.prod T)) := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro m np
      apply TensorProduct.AlgebraTensorModule.ext
      intro m' np'
      rcases np with ⟨n, p⟩
      rcases np' with ⟨n', p'⟩
      simp [QuadraticMap.associated_prod, QuadraticForm.associated_tmul, add_mul]
    exact DFunLike.congr_fun (DFunLike.congr_fun hassoc x) x

/-- The distributivity isometry acts on a pure tensor by projecting its product-valued
factor. -/
@[simp]
theorem _root_.QuadraticForm.IsometryEquiv.tmulProd_tmul
    {M N P : Type*}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (Q : QuadraticForm R M) (S : QuadraticForm R N) (T : QuadraticForm R P)
    (m : M) (np : N × P) :
    QuadraticForm.IsometryEquiv.tmulProd Q S T (m ⊗ₜ[R] np) =
      (m ⊗ₜ[R] np.1, m ⊗ₜ[R] np.2) :=
  TensorProduct.prodRight_tmul R R M N P m np

/-- The inverse distributivity isometry combines a pair of pure tensors with the same first
factor into a pure tensor with product-valued second factor. -/
@[simp]
theorem _root_.QuadraticForm.IsometryEquiv.tmulProd_symm_tmul
    {M N P : Type*}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (Q : QuadraticForm R M) (S : QuadraticForm R N) (T : QuadraticForm R P)
    (m : M) (n : N) (p : P) :
    (QuadraticForm.IsometryEquiv.tmulProd Q S T).symm (m ⊗ₜ[R] n, m ⊗ₜ[R] p) =
      m ⊗ₜ[R] (n, p) :=
  TensorProduct.prodRight_symm_tmul R R M N P m n p

end TauCeti
