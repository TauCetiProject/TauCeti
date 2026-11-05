/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Coproduct tensors and finite products

Tensoring a finite product of modules over a bialgebra distributes over that product.
The underlying equivalences are Mathlib's `TensorProduct.piLeft` and
`TensorProduct.piRight`; the component maps are tensor products of module projections.
These equivalences let one iterate finite module decompositions without losing the
coproduct action.
-/

public noncomputable section

namespace TauCeti.BialgebraModule

variable (R H : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, Module H (M i)] [∀ i, IsScalarTower R H (M i)]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module H N] [IsScalarTower R H N]

/-- Coproduct tensor products distribute over finite products in their left factor. -/
def piLeft : Tensor R H (∀ i, M i) N ≃ₗ[H] ∀ i, Tensor R H (M i) N :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => tensorMap R H (LinearMap.proj i) LinearMap.id)
    (by
      let e := (tensorEquiv R H (∀ i, M i) N).trans
        ((TensorProduct.piLeft R N M).trans
          (LinearEquiv.piCongrRight fun i => (tensorEquiv R H (M i) N).symm))
      convert e.bijective using 1
      ext x i
      induction x using Tensor.inductionOn with
      | htmul m n => simp [e, TensorProduct.piLeft]
      | hadd x y hx hy => simp only [map_add, Pi.add_apply, hx, hy])

/-- Each component of `piLeft` is the tensor product of the corresponding projection
with the identity. -/
theorem piLeft_apply (x : Tensor R H (∀ i, M i) N) (i : ι) :
    piLeft R H M N x i = tensorMap R H (LinearMap.proj i) LinearMap.id x := (rfl)

/-- The finite-product comparison evaluates pure tensors componentwise. -/
@[simp] theorem piLeft_tmul (m : ∀ i, M i) (n : N) (i : ι) :
    piLeft R H M N (tmul R H m n) i = tmul R H (m i) n := by
  simp [piLeft_apply]

/-- The inverse comparison inserts a pure tensor into one product component. -/
@[simp] theorem piLeft_symm_single_tmul (i : ι) (m : M i) (n : N) :
    (piLeft R H M N).symm (Pi.single i (tmul R H m n)) =
      tmul R H (Pi.single i m) n := by
  apply (piLeft R H M N).injective
  funext j
  simpa only [LinearEquiv.apply_symm_apply, piLeft_tmul] using
    (Pi.apply_single (fun k x => tmul R H (M := M k) x n)
      (fun _ => zero_tmul R H n) i m j).symm

/-- The inverse left comparison inserts an arbitrary tensor into one component. -/
theorem piLeft_symm_single (i : ι) (x : Tensor R H (M i) N) :
    (piLeft R H M N).symm (Pi.single i x) =
      tensorMap R H (LinearMap.single _ _ i) LinearMap.id x := by
  induction x using Tensor.inductionOn with
  | htmul m n => simp
  | hadd x y hx hy => simp only [map_add, Pi.single_add, hx, hy]

/-- Coproduct tensor products distribute over finite products in their right factor. -/
def piRight : Tensor R H N (∀ i, M i) ≃ₗ[H] ∀ i, Tensor R H N (M i) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => tensorMap R H LinearMap.id (LinearMap.proj i))
    (by
      let e := (tensorEquiv R H N (∀ i, M i)).trans
        ((TensorProduct.piRight R R N M).trans
          (LinearEquiv.piCongrRight fun i => (tensorEquiv R H N (M i)).symm))
      convert e.bijective using 1
      ext x i
      induction x using Tensor.inductionOn with
      | htmul n m => simp [e]
      | hadd x y hx hy => simp only [map_add, Pi.add_apply, hx, hy])

/-- Each component of `piRight` is the tensor product of the identity with the
corresponding projection. -/
theorem piRight_apply (x : Tensor R H N (∀ i, M i)) (i : ι) :
    piRight R H M N x i = tensorMap R H LinearMap.id (LinearMap.proj i) x := (rfl)

/-- The finite-product comparison evaluates pure tensors componentwise. -/
@[simp] theorem piRight_tmul (n : N) (m : ∀ i, M i) (i : ι) :
    piRight R H M N (tmul R H n m) i = tmul R H n (m i) := by
  simp [piRight_apply]

/-- The inverse comparison inserts a pure tensor into one product component. -/
@[simp] theorem piRight_symm_single_tmul (i : ι) (n : N) (m : M i) :
    (piRight R H M N).symm (Pi.single i (tmul R H n m)) =
      tmul R H n (Pi.single i m) := by
  apply (piRight R H M N).injective
  funext j
  simpa only [LinearEquiv.apply_symm_apply, piRight_tmul] using
    (Pi.apply_single (fun k x => tmul R H (N := M k) n x)
      (fun _ => tmul_zero R H n) i m j).symm

/-- The inverse right comparison inserts an arbitrary tensor into one component. -/
theorem piRight_symm_single (i : ι) (x : Tensor R H N (M i)) :
    (piRight R H M N).symm (Pi.single i x) =
      tensorMap R H LinearMap.id (LinearMap.single _ _ i) x := by
  induction x using Tensor.inductionOn with
  | htmul n m => simp
  | hadd x y hx hy => simp only [map_add, Pi.single_add, hx, hy]

end TauCeti.BialgebraModule
