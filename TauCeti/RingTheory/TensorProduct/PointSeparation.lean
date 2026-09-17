/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Separating tensors by rational points

Separating families of rational points on two algebras also separate their tensor product.
This lets one check equations on products of separating families of rational points, without
any finite-type or algebraic-closedness hypothesis. The proof specializes the linear separation
lemmas in `TauCeti.LinearAlgebra.TensorProduct.Separation`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Products of separating families of rational points separate the tensor product. -/
theorem tensor_eq_zero_of_forall_productMap_eq_zero
    {k A B ι κ : Type*} [Field k] [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    (f : ι → A →ₐ[k] k) (g : κ → B →ₐ[k] k)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0)
    (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    (x : A ⊗[k] B) (hx : ∀ i j, Algebra.TensorProduct.productMap (f i) (g j) x = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_lid_map_eq_zero
    (fun i ↦ (f i).toLinearMap) (fun j ↦ (g j).toLinearMap) hf hg x
  intro i j
  have heq : (TensorProduct.lid k k).toLinearMap.comp
      (TensorProduct.map (f i).toLinearMap (g j).toLinearMap) =
      (Algebra.TensorProduct.productMap (f i) (g j)).toLinearMap := by
    ext a b
    simp
  exact (DFunLike.congr_fun heq x).trans (hx i j)

end TauCeti
