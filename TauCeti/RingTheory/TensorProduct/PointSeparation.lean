/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Detecting zero tensors by rational points

Families of rational points detecting zero in two algebras also detect zero in their tensor
product over a commutative semiring when the right algebra is projective as a module. This
lets one check tensor vanishing on products of those families, without any finite-type or
algebraic-closedness hypothesis. Over a field, every module is projective.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Products of families of rational points detecting zero in each algebra detect zero in
the tensor product when the right algebra is projective as a module. -/
theorem tensor_eq_zero_of_forall_productMap_eq_zero
    {R A B ι κ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Module.Projective R B]
    (f : ι → A →ₐ[R] R) (g : κ → B →ₐ[R] R)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0)
    (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    (x : A ⊗[R] B) (hx : ∀ i j, Algebra.TensorProduct.productMap (f i) (g j) x = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_lid_map_eq_zero
    (fun i ↦ (f i).toLinearMap) (fun j ↦ (g j).toLinearMap) hf hg x
  intro i j
  have heq : (TensorProduct.lid R R).toLinearMap.comp
      (TensorProduct.map (f i).toLinearMap (g j).toLinearMap) =
      (Algebra.TensorProduct.productMap (f i) (g j)).toLinearMap := by
    ext a b
    simp
  exact (DFunLike.congr_fun heq x).trans (hx i j)

end TauCeti
