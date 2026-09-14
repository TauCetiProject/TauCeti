/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic

/-!
# Injectivity of tensor-product algebra morphisms

This file transfers injectivity of two algebra morphisms over a commutative semiring to their
tensor-product algebra morphism. For maps `A → B` and `C → D`, flatness of `B` and `C` suffices:
factor the tensor map through `B ⊗ C` and use preservation of injections by each flat factor.

## Main declarations

* `TauCeti.Algebra.TensorProduct.map_injective_of_injective`: tensoring two injective algebra
  morphisms gives an injective tensor-product algebra morphism under these flatness assumptions.

## References

The result is the algebra-morphism form of Mathlib's
`TensorProduct.map_injective_of_flat_flat`.
-/

public section

namespace TauCeti.Algebra.TensorProduct

universe u v w x y

variable {k : Type u} [CommSemiring k]

/-- The tensor product of injective algebra morphisms `A → B` and `C → D` is injective when
`B` and `C` are flat over the base. -/
theorem map_injective_of_injective {A : Type v} {B : Type w} {C : Type x} {D : Type y}
    [Semiring A] [Semiring B] [Semiring C] [Semiring D]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    [Module.Flat k B] [Module.Flat k C]
    (f : A →ₐ[k] B) (g : C →ₐ[k] D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (_root_.Algebra.TensorProduct.map f g) := by
  -- Expose the underlying linear map so the named tensor-product map lemmas can rewrite it.
  change Function.Injective (_root_.Algebra.TensorProduct.map f g).toLinearMap
  rw [_root_.Algebra.TensorProduct.toLinearMap_map,
    _root_.TensorProduct.AlgebraTensorModule.map_eq]
  exact _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

end TauCeti.Algebra.TensorProduct
