/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Flatness and tensor products of algebra homomorphisms

Mathlib's `TensorProduct.map_injective_of_flat_flat` shows that the tensor product of two
injective linear maps is injective when the codomain of the first and the domain of the second
are flat. This file records the same statement for `Algebra.TensorProduct.map` of algebra
homomorphisms, so that it applies without first passing to the underlying linear maps.
It also identifies the kernel after tensoring an algebra map with a flat algebra, the analogue
of Mathlib's `Algebra.TensorProduct.lTensor_ker` with flatness in place of surjectivity.

## Main results

* `Algebra.TensorProduct.map_injective_of_flat_flat`: the tensor product of two injective algebra
  homomorphisms is injective under the flatness hypotheses of
  `TensorProduct.map_injective_of_flat_flat`.
* `Algebra.TensorProduct.lTensor_ker_of_flat`: tensoring with a flat algebra carries kernels
  to their images under the right tensor inclusion.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

section Semiring

variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
variable [Algebra S A] [Algebra S B] [IsScalarTower R S A] [IsScalarTower R S B]

/-- The tensor product of two injective algebra homomorphisms is injective when the codomain of
the first and the domain of the second are flat. -/
theorem map_injective_of_flat_flat (f : A →ₐ[S] B) (g : C →ₐ[R] D)
    [Module.Flat R B] [Module.Flat R C]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map f g) :=
  -- `map f g` is `TensorProduct.map` of the underlying `R`-linear maps by definition.
  _root_.TensorProduct.map_injective_of_flat_flat (f.toLinearMap.restrictScalars R)
    g.toLinearMap hf hg

end Semiring

section Ring

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R A]

/-- Tensoring an algebra map with a flat algebra carries its kernel to the ideal generated
by its image under the right tensor inclusion. -/
theorem lTensor_ker_of_flat (f : B →ₐ[R] C) :
    RingHom.ker (map (AlgHom.id R A) f) =
      (RingHom.ker f).map (includeRight : B →ₐ[R] A ⊗[R] B) := by
  rw [← Submodule.restrictScalars_inj R, Ideal.map_includeRight_eq]
  -- Restricted to `R`, `RingHom.ker` of `map (AlgHom.id R A) f` and of `f` are by definition the
  -- `LinearMap.ker` of `LinearMap.lTensor A f.toLinearMap` and of `f.toLinearMap`.
  exact (Module.Flat.lTensor_exact A f.toLinearMap.exact_subtype_ker_map).linearMap_ker_eq

end Ring

end Algebra.TensorProduct
