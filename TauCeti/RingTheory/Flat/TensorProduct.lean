/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Injectivity of tensor products of algebra maps under flatness

Mathlib's `TensorProduct.map_injective_of_flat_flat` shows that the tensor product of two
injective linear maps is injective when the codomain of the first and the domain of the second
are flat. This file records the same statement for `Algebra.TensorProduct.map` of algebra
homomorphisms, so that it applies without first passing to the underlying linear maps.

## Main results

* `Algebra.TensorProduct.map_injective_of_flat_flat`: the tensor product of two injective algebra
  homomorphisms is injective under the flatness hypotheses of
  `TensorProduct.map_injective_of_flat_flat`.
-/

public section

namespace Algebra.TensorProduct

variable {R A B C D : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- The tensor product of two injective algebra homomorphisms is injective when the codomain of
the first and the domain of the second are flat. -/
theorem map_injective_of_flat_flat (f : A →ₐ[R] B) (g : C →ₐ[R] D)
    [Module.Flat R B] [Module.Flat R C]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map f g) := by
  have h := _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  rwa [← TensorProduct.AlgebraTensorModule.map_eq, ← toLinearMap_map, AlgHom.coe_toLinearMap] at h

end Algebra.TensorProduct
