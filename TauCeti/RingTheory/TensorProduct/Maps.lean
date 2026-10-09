/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of algebra maps as linear maps

The base change `Algebra.TensorProduct.map (AlgHom.id R S) f : S ⊗[R] B → S ⊗[R] C` of an
algebra map `f : B →ₐ[R] C` agrees with `LinearMap.lTensor S` applied to the underlying linear
map of `f`. This lets results about base change of linear maps, such as flatness preserving
injectivity and exactness, be applied to base change of algebra maps.

## Main declarations

* `AlgHom.lTensor_toLinearMap_apply`: `f.toLinearMap.lTensor S` is
  `Algebra.TensorProduct.map (AlgHom.id R S) f`.
-/

public section

open TensorProduct

/-- Base change of the underlying linear map of an algebra map is the base change of the
algebra map. -/
theorem AlgHom.lTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommRing R] [Ring S]
    [Algebra R S] [Ring B] [Algebra R B] [Ring C] [Algebra R C] (f : B →ₐ[R] C)
    (x : S ⊗[R] B) :
    f.toLinearMap.lTensor S x = Algebra.TensorProduct.map (AlgHom.id R S) f x := by
  induction x using TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp [hx, hy]
