/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# A multilinear map as a bilinear map in two of its arguments

Mathlib's `MultilinearMap.toLinearMap f m i` fixes all arguments of a multilinear map `f` but the
`i`-th to those of `m` and varies the `i`-th one. This file does the same with two distinct
arguments `i ≠ j`: `MultilinearMap.toLinearMap₂ f m hij` is the bilinear map
`(x, y) ↦ f (m with x in slot i and y in slot j)`.

For instance, applied to `PiTensorProduct.tprod`, it places two vectors into two entries of a pure
tensor, which transports an identity in a binary tensor product into any two entries of a pure
tensor of higher arity.

## Main definitions

* `MultilinearMap.toLinearMap₂`: a multilinear map as a bilinear map in two distinct arguments.
-/

public section

open Function

namespace MultilinearMap

variable {R ι N : Type*} {M : ι → Type*} [CommSemiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N] [DecidableEq ι]

/-- The bilinear map obtained from a multilinear map `f` by fixing all arguments but the
distinct `i`-th and `j`-th ones to those of `m`: `(x, y) ↦ f (update (update m j y) i x)`. -/
def toLinearMap₂ (f : (Π k, M k) →ₘₗ[R] N) (m : Π k, M k) {i j : ι} (hij : i ≠ j) :
    M i →ₗ[R] M j →ₗ[R] N :=
  LinearMap.mk₂ R (fun x y ↦ f (update (update m j y) i x))
    (fun x x' y ↦ by simp) (fun c x y ↦ by simp)
    (fun x y y' ↦ by
      rw [update_comm hij.symm, update_comm hij.symm, update_comm hij.symm]
      simp)
    (fun c x y ↦ by
      rw [update_comm hij.symm, update_comm hij.symm]
      simp)

/-- `f.toLinearMap₂ m hij` evaluates `f` at `m` with `x` in slot `i` and `y` in slot `j`. -/
@[simp]
theorem toLinearMap₂_apply (f : (Π k, M k) →ₘₗ[R] N) (m : Π k, M k) {i j : ι} (hij : i ≠ j)
    (x : M i) (y : M j) :
    f.toLinearMap₂ m hij x y = f (update (update m j y) i x) := by
  simp [toLinearMap₂]

end MultilinearMap
