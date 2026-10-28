/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Base change of bilinear maps along algebra maps

The scalar extension `LinearMap.BilinMap.baseChange S C` of an `R`-bilinear map `C` is natural in
the commutative `R`-algebra `S`: an `R`-algebra map `φ : S →ₐ[R] T` intertwines the base changes
to `S` and to `T`. It is also natural in the modules: it commutes with precomposition by linear
maps of the arguments and with postcomposition by a linear map of the target.

## Main declarations

* `LinearMap.BilinMap.rTensor_baseChange_apply`: the base change of a bilinear map commutes with
  algebra maps between scalar algebras.
* `LinearMap.BilinMap.baseChange_compl₁₂` and `LinearMap.BilinMap.baseChange_compr₂`: the base
  change of a bilinear map commutes with precomposition and postcomposition by linear maps.
-/

public section

open TensorProduct
open LinearMap (BilinMap)

namespace LinearMap

variable {R : Type*} [CommSemiring R]
variable {M P : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]
variable {M' P' : Type*} [AddCommMonoid M'] [Module R M'] [AddCommMonoid P'] [Module R P']

/-- The base change of a bilinear map commutes with an algebra map `φ : S →ₐ[R] T` between scalar
algebras: `φ (C_S x y) = C_T (φ x) (φ y)`. -/
theorem BilinMap.rTensor_baseChange_apply (C : BilinMap R M P) {S T : Type*} [CommSemiring S]
    [Algebra R S] [CommSemiring T] [Algebra R T] (φ : S →ₐ[R] T) (x y : S ⊗[R] M) :
    φ.toLinearMap.rTensor P (BilinMap.baseChange S C x y) =
      BilinMap.baseChange T C (φ.toLinearMap.rTensor M x) (φ.toLinearMap.rTensor M y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, add_apply, hx, hx']
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t n => simp

/-- The base change of a bilinear map commutes with precomposition by linear maps of its
arguments. -/
theorem BilinMap.baseChange_compl₁₂ (C : BilinMap R M P) (f g : M' →ₗ[R] M) (S : Type*)
    [CommSemiring S] [Algebra R S] :
    BilinMap.baseChange S (C.compl₁₂ f g) =
      (BilinMap.baseChange S C).compl₁₂ (f.baseChange S) (g.baseChange S) := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, add_apply, hx, hx']
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t n => simp

/-- The base change of a bilinear map commutes with postcomposition by a linear map of its
target. -/
theorem BilinMap.baseChange_compr₂ (C : BilinMap R M P) (h : P →ₗ[R] P') (S : Type*)
    [CommSemiring S] [Algebra R S] :
    BilinMap.baseChange S (C.compr₂ h) = (BilinMap.baseChange S C).compr₂ (h.baseChange S) := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, add_apply, hx, hx']
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t n => simp

end LinearMap
