/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Maps between tensor products of algebras

The base change `Algebra.TensorProduct.map (AlgHom.id R S) f : S ⊗[R] B → S ⊗[R] C` of an
algebra map `f : B →ₐ[R] C` agrees with `LinearMap.lTensor S` applied to the underlying linear
map of `f`. This lets results about base change of linear maps, such as flatness preserving
injectivity and exactness, be applied to base change of algebra maps.

For an `S`-algebra `B` over `R` which need not be commutative, the multiplication maps
`S ⊗[R] B → B` and `B ⊗[R] S → B` are `S`-algebra maps, because `S` acts through its central
image in `B`. Mathlib's `Algebra.TensorProduct.lmul''` and `Algebra.TensorProduct.productMap`
require a commutative target.

## Main declarations

* `AlgHom.lTensor_toLinearMap_apply`: `f.toLinearMap.lTensor S` is
  `Algebra.TensorProduct.map (AlgHom.id R S) f`.
* `TauCeti.Algebra.TensorProduct.mulLeft`, `TauCeti.Algebra.TensorProduct.mulRight`: the
  multiplication maps `s ⊗ b ↦ s • b` and `b ⊗ t ↦ b * t`.
* `TauCeti.Algebra.TensorProduct.map_assoc_tmul_one`: applying `f : B ⊗[R] C → D` after
  reassociating `y ⊗ 1` is the base change of `b ↦ f (b ⊗ 1)`.
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

open Algebra.TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]

/-- Reassociating `y ⊗ 1 ∈ (A ⊗[R] B) ⊗[R] C` and applying `f : B ⊗[R] C → D` to the last two
factors is the base change of `b ↦ f (b ⊗ 1)`. -/
theorem map_assoc_tmul_one {C D : Type*} [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
    (f : B ⊗[R] C →ₐ[R] D) (y : A ⊗[R] B) :
    map (AlgHom.id R A) f (Algebra.TensorProduct.assoc R R R A B C (y ⊗ₜ 1)) =
      map (AlgHom.id R A) (f.comp includeLeft) y := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

variable [Algebra S B]

/-- The image of `S` in the right factor is central in `A ⊗[R] B`. -/
theorem commute_one_tmul_algebraMap (x : A ⊗[R] B) (t : S) :
    Commute x (1 ⊗ₜ algebraMap S B t) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact (Commute.one_right a).tmul (Algebra.commute_algebraMap_right t b)
  | add x y hx hy => exact hx.add_left hy

variable [Algebra R S] [IsScalarTower R S B]

/-- The multiplication map `S ⊗[R] B →ₐ[S] B`, `s ⊗ b ↦ s • b`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulLeft : S ⊗[R] B →ₐ[S] B :=
  lift (Algebra.ofId S B) (AlgHom.id R B)
    (fun s b ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _)

@[simp]
theorem mulLeft_tmul (s : S) (b : B) :
    (mulLeft (s ⊗ₜ[R] b) : B) = algebraMap S B s * b := by
  simp [mulLeft]

/-- The multiplication map `B ⊗[R] S →ₐ[S] B`, `b ⊗ t ↦ b * t`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulRight : B ⊗[R] S →ₐ[S] B :=
  lift (AlgHom.id S B) (IsScalarTower.toAlgHom R S B)
    (fun b t ↦ by rw [IsScalarTower.coe_toAlgHom']; exact Algebra.commute_algebraMap_right t b)

@[simp]
theorem mulRight_tmul (b : B) (t : S) :
    (mulRight (b ⊗ₜ[R] t) : B) = b * algebraMap S B t := by
  simp [mulRight]

end TauCeti.Algebra.TensorProduct
