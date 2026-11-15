/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Finiteness of tensor products over a larger scalar ring

Let `S` be an `R`-algebra, `M` a finite `S`-module and `N` a finite `R`-module. Then `M ⊗[R] N`,
with `S` acting through `M`, is a finite `S`-module. This is the finiteness counterpart of
Mathlib's `Module.Free.tensor`; Mathlib's `Module.Finite.tensorProduct` is the case `S = R` and
`Module.Finite.base_change` the case `M = S`.

Conversely, tensoring with a nonzero free module reflects finiteness: a coordinate functional of
such a module is onto the scalars, so it exhibits `M` as a quotient of the tensor product.

## Main results

* `Module.Finite.tensor`: `M ⊗[R] N` is finite over `S`.
* `Module.Finite.of_tensorProduct_left`: if `M ⊗[R] N` is finite and `N` is free and nonzero,
  then `M` is finite.
* `Module.Finite.of_tensorProduct_self`: a free module whose tensor square is finite is finite.
* `Module.Finite.of_baseChange`: a free module whose base change to a nontrivial algebra is finite
  is finite.
-/

public section

open TensorProduct

namespace Module.Finite

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

/-- The tensor product of a finite `S`-module with a finite `R`-module is a finite `S`-module. -/
instance tensor [Module.Finite S M] [Module.Finite R N] : Module.Finite S (M ⊗[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  exact .of_surjective ((AlgebraTensorModule.lTensor S M f) ∘ₗ
    (TensorProduct.piScalarRight R S M (Fin n)).symm.toLinearMap)
    ((LinearMap.lTensor_surjective M hf).comp (LinearEquiv.surjective _))

/-- If `M ⊗[R] N` is finite and `N` is free and nonzero, then `M` is finite: a coordinate
functional of `N` is onto `R`, so `M ≃ M ⊗[R] R` is a quotient of `M ⊗[R] N`. No freeness or
finiteness of `M` is assumed. -/
theorem of_tensorProduct_left [Module.Free R N] [Nontrivial N]
    (h : Module.Finite R (M ⊗[R] N)) : Module.Finite R M := by
  let b := Module.Free.chooseBasis R N
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex R N) := b.index_nonempty
  have hsurj : Function.Surjective (b.coord i) := fun r ↦ ⟨r • b i, by simp⟩
  exact .of_surjective ((TensorProduct.rid R M).toLinearMap ∘ₗ LinearMap.lTensor M (b.coord i))
    ((TensorProduct.rid R M).surjective.comp (LinearMap.lTensor_surjective M hsurj))

/-- A free module whose tensor square is finite is itself finite. -/
theorem of_tensorProduct_self [Module.Free R M] (h : Module.Finite R (M ⊗[R] M)) :
    Module.Finite R M := by
  obtain hM | hM := subsingleton_or_nontrivial M
  · infer_instance
  · exact of_tensorProduct_left h

/-- A free module whose base change to a nontrivial algebra is finite is itself finite: the
base change of a basis is a basis of the same index type. -/
theorem of_baseChange {R S N : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [Nontrivial S] [AddCommMonoid N] [Module R N] [Module.Free R N]
    (h : Module.Finite S (S ⊗[R] N)) : Module.Finite R N := by
  let b := Module.Free.chooseBasis R N
  have := Module.Finite.finite_basis (Algebra.TensorProduct.basis S b)
  exact Module.Finite.of_basis b

end Module.Finite
