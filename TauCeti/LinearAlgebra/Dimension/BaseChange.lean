/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The dimension of a base change

A module specified as a base change of a finite module is finite. If the module being extended is
free and the target semiring is nontrivial, then the two modules have the same
natural-number rank (`Module.finrank`), including when their rank is infinite and `finrank` is zero.
Both statements are about Mathlib's `IsBaseChange` predicate rather than about the concrete tensor
product `S ⊗[R] M`, so they apply to a model of the base change that is not literally a tensor
product — the situation the `IsBaseChange` interface exists to serve.

Mathlib proves the corresponding facts for the concrete tensor product (`Module.finrank_baseChange`
and the `Module.Finite` instance on `S ⊗[R] M`); transporting them along
`IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N` is all that is needed.
-/

public section

namespace IsBaseChange

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N]
variable [IsScalarTower R S N] {f : M →ₗ[R] N}

/-- A base change of a finite module is a finite module. -/
theorem finite (hf : IsBaseChange S f) [Module.Finite R M] : Module.Finite S N :=
  Module.Finite.equiv hf.equiv

/-- A base change of a free module to a nontrivial semiring preserves `Module.finrank`. No
finite-generation assumption is needed. -/
theorem finrank_eq_of_free (hf : IsBaseChange S f) [Nontrivial S] [Module.Free R M] :
    Module.finrank S N = Module.finrank R M := by
  -- Nontrivial commutative semirings satisfy the strong rank condition
  -- (`CommSemiring.strongRankCondition_of_nontrivial`), and `R` is nontrivial because `S` is.
  have := (algebraMap R S).domain_nontrivial
  rw [← hf.equiv.finrank_eq, Module.finrank_baseChange]

end IsBaseChange
