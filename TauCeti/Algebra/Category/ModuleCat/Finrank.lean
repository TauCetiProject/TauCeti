/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finrank of zero objects and biproducts in `ModuleCat`

Vanishing and direct sums of objects of `ModuleCat R` are naturally expressed categorically, as
`CategoryTheory.Limits.IsZero` and biproducts `M ⊞ N`, while the dimension counts that consume them
speak of `Module.finrank`. This file supplies the translations between the two: a zero object has
finrank zero, and finrank is additive on biproducts of finite free modules
(`ModuleCat.finrank_biprod`, the analogue of `FGModuleCat.finrank_biprod`).

The first translation is what bounds the `Module.finrank` support of a bounded complex of vector
spaces by its bounding interval, which is in turn what makes Mathlib's `finsum`-based Euler
characteristic of such a complex an honest finite sum.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] [Nontrivial R]

/-- A zero object in `ModuleCat R` has finrank zero. -/
theorem finrank_eq_zero_of_isZero {X : ModuleCat.{v} R} (hX : IsZero X) :
    Module.finrank R X = 0 := by
  let _ : Subsingleton X := ModuleCat.subsingleton_of_isZero hX
  exact Module.finrank_zero_of_subsingleton

/-- The finrank of a biproduct of finite free modules is the sum of their finranks. -/
@[simp]
theorem finrank_biprod {R : Type u} [Ring R] [StrongRankCondition R] (M N : ModuleCat.{v} R)
    [Module.Free R M] [Module.Free R N] [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R ↑(M ⊞ N) = Module.finrank R M + Module.finrank R N :=
  (biprodIsoProd M N).toLinearEquiv.finrank_eq.trans Module.finrank_prod

end ModuleCat
