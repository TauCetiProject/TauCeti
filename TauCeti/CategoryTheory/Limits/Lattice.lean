/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Finite products of reindexed families in a lattice

In a `SemilatticeInf` with `OrderTop`, Mathlib identifies the finite product of a family with the
infimum of its members (`CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf`). This
file records the reindexed form used for Čech complexes: the product of the members `f (a j)` of a
family `f`, for `a : J → ι` with `J` finite, is the infimum of `f` over the image of `a`.
-/

public section

universe u v w

namespace CategoryTheory.Limits.CompleteLattice

variable {α : Type u} [SemilatticeInf α] [OrderTop α]

/-- The finite product of the members `f (a j)` of a family `f` is the infimum of `f` over the
image of `a`. Unlike `finite_product_eq_finset_inf`, the index type `J` may live in any universe,
as for the products `U (a 0) × ⋯ × U (a n)` indexed by `Fin (n + 1)` in Čech complexes. -/
theorem finite_product_eq_finset_image_inf {ι : Type v} [DecidableEq ι] {J : Type w}
    [Fintype J] (f : ι → α) (a : J → ι) :
    (∏ᶜ fun j ↦ f (a j)) = (Finset.univ.image a).inf f := by
  rw [Finset.inf_image]
  refine (finite_limit_eq_finset_univ_inf _).trans ?_
  -- reindex the infimum over `Discrete J` along `discreteEquiv`
  rw [← Finset.univ_map_equiv_to_embedding (discreteEquiv (α := J)).symm, Finset.inf_map]
  rfl

end CategoryTheory.Limits.CompleteLattice
