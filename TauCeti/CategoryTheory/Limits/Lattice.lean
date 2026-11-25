/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import TauCeti.Data.Finset.Image

/-!
# Finite products of reindexed families in a lattice

In a `SemilatticeInf` with `OrderTop`, Mathlib identifies the finite product of a family with the
infimum of its members (`CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf`). This
file records the reindexed form used for Čech complexes: the product of the members `f (a j)` of a
family `f`, for `a : J → ι` with `J` finite, is the infimum of `f` over the image of `a`. Hence a
property of the nonempty finite infima of `f` holds for the products `f (a 0) × ⋯ × f (a n)`.
In `(Finset ι)ᵒᵈ` (ordered by reverse inclusion), this identifies the finite product of singletons
`toDual {a j}` with `Finset.univ.image a` (`ofDual_finite_product_toDual_singleton`), which equals
`Finset.univ` if and only if `a` is surjective
(`ofDual_finite_product_toDual_singleton_eq_univ_iff`).
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

/-- A property of the nonempty finite infima of a family `f` holds for the nonempty finite products
of its members `f (a j)`, such as the products `f (a 0) × ⋯ × f (a n)` in the terms of Čech
complexes: such a product is the infimum of `f` over the image of `a`. -/
theorem finite_product_of_forall_finset_inf {ι : Type v} {p : α → Prop} (f : ι → α)
    (h : ∀ s : Finset ι, s.Nonempty → p (s.inf f)) {J : Type w} [Finite J] [Nonempty J]
    (a : J → ι) : p (∏ᶜ fun j ↦ f (a j)) := by
  classical
  have := Fintype.ofFinite J
  exact finite_product_eq_finset_image_inf f a ▸ h _ (Finset.univ_nonempty.image a)

/-- In `(Finset ι)ᵒᵈ` (ordered by reverse inclusion), the finite product of the singletons
`toDual {a j}` is the image of `a`. -/
theorem ofDual_finite_product_toDual_singleton {ι : Type u} [DecidableEq ι] {J : Type v}
    [Fintype J] (a : J → ι) :
    OrderDual.ofDual (∏ᶜ fun j ↦ (OrderDual.toDual ({a j} : Finset ι))) =
      Finset.univ.image a := by
  rw [finite_product_eq_finset_image_inf (fun i : ι ↦ (OrderDual.toDual ({i} : Finset ι))) a,
    Finset.ofDual_inf]
  exact Finset.sup_singleton_eq_self _

open scoped Classical in
/-- In `(Finset ι)ᵒᵈ` (ordered by reverse inclusion), the finite product of the singletons
`toDual {a j}` equals `Finset.univ` if and only if `a` is surjective. -/
theorem ofDual_finite_product_toDual_singleton_eq_univ_iff {ι : Type u} [Fintype ι] {J : Type v}
    [Finite J] (a : J → ι) :
    OrderDual.ofDual (∏ᶜ fun j ↦ (OrderDual.toDual ({a j} : Finset ι))) = Finset.univ ↔
      Function.Surjective a := by
  have := Fintype.ofFinite J
  rw [ofDual_finite_product_toDual_singleton, Finset.image_univ_eq_univ_iff]

end CategoryTheory.Limits.CompleteLattice
