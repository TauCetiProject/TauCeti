/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Commuting squares of linear maps in the category of modules

A commuting square of linear maps gives a commuting square of the corresponding morphisms
`ModuleCat.ofHom` in the category of `R`-modules.

## Main results

* `ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq`: if `g' ∘ₗ f = f' ∘ₗ g` then
  `ofHom f ≫ ofHom g' = ofHom g ≫ ofHom f'`.

## Implementation notes

The lemma is meant to be applied as a term (`exact ofHom_comp_ofHom_eq_of_comp_eq h`). When the
objects of the goal are, say, the objects of a chain complex built by `ChainComplex.of` that agree
with `ModuleCat.of R M` only up to unfolding, `rw [← ModuleCat.ofHom_comp]` cannot match the goal,
whereas elaborating this lemma against it unifies the objects up to definitional unfolding.
-/

public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] {M N P Q : Type v} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N] [Module R P] [Module R Q]

/-- A commuting square of linear maps gives a commuting square of `ModuleCat.ofHom`s. -/
theorem ofHom_comp_ofHom_eq_of_comp_eq {f : M →ₗ[R] N} {g' : N →ₗ[R] Q} {g : M →ₗ[R] P}
    {f' : P →ₗ[R] Q} (h : g' ∘ₗ f = f' ∘ₗ g) : ofHom f ≫ ofHom g' = ofHom g ≫ ofHom f' := by
  rw [← ofHom_comp, ← ofHom_comp, h]

end ModuleCat
