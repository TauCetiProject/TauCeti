/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Modules of bounded cardinal rank

For any ring `R` and cardinal `μ`, `ModuleCat.rankLe R μ` is the object property of `R`-modules of
cardinal rank at most `μ`. Because `Module.rank R` does not increase along injective or surjective
linear maps (`LinearMap.rank_le_of_injective`, `LinearMap.rank_le_of_surjective`),
`ModuleCat.rankLe R μ` is closed under subobjects and quotients, so rank bounds propagate through
categorical subquotients such as homology and spectral sequence pages.

## Main definitions and results

* `ModuleCat.rankLe`: the object property `Module.rank R M ≤ μ` on `ModuleCat.{v} R`.
* `ModuleCat.rankLe_iff`: membership in `ModuleCat.rankLe R μ` is `Module.rank R M ≤ μ`.
* `ModuleCat.rankLe R μ` has instances of `CategoryTheory.ObjectProperty.IsClosedUnderSubobjects`
  and `CategoryTheory.ObjectProperty.IsClosedUnderQuotients`.
-/

public section

open CategoryTheory

universe v u

namespace ModuleCat

/-- `R`-modules of cardinal rank at most `μ`, as a property of objects of `ModuleCat R`. -/
def rankLe (R : Type u) [Ring R] (μ : Cardinal.{v}) : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.rank R M ≤ μ

@[simp, grind =]
theorem rankLe_iff {R : Type u} [Ring R] {μ : Cardinal.{v}} (M : ModuleCat.{v} R) :
    rankLe R μ M ↔ Module.rank R M ≤ μ :=
  Iff.rfl

/-- Submodules of a module of cardinal rank at most `μ` have cardinal rank at most `μ`. -/
instance (R : Type u) [Ring R] (μ : Cardinal.{v}) :
    (rankLe.{v, u} R μ).IsClosedUnderSubobjects where
  prop_of_mono f _ hN := by
    rw [rankLe_iff] at hN ⊢
    exact (LinearMap.rank_le_of_injective f.hom
      ((ModuleCat.mono_iff_injective f).mp inferInstance)).trans hN

/-- Quotients of a module of cardinal rank at most `μ` have cardinal rank at most `μ`. -/
instance (R : Type u) [Ring R] (μ : Cardinal.{v}) :
    (rankLe.{v, u} R μ).IsClosedUnderQuotients where
  prop_of_epi f _ hM := by
    rw [rankLe_iff] at hM ⊢
    exact (LinearMap.rank_le_of_surjective f.hom
      ((ModuleCat.epi_iff_surjective f).mp inferInstance)).trans hM

end ModuleCat
