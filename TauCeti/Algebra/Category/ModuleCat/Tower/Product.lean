/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact

/-!
# The product functor on towers of modules

The product `∏ₙ Aₙ` of the terms of a tower `A` of `R`-modules is functorial in `A`. This file
packages it as an additive functor `ModuleTower R ⥤ ModuleCat R`, shows that it is exact (products
of modules are exact), hence preserves homology, and records the shift maps
`δ(x)ₙ = xₙ - φₙ(xₙ₊₁)` and the projections `∏ₖ Aₖ → Aₙ` as natural transformations.

## Main declarations

* `TauCeti.ModuleTower.productFunctor`: the product functor `A ↦ ∏ₙ Aₙ` on towers, which is exact
  (`TauCeti.ModuleTower.exact_map_productFunctor`) and preserves homology.
* `TauCeti.ModuleTower.shiftNatTrans`: the shift maps `δ`, as a natural endomorphism of the
  product functor.
* `TauCeti.ModuleTower.productπ`: the projections `∏ₖ Aₖ → Aₙ`, related to the shift by
  `TauCeti.ModuleTower.shiftNatTrans_comp_productπ`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Opposite

universe v u

namespace ModuleTower

variable (R : Type u) [Ring R]

/-- The product functor `A ↦ ∏ₙ Aₙ` on towers of `R`-modules. -/
@[expose, simps]
def productFunctor : ModuleTower.{v} R ⥤ ModuleCat.{v} R where
  obj F := ModuleCat.of R F.Product
  map f := ModuleCat.ofHom (productMap f)
  map_id F := by
    ext1
    exact productMap_id
  map_comp f g := by
    ext1
    exact productMap_comp f g

instance : (productFunctor.{v} R).Additive where
  map_add {_ _ f g} := by
    ext1
    exact productMap_add f g

variable {R} in
/-- The product functor is exact: it sends exact short complexes of towers to exact short
complexes of modules. -/
theorem exact_map_productFunctor {S : ShortComplex (ModuleTower.{v} R)} (hS : S.Exact) :
    (S.map (productFunctor R)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_productMap fun n ↦
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)))

instance : (productFunctor.{v} R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun _ hS ↦ exact_map_productFunctor hS

/-- The shift maps `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`, as a natural endomorphism of the product functor. -/
@[expose, simps]
def shiftNatTrans : productFunctor.{v} R ⟶ productFunctor.{v} R where
  app F := ModuleCat.ofHom F.shift
  naturality _ _ f := by
    ext1
    exact shift_natural f

/-- The projection `∏ₖ Aₖ → Aₙ`, as a natural transformation from the product functor to the
evaluation at `n`. -/
@[expose, simps]
def productπ (n : ℕ) :
    productFunctor.{v} R ⟶ (evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n) where
  app F := ModuleCat.ofHom (LinearMap.proj n)
  naturality _ _ f := by
    ext x : 2
    exact productMap_apply f x n

/-- The shift followed by the projection onto `Aₙ` is the projection onto `Aₙ` minus the
projection onto `Aₙ₊₁` followed by the transition `Aₙ₊₁ → Aₙ`. -/
theorem shiftNatTrans_comp_productπ (n : ℕ) :
    shiftNatTrans.{v} R ≫ productπ R n =
      productπ R n - productπ R (n + 1) ≫
        (evaluation ℕᵒᵖ (ModuleCat.{v} R)).map (homOfLE (Nat.le_succ n)).op := by
  ext F : 2
  ext x
  -- Both sides are `xₙ - φₙ(xₙ₊₁)`, by `shift_apply` and `transition_def`.
  exact (F.shift_apply x n).trans (by rw [transition_def]; rfl)

end ModuleTower

end TauCeti
