/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology

/-!
# Graded commutativity of the cup product on Čech cohomology

Let `C` be a thin category with finite products, for instance the opens of a topological space,
`U : ι → C` a family of objects and `F` a presheaf of commutative `R`-algebras on `C`, for
instance the sheaf of locally constant functions with values in a commutative ring `R`. The cup
product on Čech cohomology (`TauCeti.CategoryTheory.cechCupHomology`) is **graded commutative**:

`β ⌣ α = (-1) ^ (p q) α ⌣ β`

for classes `α` of degree `p` and `β` of degree `q`
(`TauCeti.CategoryTheory.cechCupHomology_comm`). Together with associativity and the unit of
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology`, this makes
`⊕ₚ Hᵖ(U, F)` a graded-commutative graded `R`-algebra. In particular a class of odd degree
anticommutes with itself, so its square vanishes when `2` is invertible in `R`
(`TauCeti.CategoryTheory.cechCupHomology_self_eq_zero_of_odd`), for instance over `ℚ`.

This specializes the general graded-commutativity theorem
`TauCeti.CategoryTheory.cechComplexCup_comm` to multiplication in a presheaf of commutative
`R`-algebras (proved in `TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology` via the
order-reversing operator `TauCeti.CategoryTheory.cechReverse`).

## Main results

* `TauCeti.CategoryTheory.cechCupHomology_comm`: graded commutativity of the cup product on Čech
  cohomology.
* `TauCeti.CategoryTheory.cechCupHomology_self_eq_zero_of_odd`: when `2` is invertible, the cup
  square of a class of odd degree vanishes.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the graded
  commutativity of the cup product on Čech cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [Quiver.IsThin C] {ι : Type w}
  {U : ι → C} {R : Type u'} [CommRing R] {F : Cᵒᵖ ⥤ AlgCat.{w} R}

/-- **Graded commutativity** of the cup product on Čech cohomology: for a presheaf of commutative
algebras on a thin category, `β ⌣ α = (-1) ^ (p q) α ⌣ β` for classes `α` of degree `p` and `β`
of degree `q`. -/
theorem cechCupHomology_comm (hF : ∀ X (x y : F.obj X), x * y = y * x) {p q n : ℕ}
    (h : p + q = n) (h' : q + p = n) (α : (cechAlgebraComplex U F).homology p)
    (β : (cechAlgebraComplex U F).homology q) :
    cechCupHomology U F q p n h' β α = (-1 : ℤ) ^ (p * q) • cechCupHomology U F p q n h α β := by
  simp only [cechCupHomology_eq_cechComplexCup]
  exact cechComplexCup_comm U
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ LinearMap.mul R (F.obj X))
    (cechAlgebraMul_naturality F) (cechAlgebraMul_naturality F)
    (fun X (x y : F.obj X) ↦ hF X y x) p q n h α β

/-- **Odd classes square to zero** when `2` is invertible: for a presheaf of commutative algebras
on a thin category, graded commutativity makes a class `α` of odd degree anticommute with itself,
`α ⌣ α = -(α ⌣ α)`, so `α ⌣ α = 0`. -/
theorem cechCupHomology_self_eq_zero_of_odd (hF : ∀ X (x y : F.obj X), x * y = y * x)
    (h2 : IsUnit (2 : R)) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (α : (cechAlgebraComplex U F).homology p) : cechCupHomology U F p p n h α α = 0 := by
  have hα := cechCupHomology_comm hF h h α α
  rw [(hp.mul hp).neg_one_pow, neg_one_zsmul, eq_neg_iff_add_eq_zero, ← two_smul R] at hα
  exact (h2.smul_left_cancel (y := (0 : (cechAlgebraComplex U F).homology n))).1
    (by rwa [smul_zero])

end TauCeti.CategoryTheory
