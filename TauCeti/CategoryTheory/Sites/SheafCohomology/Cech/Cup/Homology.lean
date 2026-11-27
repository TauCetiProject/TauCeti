/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Bilinear
public import TauCeti.Algebra.Homology.ModuleCat.Single
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic

/-!
# The cup product on the Čech cohomology of a family

Let `C` be a category with finite products, `U : ι → C` a family of objects, for instance an open
cover of a topological space, and `F` a presheaf of `R`-algebras on `C`, for instance the sheaf of
locally constant functions with values in a commutative ring `R`. The cup product of Čech cochains
(`TauCeti.CategoryTheory.cechCup`) obeys the Leibniz rule, so it descends to the Čech cohomology
`Hᵖ(U, F)` of the family (`TauCeti.CategoryTheory.cechCupHomology`): the cup product of the classes
of two cocycles is the class of their cup product
(`TauCeti.CategoryTheory.cechCupHomology_homologyπ`). On cohomology:

* the cup product is **associative** (`TauCeti.CategoryTheory.cechCupHomology_assoc`);
* the class of the unit cochain `1` (`TauCeti.CategoryTheory.cechOneHomology`) is a two-sided
  **unit** (`TauCeti.CategoryTheory.cechCupHomology_cechOneHomology`,
  `TauCeti.CategoryTheory.cechOneHomology_cechCupHomology`);
* the maps on cohomology induced by morphisms of families, such as refinements of open covers,
  and by morphisms of presheaves of algebras preserve the cup product and the unit
  (`TauCeti.CategoryTheory.homologyMap_cechComplexMap_cechCupHomology`,
  `TauCeti.CategoryTheory.homologyMap_cechComplexFunctor_map_cechCupHomology` and the
  corresponding statements for `cechOneHomology`);
* in degree `0`, for a terminal object `T`, the classes of the augmentations of sections over `T`
  multiply as the sections do, and the section `1` gives the unit class
  (`TauCeti.CategoryTheory.homologyMap_cechAugmentation_mul`,
  `TauCeti.CategoryTheory.homologyMap_cechAugmentation_one`).

So `⊕ₚ Hᵖ(U, F)` is an associative unital graded `R`-algebra, functorial in the family and in the
presheaf. Since any two morphisms between two families induce the same map on cohomology, these
are the compatibilities through which the product passes to Čech cohomology defined as a colimit
over a directed system of covers (`TauCeti.CategoryTheory.cechCohomologyCup`).

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the cup product on
  Čech cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} {U : ι → C}
  {R : Type u'} [CommRing R] {F : Cᵒᵖ ⥤ AlgCat.{w} R}

variable (U F) in
/-- **The cup product on Čech cohomology** `Hᵖ(U, F) × H^q(U, F) → Hⁿ(U, F)`, for `p + q = n`, of
a family `U` and a presheaf of algebras `F`: the class of the cup product of representing
cocycles (`TauCeti.CategoryTheory.cechCupHomology_homologyπ`). -/
def cechCupHomology (p q n : ℕ) (h : p + q = n) :
    (cechAlgebraComplex U F).homology p →ₗ[R] (cechAlgebraComplex U F).homology q →ₗ[R]
      (cechAlgebraComplex U F).homology n :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂ (fun p q n h ↦ cechCup p q n h)
    (fun _ _ _ h a b ↦ d_cechCup h a b) p q n h

/-- **The cup product on classes**: the cup product of the classes of two cocycles is the class of
the cup product of the cocycles. -/
@[simp]
theorem cechCupHomology_homologyπ {p q n : ℕ} (h : p + q = n)
    (a : (cechAlgebraComplex U F).cycles p) (b : (cechAlgebraComplex U F).cycles q) :
    cechCupHomology U F p q n h (((cechAlgebraComplex U F).homologyπ p).hom a)
        (((cechAlgebraComplex U F).homologyπ q).hom b) =
      ((cechAlgebraComplex U F).homologyπ n).hom ((cechAlgebraComplex U F).moduleCatCyclesMk
        (cechCup p q n h (((cechAlgebraComplex U F).iCycles p).hom a)
          (((cechAlgebraComplex U F).iCycles q).hom b)) (n + 1) (by simp)
        (d_cechCup_eq_zero h (moduleCat_d_iCycles_apply _ _ _ a)
          (moduleCat_d_iCycles_apply _ _ _ b))) := by
  rw [cechCupHomology, TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ]
  congr 1
  apply moduleCat_iCycles_injective
  simp

/-- **The cup product on classes of cochains**: the cup product of the classes of two cocycles
given as cochains is the class of their cup product. -/
theorem cechCupHomology_homologyπ_moduleCatCyclesMk {p q n : ℕ} (h : p + q = n)
    (x : (cechAlgebraComplex U F).X p) (m₁ : ℕ) (hm₁ : (ComplexShape.up ℕ).next p = m₁)
    (hx : ((cechAlgebraComplex U F).d p m₁).hom x = 0) (y : (cechAlgebraComplex U F).X q)
    (m₂ : ℕ) (hm₂ : (ComplexShape.up ℕ).next q = m₂)
    (hy : ((cechAlgebraComplex U F).d q m₂).hom y = 0) :
    cechCupHomology U F p q n h
        (((cechAlgebraComplex U F).homologyπ p).hom
          ((cechAlgebraComplex U F).moduleCatCyclesMk x m₁ hm₁ hx))
        (((cechAlgebraComplex U F).homologyπ q).hom
          ((cechAlgebraComplex U F).moduleCatCyclesMk y m₂ hm₂ hy)) =
      ((cechAlgebraComplex U F).homologyπ n).hom ((cechAlgebraComplex U F).moduleCatCyclesMk
        (cechCup p q n h x y) (n + 1) (by simp)
        (d_cechCup_eq_zero h (by subst hm₁; rwa [CochainComplex.next] at hx)
          (by subst hm₂; rwa [CochainComplex.next] at hy))) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ_moduleCatCyclesMk _ _ h x m₁ hm₁ hx y m₂
    hm₂ hy

/-- **Associativity** of the cup product on Čech cohomology. -/
theorem cechCupHomology_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (α : (cechAlgebraComplex U F).homology p)
    (β : (cechAlgebraComplex U F).homology q) (γ : (cechAlgebraComplex U F).homology r) :
    cechCupHomology U F m r n h₂ (cechCupHomology U F p q m h₁ α β) γ =
      cechCupHomology U F p l n h₄ α (cechCupHomology U F q r l h₃ β γ) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_assoc _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
    (cechCup_assoc h₁ h₂ h₃ h₄) α β γ

variable (U F) in
/-- The **unit class** of Čech cohomology: the class in `H⁰(U, F)` of the unit cocycle, all of
whose factors are `1`. -/
def cechOneHomology : (cechAlgebraComplex U F).homology 0 :=
  ((cechAlgebraComplex U F).homologyπ 0).hom
    ((cechAlgebraComplex U F).moduleCatCyclesMk (cechOne U F) 1 (by simp) d_cechOne)

variable (U F) in
/-- The unit class is the class of the unit cocycle. -/
theorem cechOneHomology_def :
    cechOneHomology U F = ((cechAlgebraComplex U F).homologyπ 0).hom
      ((cechAlgebraComplex U F).moduleCatCyclesMk (cechOne U F) 1 (by simp) d_cechOne) :=
  (rfl)

/-- The unit class is a left unit for the cup product on Čech cohomology. -/
@[simp]
theorem cechOneHomology_cechCupHomology {q : ℕ} (β : (cechAlgebraComplex U F).homology q) :
    cechCupHomology U F 0 q q (zero_add q) (cechOneHomology U F) β = β :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_left _ _ _ d_cechOne cechOne_cechCup β

/-- The unit class is a right unit for the cup product on Čech cohomology. -/
@[simp]
theorem cechCupHomology_cechOneHomology {p : ℕ} (α : (cechAlgebraComplex U F).homology p) :
    cechCupHomology U F p 0 p (add_zero p) α (cechOneHomology U F) = α :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_unit_right _ _ _ d_cechOne cechCup_cechOne α

section Naturality

/-- **Naturality under refinement.** The map on Čech cohomology `Hⁿ(V, F) ⟶ Hⁿ(U, F)` induced by a
morphism of families `φ : U ⟶ V`, such as a refinement of open covers, preserves cup products. -/
@[simp]
theorem homologyMap_cechComplexMap_cechCupHomology {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {p q n : ℕ} (h : p + q = n)
    (α : (cechAlgebraComplex V F).homology p) (β : (cechAlgebraComplex V F).homology q) :
    (homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) n).hom
        (cechCupHomology V F p q n h α β) =
      cechCupHomology U F p q n h
        ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) p).hom α)
        ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) q).hom
          β) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _ _ _ _ _ _ _
    (fun _ _ _ h a b ↦ cechComplexMap_cechCup h φ a b) p q n h α β

/-- The map on Čech cohomology induced by a morphism of families, such as a refinement of open
covers, preserves the unit class. -/
@[simp]
theorem homologyMap_cechComplexMap_cechOneHomology {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) 0).hom
        (cechOneHomology V F) =
      cechOneHomology U F := by
  rw [cechOneHomology_def, cechOneHomology_def, homologyMap_homologyπ_moduleCatCyclesMk]
  congr 2
  exact cechComplexMap_cechOne φ

/-- **Naturality in the coefficients.** The map on Čech cohomology induced by a morphism of
presheaves of algebras `α : F ⟶ G` preserves cup products. -/
@[simp]
theorem homologyMap_cechComplexFunctor_map_cechCupHomology {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)
    {p q n : ℕ} (h : p + q = n) (x : (cechAlgebraComplex U F).homology p)
    (y : (cechAlgebraComplex U F).homology q) :
    (homologyMap ((cechComplexFunctor U).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) n).hom
        (cechCupHomology U F p q n h x y) =
      cechCupHomology U G p q n h
        ((homologyMap ((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) p).hom x)
        ((homologyMap ((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) q).hom y) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂ _ _ _ _ _ _ _
    (fun _ _ _ h a b ↦ cechComplexFunctor_map_cechCup h α a b) p q n h x y

/-- The map on Čech cohomology induced by a morphism of presheaves of algebras preserves the unit
class. -/
@[simp]
theorem homologyMap_cechComplexFunctor_map_cechOneHomology {G : Cᵒᵖ ⥤ AlgCat.{w} R}
    (α : F ⟶ G) :
    (homologyMap ((cechComplexFunctor U).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) 0).hom
        (cechOneHomology U F) =
      cechOneHomology U G := by
  rw [cechOneHomology_def, cechOneHomology_def, homologyMap_homologyπ_moduleCatCyclesMk]
  congr 2
  exact cechComplexFunctor_map_cechOne α

end Naturality

section Augmentation

variable {T : C} (hT : IsTerminal T)

/-- The class in `H⁰(U, F)` of the augmentation of a section over the terminal object is the class
of the cycle that the augmentation maps it to. -/
private lemma homologyMap_cechAugmentation_apply (s : F.obj (op T)) :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s) =
      ((cechAlgebraComplex U F).homologyπ 0).hom
        (cyclesMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0
          ((singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s)) := by
  rw [← singleObjCyclesSelfIso_inv_homologyπ, ModuleCat.comp_apply,
    moduleCat_homologyMap_homologyπ]

/-- **The cup product in degree zero is the product of sections.** For a terminal object `T`, the
class in `H⁰(U, F)` of the augmentation of a product `s * t` of sections of `F` over `T` is the cup
product of the classes of the augmentations of `s` and `t`. -/
theorem homologyMap_cechAugmentation_mul (s t : F.obj (op T)) :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom (s * t)) =
      cechCupHomology U F 0 0 0 rfl
        ((homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s))
        ((homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom t)) := by
  simp only [homologyMap_cechAugmentation_apply, cechCupHomology_homologyπ]
  congr 1
  apply moduleCat_iCycles_injective
  refine cechCochain_ext fun a ↦ ?_
  simp only [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk, cechComponent_cechCup,
    CochainComplex.iCycles_singleObjCyclesSelfIso_inv, cechFace_cechAugmentation_f_zero,
    cechComponent_cechAugmentation_f_zero, map_mul]

/-- **The unit class in degree zero is the class of the unit section.** For a terminal object `T`,
the class in `H⁰(U, F)` of the augmentation of the section `1` of `F` over `T` is the unit class. -/
theorem homologyMap_cechAugmentation_one :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom
          (1 : F.obj (op T))) =
      cechOneHomology U F := by
  rw [homologyMap_cechAugmentation_apply, cechOneHomology_def]
  congr 1
  apply moduleCat_iCycles_injective
  refine cechCochain_ext fun a ↦ ?_
  simp only [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk,
    CochainComplex.iCycles_singleObjCyclesSelfIso_inv, cechComponent_cechAugmentation_f_zero,
    map_one, cechComponent_cechOne]

end Augmentation

end TauCeti.CategoryTheory
