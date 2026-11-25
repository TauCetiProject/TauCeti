/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology

/-!
# The cup product on Čech cohomology over a directed system of families

Let `C` be a category with finite products, `F` a presheaf of `R`-algebras on `C`, and
`E : J → FormalCoproduct C` a system of families indexed by a directed order `J`, such that `E j`
admits a morphism of families to `E i` whenever `i ≤ j`; for instance the point-neighborhood covers
of a topological space, through which `TauCeti.Topology.cechCohomology` is defined. The Čech
cohomology `Hⁿ(E, F)` of the underlying presheaf of modules for the system
(`TauCeti.CategoryTheory.cechCohomology`) is the colimit over `J` of the Čech cohomologies of the
families `E j`.

The cup products on the cohomologies of the families commute with the maps induced by morphisms of
families (`TauCeti.CategoryTheory.homologyMap_cechComplexMap_cechCupHomology`), so they pass to the
colimit over the directed order `J`. This file defines the resulting **cup product**
`Hᵖ(E, F) × H^q(E, F) → Hⁿ(E, F)`, for `p + q = n`
(`TauCeti.CategoryTheory.cechCohomologyCup`), and the **unit class** in `H⁰(E, F)`
(`TauCeti.CategoryTheory.cechCohomologyOne`), and proves that the product is associative and
unital and natural in the presheaf of algebras. So `⊕ₚ Hᵖ(E, F)` is an associative unital graded
`R`-algebra. When `F` satisfies the sheaf condition for every family of the system, the
identification of `H⁰(E, F)` with the sections of `F` over the terminal object
(`TauCeti.CategoryTheory.cechCohomologyZeroIso`) is multiplicative and unital, so in degree `0` the
cup product is the product of sections.

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyCup`: the cup product on Čech cohomology for the system.
* `TauCeti.CategoryTheory.cechCohomologyOne`: the unit class.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyCup_ι`: on the images of two classes of one family, the
  cup product is the image of their cup product; `TauCeti.CategoryTheory.cechCohomologyCup_ι_ι`
  computes it on classes of two families through any common refinement.
* `TauCeti.CategoryTheory.cechCohomologyι_app_cechOneHomology`: the unit class is the image of the
  unit class of every family.
* `TauCeti.CategoryTheory.cechCohomologyCup_assoc`,
  `TauCeti.CategoryTheory.cechCohomologyOne_cechCohomologyCup`,
  `TauCeti.CategoryTheory.cechCohomologyCup_cechCohomologyOne`: associativity and the unit laws.
* `TauCeti.CategoryTheory.cechCohomology_map_cechCohomologyCup`,
  `TauCeti.CategoryTheory.cechCohomology_map_cechCohomologyOne`: the maps induced by morphisms of
  presheaves of algebras preserve the cup product and the unit class.
* `TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_mul`,
  `TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_one`: in degree `0` the cup product and the
  unit class are the product of sections and the section `1`.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the cup product on
  Čech cohomology, and Section 20.15 (tag 09UY) for the colimit over refinements.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w t v u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {R : Type u'} [CommRing R]
  {J : Type t} [Preorder J] [IsDirectedOrder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) [HasColimitsOfShape J (ModuleCat.{w} R)]
  (F : Cᵒᵖ ⥤ AlgCat.{w} R)

/-- **The cup product on Čech cohomology** `Hᵖ(E, F) × H^q(E, F) → Hⁿ(E, F)`, for `p + q = n`,
of a presheaf of algebras `F` for a directed system of families `E`: the colimit of the cup
products on the Čech cohomologies of the families of the system. It is computed on the images of
classes of the families by `TauCeti.CategoryTheory.cechCohomologyCup_ι` and
`TauCeti.CategoryTheory.cechCohomologyCup_ι_ι`. -/
def cechCohomologyCup (p q n : ℕ) (h : p + q = n) :
    (cechCohomology (ModuleCat.{w} R) E hE p).obj
        (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj
          (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) →ₗ[R]
        (cechCohomology (ModuleCat.{w} R) E hE n).obj
          (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) :=
  TauCeti.ModuleCat.colimitMap₂
    (M := (cechCohomologyDiagram (ModuleCat.{w} R) E hE p).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (N := (cechCohomologyDiagram (ModuleCat.{w} R) E hE q).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (P := (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun j ↦ cechCupHomology (E j).obj F p q n h)
    fun _ _ f x y ↦ by
      simp only [cechCohomologyDiagram_flip_obj_map E hE _
        (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) f (hE (leOfHom f)).some]
      exact (homologyMap_cechComplexMap_cechCupHomology _ h x y).symm

/-- **The cup product on images of classes of one family.** The cup product of the images of two
classes of the family `E j` is the image of their cup product. -/
@[simp]
theorem cechCohomologyCup_ι {p q n : ℕ} (h : p + q = n) (j : J)
    (a : (cechAlgebraComplex (E j).obj F).homology p)
    (b : (cechAlgebraComplex (E j).obj F).homology q) :
    cechCohomologyCup E hE F p q n h
        (((cechCohomologyι E hE p j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom a)
        (((cechCohomologyι E hE q j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom b) =
      ((cechCohomologyι E hE n j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechCupHomology (E j).obj F p q n h a b) := by
  simp only [cechCohomologyCup, cechCohomologyι_app]
  -- the diagrams are only determined by the goal, so the universe levels are given explicitly
  exact TauCeti.ModuleCat.colimitMap₂_ι.{t, w} _ _ j _ _

/-- **The cup product on images of classes of two families.** The cup product of the images of a
class `a` of `E i` and a class `b` of `E j` is the image of the cup product of their restrictions
to any common refinement `E k`, along any morphisms of families `E k ⟶ E i` and `E k ⟶ E j`. -/
theorem cechCohomologyCup_ι_ι {p q n : ℕ} (h : p + q = n) {i j k : J} (hik : i ≤ k)
    (hjk : j ≤ k) (φ : E k ⟶ E i) (ψ : E k ⟶ E j)
    (a : (cechAlgebraComplex (E i).obj F).homology p)
    (b : (cechAlgebraComplex (E j).obj F).homology q) :
    cechCohomologyCup E hE F p q n h
        (((cechCohomologyι E hE p i).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom a)
        (((cechCohomologyι E hE q j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom b) =
      ((cechCohomologyι E hE n k).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechCupHomology (E k).obj F p q n h
          ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) p).hom
            a)
          ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) ψ) q).hom
            b)) := by
  rw [← cechCohomologyι_app_homologyMap E hE _ hik φ a,
    ← cechCohomologyι_app_homologyMap E hE _ hjk ψ b, cechCohomologyCup_ι]

section Nonempty

variable [Nonempty J]

/-- The **unit class** of Čech cohomology for the system: the image of the unit class of any
family of the system (`TauCeti.CategoryTheory.cechCohomologyι_app_cechOneHomology`). -/
def cechCohomologyOne :
    (cechCohomology (ModuleCat.{w} R) E hE 0).obj (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) :=
  ((cechCohomologyι E hE 0 (Classical.arbitrary J)).app
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom (cechOneHomology (E _).obj F)

/-- The unit class is the image of the unit class of every family of the system. -/
@[simp]
theorem cechCohomologyι_app_cechOneHomology (j : J) :
    ((cechCohomologyι E hE 0 j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechOneHomology (E j).obj F) =
      cechCohomologyOne E hE F := by
  obtain ⟨k, hjk, hk⟩ := exists_ge_ge j (Classical.arbitrary J)
  rw [cechCohomologyOne, ← cechCohomologyι_app_homologyMap E hE _ hjk (hE hjk).some,
    ← cechCohomologyι_app_homologyMap E hE _ hk (hE hk).some,
    homologyMap_cechComplexMap_cechOneHomology, homologyMap_cechComplexMap_cechOneHomology]

/-- The unit class is a left unit for the cup product on Čech cohomology for the system. -/
@[simp]
theorem cechCohomologyOne_cechCohomologyCup {q : ℕ}
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F 0 q q (zero_add q) (cechCohomologyOne E hE F) y = y := by
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  rw [← cechCohomologyι_app_cechOneHomology E hE F j, cechCohomologyCup_ι,
    cechOneHomology_cechCupHomology]

/-- The unit class is a right unit for the cup product on Čech cohomology for the system. -/
@[simp]
theorem cechCohomologyCup_cechCohomologyOne {p : ℕ}
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F p 0 p (add_zero p) x (cechCohomologyOne E hE F) = x := by
  obtain ⟨j, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  rw [← cechCohomologyι_app_cechOneHomology E hE F j, cechCohomologyCup_ι,
    cechCupHomology_cechOneHomology]

/-- **Associativity** of the cup product on Čech cohomology for the system. -/
theorem cechCohomologyCup_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (z : (cechCohomology (ModuleCat.{w} R) E hE r).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F m r n h₂ (cechCohomologyCup E hE F p q m h₁ x y) z =
      cechCohomologyCup E hE F p l n h₄ x (cechCohomologyCup E hE F q r l h₃ y z) := by
  obtain ⟨i, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  obtain ⟨k, c, rfl⟩ := exists_cechCohomologyι_app_eq E hE z
  -- move the three classes to a common refinement
  obtain ⟨s, his, hjs⟩ := exists_ge_ge i j
  obtain ⟨t, hst, hkt⟩ := exists_ge_ge s k
  rw [← cechCohomologyι_app_homologyMap E hE _ (his.trans hst) (hE (his.trans hst)).some a,
    ← cechCohomologyι_app_homologyMap E hE _ (hjs.trans hst) (hE (hjs.trans hst)).some b,
    ← cechCohomologyι_app_homologyMap E hE _ hkt (hE hkt).some c]
  simp only [cechCohomologyCup_ι, cechCupHomology_assoc h₁ h₂ h₃ h₄]

section Naturality

variable {F} {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)

/-- **Naturality in the coefficients.** The map on Čech cohomology for the system induced by a
morphism of presheaves of algebras `α : F ⟶ G` preserves cup products. -/
@[simp]
theorem cechCohomology_map_cechCohomologyCup {p q n : ℕ} (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    ((cechCohomology (ModuleCat.{w} R) E hE n).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom
        (cechCohomologyCup E hE F p q n h x y) =
      cechCohomologyCup E hE G p q n h
        (((cechCohomology (ModuleCat.{w} R) E hE p).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom x)
        (((cechCohomology (ModuleCat.{w} R) E hE q).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom y) := by
  obtain ⟨i, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  -- move the two classes to a common refinement
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [← cechCohomologyι_app_homologyMap E hE _ hik (hE hik).some a,
    ← cechCohomologyι_app_homologyMap E hE _ hjk (hE hjk).some b]
  simp only [cechCohomologyCup_ι, cechCohomology_map_cechCohomologyι_app,
    homologyMap_cechComplexFunctor_map_cechCupHomology]

/-- The map on Čech cohomology for the system induced by a morphism of presheaves of algebras
preserves the unit class. -/
@[simp]
theorem cechCohomology_map_cechCohomologyOne :
    ((cechCohomology (ModuleCat.{w} R) E hE 0).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom
        (cechCohomologyOne E hE F) =
      cechCohomologyOne E hE G := by
  rw [cechCohomologyOne, cechCohomology_map_cechCohomologyι_app,
    homologyMap_cechComplexFunctor_map_cechOneHomology, cechCohomologyι_app_cechOneHomology]

end Naturality

section Zero

attribute [local instance] _root_.CategoryTheory.IsFiltered.isConnected

variable {T : C} (hT : IsTerminal T)
  (h : ∀ j, QuasiIsoAt
    (cechAugmentation (E j).obj hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0)

/-- **In degree zero the cup product is the product of sections.** If `F` satisfies the sheaf
condition for every family of the system, the identification of the degree `0` Čech cohomology
with the sections of `F` over the terminal object `T` (`cechCohomologyZeroIso`) carries the product
of sections to the cup product. -/
theorem cechCohomologyZeroIso_hom_mul (s t : F.obj (op T)) :
    (cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
        (s * t) =
      cechCohomologyCup E hE F 0 0 0 rfl
        ((cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom s)
        ((cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
          t) := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    homologyMap_cechAugmentation_mul, cechCohomologyCup_ι]

/-- **In degree zero the unit class is the unit section.** If `F` satisfies the sheaf condition for
every family of the system, the identification of the degree `0` Čech cohomology with the sections
of `F` over the terminal object `T` (`cechCohomologyZeroIso`) carries the section `1` to the unit
class. -/
theorem cechCohomologyZeroIso_hom_one :
    (cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
        (1 : F.obj (op T)) =
      cechCohomologyOne E hE F := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    homologyMap_cechAugmentation_one, cechCohomologyι_app_cechOneHomology]

end Zero

end Nonempty

end TauCeti.CategoryTheory
