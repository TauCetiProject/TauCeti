/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.Algebra.Homology.TotalComplex.Homotopy
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Total Čech complexes and refinement homotopies

For a presheaf of integer-graded cochain complexes, take its native tuple Čech complex,
extend its nonnegative Čech grading by zero to the integers, and form the native direct-sum
total complex. The total differential is `δ + (-1)^p d` on Čech degree `p`. No covering
condition or topological hypothesis is needed.

Actual morphisms of indexed families induce contravariant maps of totals. Two such morphisms
induce homotopic maps, by extending and totalizing the Čech prism. Consequently their maps on
total cohomology agree. This is the refinement independence needed before taking a colimit of
fixed-cover hypercohomology groups. The construction allows unbounded coefficient complexes;
no convergence or derived comparison is asserted for them.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25, equation (20.25.0.2) and the computation
  following it: the refinement prism for complexes of presheaves.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex₂

universe w v u v' u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasZeroObject A]
  [HasProducts.{w} A] [HasCoproducts.{0} A]
  {ι κ : Type w} (U : ι → C) {V : κ → C}

/-- The direct-sum total Čech complex of a presheaf of cochain complexes, functorial in its
coefficients. The Čech grading is extended by zero from `ℕ` to `ℤ` before totalization.
The composite functor is exposed so native total inclusions and maps can elaborate with its
objects as their source and target. -/
@[expose, implicit_reducible]
def cechTotalComplexFunctor :
    (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ :=
  cechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor (CochainComplex A ℤ) ⋙
      totalFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The total Čech complex is the native total of the zero-extended tuple bicomplex. -/
@[simp]
lemma cechTotalComplexFunctor_obj (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexFunctor U).obj P =
      total (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat)
        (ComplexShape.up ℤ) :=
  (rfl)

/-- A coefficient morphism acts by extending and totalizing its native Čech map. -/
@[simp]
lemma cechTotalComplexFunctor_map {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechTotalComplexFunctor U).map α =
      total.map (HomologicalComplex.extendMap ((cechComplexFunctor U).map α)
        ComplexShape.embeddingUpNat) (ComplexShape.up ℤ) :=
  (rfl)

variable {U} (P : Cᵒᵖ ⥤ CochainComplex A ℤ)

/-- A morphism of indexed families induces a map in the reverse direction on total Čech
complexes, by the native refinement map, extension by zero, and totalization. -/
def cechTotalComplexMap (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechTotalComplexFunctor V).obj P ⟶ (cechTotalComplexFunctor U).obj P :=
  total.map (HomologicalComplex.extendMap (cechComplexMap P φ) ComplexShape.embeddingUpNat) _

/-- The refinement map is the native total map of the extended Čech refinement. -/
lemma cechTotalComplexMap_def (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexMap P φ =
      total.map (HomologicalComplex.extendMap (cechComplexMap P φ)
        ComplexShape.embeddingUpNat) (ComplexShape.up ℤ) :=
  (rfl)

/-- On each total summand, refinement is the corresponding component of the extended
Čech refinement map. -/
@[reassoc, simp]
lemma ι_cechTotalComplexMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (p q n : ℤ)
    (hpq : p + q = n) :
    ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫ (cechTotalComplexMap P φ).f n =
      ((HomologicalComplex.extendMap (cechComplexMap P φ)
        ComplexShape.embeddingUpNat).f p).f q ≫
          ιTotal _ (ComplexShape.up ℤ) p q n hpq := by
  exact ιTotal_map _ _ _ _ p q n hpq

/-- The identity refinement induces the identity of the total Čech complex. -/
@[simp]
lemma cechTotalComplexMap_id :
    cechTotalComplexMap P (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  rw [cechTotalComplexMap_def, cechComplexMap_id, HomologicalComplex.extendMap_id,
    total.map_id]
  -- The remaining object equation is `cechTotalComplexFunctor_obj`.
  rfl

/-- Refinement of total Čech complexes respects composition contravariantly. -/
@[simp]
lemma cechTotalComplexMap_comp {ν : Type w} {W : ν → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    cechTotalComplexMap P (φ ≫ ψ) = cechTotalComplexMap P ψ ≫ cechTotalComplexMap P φ := by
  simp only [cechTotalComplexMap_def, cechComplexMap_comp,
    HomologicalComplex.extendMap_comp, total.map_comp]
  -- The remaining object equations are instances of `cechTotalComplexFunctor_obj`.
  rfl

/-- The total refinement map is natural in the presheaf of coefficient complexes. -/
@[reassoc]
lemma cechTotalComplexMap_naturality {Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechTotalComplexFunctor V).map α ≫ cechTotalComplexMap Q φ =
      cechTotalComplexMap P φ ≫ (cechTotalComplexFunctor U).map α := by
  have h := congrArg
    (fun k ↦ total.map (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
      (ComplexShape.up ℤ)) (cechComplexMap_naturality P α φ)
  simp only [HomologicalComplex.extendMap_comp, total.map_comp] at h
  rw [cechTotalComplexFunctor_map, cechTotalComplexFunctor_map,
    cechTotalComplexMap_def, cechTotalComplexMap_def]
  exact h

/-- The totalized refinement prism. Its homotopy equation is `T_φ - T_ψ = DH + HD`,
as for the native Čech prism. Swapping `φ` and `ψ` gives the opposite difference. -/
def cechTotalComplexMapHomotopy
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy (cechTotalComplexMap P φ) (cechTotalComplexMap P ψ) :=
  ((cechComplexMapHomotopy P φ ψ).extend ComplexShape.embeddingUpNat).totalMap
    (ComplexShape.up ℤ)

/-- On each total summand the refinement prism is the extended Čech prism, with no extra
sign. The inclusion on the right has bidegree `(p - 1,q)`. -/
@[reassoc, simp]
lemma ι_cechTotalComplexMapHomotopy_hom
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (p q n : ℤ)
    (hpq : p + q = n) :
    ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫
        (cechTotalComplexMapHomotopy P φ ψ).hom n (n - 1) =
      (((cechComplexMapHomotopy P φ ψ).extend ComplexShape.embeddingUpNat).hom
        p (p - 1)).f q ≫
          ιTotal _ (ComplexShape.up ℤ) (p - 1) q (n - 1)
            (by omega : p - 1 + q = n - 1) := by
  unfold cechTotalComplexMapHomotopy
  exact Homotopy.ι_totalMap_hom_up_int _ p q n hpq

/-- Total Čech cohomology maps are independent of the chosen raw refinement function. -/
lemma homologyMap_cechTotalComplexMap_eq
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℤ)
    [((cechTotalComplexFunctor V).obj P).HasHomology n]
    [((cechTotalComplexFunctor U).obj P).HasHomology n] :
    HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n =
      HomologicalComplex.homologyMap (cechTotalComplexMap P ψ) n :=
  (cechTotalComplexMapHomotopy P φ ψ).homologyMap_eq n

end TauCeti.CategoryTheory
