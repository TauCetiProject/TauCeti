/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.Algebra.Homology.TotalComplex.Additive
public import TauCeti.Algebra.Homology.TotalComplex.Homotopy
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

import TauCeti.Algebra.Homology.Embedding.MapExtend

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
  [HasProducts.{w} A]
  {ι κ : Type w} (U : ι → C) {V : κ → C}

/-- Cochain complexes in a category with products have products, computed degreewise. -/
instance hasProducts_cochainComplex : HasProducts.{w} (CochainComplex A ℤ) where

variable (P : Cᵒᵖ ⥤ CochainComplex A ℤ)

/-- Evaluation in internal degree `q` identifies a row of the zero-extended Čech bicomplex
with the zero extension of the Čech complex of the evaluated coefficients. -/
def extendedCechRowIso (q : ℤ) :
    (HomologicalComplex₂.flip
      (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat)).X q ≅
      ((cechComplexFunctor U).obj
        (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).extend
          ComplexShape.embeddingUpNat :=
  HomologicalComplex.mapExtendIso (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    ((cechComplexFunctor U).obj P) ComplexShape.embeddingUpNat ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor A).mapIso
        ((cechComplexFunctorMapIso U (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).app P)

/-- In each nonnegative Čech degree, the row comparison is the coefficient evaluation
comparison, transported through the canonical extension isomorphisms. -/
lemma extendedCechRowIso_hom_f (q : ℤ) (p : ℕ) :
    (extendedCechRowIso U P q).hom.f (p : ℤ) =
      (HomologicalComplex.eval A (ComplexShape.up ℤ) q).map
          ((((cechComplexFunctor U).obj P).extendXIso ComplexShape.embeddingUpNat
            (i := p) rfl).hom) ≫
        ((cechComplexFunctorMapIso U
          (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).hom.app P).f p ≫
          (((cechComplexFunctor U).obj
            (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).extendXIso
              ComplexShape.embeddingUpNat (i := p) rfl).inv := by
  simp only [extendedCechRowIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom]
  dsimp only [ComplexShape.Embedding.extendFunctor]
  rw [HomologicalComplex.mapExtendIso_hom_f _ _ _ (j := p) (j' := (p : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := (p : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The row comparison commutes with the maps induced by raw refinements of families. -/
@[reassoc]
lemma extendedCechRowIso_hom_comp_cechComplexMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (q : ℤ) :
    ((flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (cechComplexMap P φ)
        ComplexShape.embeddingUpNat)).f q ≫ (extendedCechRowIso U P q).hom =
      (extendedCechRowIso V P q).hom ≫ HomologicalComplex.extendMap
        (cechComplexMap (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q) φ)
          ComplexShape.embeddingUpNat := by
  ext p : 1
  simp only [HomologicalComplex.comp_f, flipFunctor_map_f_f]
  by_cases hp : ∃ n : ℕ, (n : ℤ) = p
  · obtain ⟨n, rfl⟩ := hp
    rw [extendedCechRowIso_hom_f, extendedCechRowIso_hom_f,
      HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl,
      HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl]
    simp only [HomologicalComplex.comp_f, HomologicalComplex.eval_map, Category.assoc]
    simp only [← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id,
      HomologicalComplex.id_f, Category.id_comp, Iso.inv_hom_id_assoc]
    have h := congrArg (fun f ↦ f.f n)
      (cechComplexFunctorMapIso_hom_app_comp_cechComplexMap U
        (HomologicalComplex.eval A (ComplexShape.up ℤ) q) P φ)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.eval_map] at h
    simp only [HomologicalComplex.comp_f, Category.assoc]
    simpa only [Category.assoc] using congrArg (fun f ↦
      ((((cechComplexFunctor V).obj P).extendXIso ComplexShape.embeddingUpNat
        (i := n) rfl).hom.f q) ≫ f ≫
      (((cechComplexFunctor U).obj
        (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).inv) h
  · apply IsZero.eq_of_src
    apply (HomologicalComplex.eval A (ComplexShape.up ℤ) q).map_isZero
    exact ((cechComplexFunctor V).obj P).isZero_extend_X ComplexShape.embeddingUpNat p
      fun n hn ↦ hp ⟨n, hn⟩

variable [HasCoproducts.{0} A]

/-- The direct-sum total Čech complex of a presheaf of cochain complexes, functorial in its
coefficients. The Čech grading is extended by zero from `ℕ` to `ℤ` before totalization.
The composite functor is exposed with its object field given by the native total, so native
total inclusions and maps also match simplification lemmas at implicit transparency. -/
@[expose, implicit_reducible]
def cechTotalComplexFunctor :
    (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ :=
  { cechComplexFunctor U ⋙
      ComplexShape.embeddingUpNat.extendFunctor (CochainComplex A ℤ) ⋙
        totalFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) with
    obj P := total (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat)
      (ComplexShape.up ℤ) }

instance : (cechTotalComplexFunctor U :
    (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ).Additive where
  map_add := Functor.map_add (cechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor (CochainComplex A ℤ) ⋙
      totalFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

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
@[reassoc]
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
@[reassoc]
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

variable (U) in
/-- An empty family has zero total Čech complex, without requiring any value of the
coefficient presheaf to vanish. -/
lemma isZero_cechTotalComplexFunctor_obj [IsEmpty ι] :
    IsZero ((cechTotalComplexFunctor U).obj P) :=
  (totalFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map_isZero
    ((ComplexShape.embeddingUpNat.extendFunctor (CochainComplex A ℤ)).map_isZero
      (isZero_cechComplexFunctor_obj U P))

section Homology

variable (A) [CategoryWithHomology A] (n : ℤ)

/-- Refinement on total Čech cohomology, natural in the presheaf of complexes. -/
def cechTotalComplexHomologyMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexFunctor V ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechTotalComplexFunctor U ⋙ HomologicalComplex.homologyFunctor A _ n where
  app P := (HomologicalComplex.homologyFunctor A _ n).map (cechTotalComplexMap P φ)
  naturality P _ α := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
      cechTotalComplexMap_naturality]

@[simp]
lemma cechTotalComplexHomologyMap_app
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexHomologyMap A n φ).app P =
      HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n :=
  (rfl)

/-- The total cohomology transformation does not depend on the raw refinement. -/
lemma cechTotalComplexHomologyMap_eq
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexHomologyMap A n φ = cechTotalComplexHomologyMap A n ψ := by
  ext P
  exact homologyMap_cechTotalComplexMap_eq P φ ψ n

@[simp]
lemma cechTotalComplexHomologyMap_id :
    cechTotalComplexHomologyMap A n (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  ext P
  rw [cechTotalComplexHomologyMap_app, cechTotalComplexMap_id]
  exact HomologicalComplex.homologyMap_id _ n

@[simp]
lemma cechTotalComplexHomologyMap_comp {ν : Type w} {W : ν → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    cechTotalComplexHomologyMap A n (φ ≫ ψ) =
      cechTotalComplexHomologyMap A n ψ ≫ cechTotalComplexHomologyMap A n φ := by
  ext P
  rw [cechTotalComplexHomologyMap_app, cechTotalComplexMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ n

/-- Refinements in both directions identify total Čech cohomology. Their composites
induce identity maps by independence of the raw refinement functions. -/
lemma isIso_cechTotalComplexHomologyMap_of_reverse
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    IsIso (cechTotalComplexHomologyMap A n φ) := by
  refine ⟨⟨cechTotalComplexHomologyMap A n ψ, ?_, ?_⟩⟩
  · rw [← cechTotalComplexHomologyMap_comp,
      cechTotalComplexHomologyMap_eq A n (ψ ≫ φ) (𝟙 _), cechTotalComplexHomologyMap_id]
  · rw [← cechTotalComplexHomologyMap_comp,
      cechTotalComplexHomologyMap_eq A n (φ ≫ ψ) (𝟙 _), cechTotalComplexHomologyMap_id]

end Homology

end TauCeti.CategoryTheory
