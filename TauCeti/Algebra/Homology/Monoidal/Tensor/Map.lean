/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Basic
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.Additive

/-!
# Additive monoidal functors and tensor products of cochain complexes

An additive strong monoidal functor that preserves the coproducts indexed by the
antidiagonals of `ℤ × ℤ` commutes with tensor products of unbounded cochain complexes.
The comparison uses the functor's tensor comparison on each homogeneous summand.
It preserves the Koszul signs in Mathlib's tensor differential.

The construction uses `Functor.Monoidal.μIso`, the coproduct comparison
`Limits.PreservesCoproduct.iso`, and the summand differential formula
`HomologicalComplex.ιTensorObj_tensor_d`.
-/

public section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

noncomputable section

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasCountableCoproducts C] [HasCountableCoproducts D]
  [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete {pq : ℤ × ℤ // pq.1 + pq.2 = n}) F]

local instance : HasZeroObject C := Preadditive.hasZeroObject_of_hasCoproduct.{0} C

local instance : HasZeroObject D := Preadditive.hasZeroObject_of_hasCoproduct.{0} D

attribute [local instance] Functor.preservesInitialObject_of_preservesZeroMorphisms

/-- The degreewise tensor comparison for an additive monoidal functor, formed by applying
its tensor isomorphism to every summand of the tensor product. -/
def mapCochainTensorXIso (K L : CochainComplex C ℤ) (n : ℤ) :
    (((F.mapHomologicalComplex (.up ℤ)).obj K) ⊗
      ((F.mapHomologicalComplex (.up ℤ)).obj L)).X n ≅ F.obj ((K ⊗ L).X n) :=
  Sigma.mapIso (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
    Monoidal.μIso F (K.X pq.val.1) (L.X pq.val.2)) ≪≫
      (PreservesCoproduct.iso F
        (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦ K.X pq.val.1 ⊗ L.X pq.val.2)).symm

/-- On a homogeneous summand the forward comparison is the monoidal tensor comparison,
followed by the image of the inclusion. -/
@[reassoc (attr := simp)]
lemma ι_mapCochainTensorXIso_hom (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
        (F.mapCochainTensorXIso K L n).hom =
      (Monoidal.μIso F (K.X p) (L.X q)).hom ≫ F.map (ιTensorObj K L p q n h) := by
  exact (Sigma.ι_mapIso_hom_assoc
    (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
      Monoidal.μIso F (K.X pq.val.1) (L.X pq.val.2)) ⟨(p, q), h⟩ _).trans
    (congrArg ((Monoidal.μIso F (K.X p) (L.X q)).hom ≫ ·)
      (ι_comp_sigmaComparison F
        (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦ K.X pq.val.1 ⊗ L.X pq.val.2)
        ⟨(p, q), h⟩))

/-- On the image of a homogeneous summand the inverse comparison uses the inverse
monoidal tensor comparison. -/
@[reassoc (attr := simp)]
lemma map_ι_mapCochainTensorXIso_inv (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    F.map (ιTensorObj K L p q n h) ≫ (F.mapCochainTensorXIso K L n).inv =
      (Monoidal.μIso F (K.X p) (L.X q)).inv ≫
        ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) p q n h := by
  rw [Iso.comp_inv_eq, Category.assoc, ι_mapCochainTensorXIso_hom]
  simp

private lemma mapCochainTensorXIso_hom_comm (K L : CochainComplex C ℤ) (n : ℤ) :
    (F.mapCochainTensorXIso K L n).hom ≫ F.map ((K ⊗ L).d n (n + 1)) =
      (((F.mapHomologicalComplex (.up ℤ)).obj K) ⊗
        ((F.mapHomologicalComplex (.up ℤ)).obj L)).d n (n + 1) ≫
          (F.mapCochainTensorXIso K L (n + 1)).hom := by
  apply mapBifunctor.hom_ext
  intro p q h
  rw [ι_mapCochainTensorXIso_hom_assoc, ← F.map_comp,
    ιTensorObj_tensor_d, ιTensorObj_tensor_d_assoc]
  simp only [F.map_add, F.map_units_smul, F.map_comp,
    Preadditive.comp_add, Linear.comp_units_smul, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc, ι_mapCochainTensorXIso_hom,
    mapHomologicalComplex_obj_d, mapHomologicalComplex_obj_X, Monoidal.μIso_hom,
    LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc]

/-- An additive strong monoidal functor preserving the antidiagonal coproducts commutes
with the tensor product of arbitrary integer-indexed cochain complexes. -/
def mapCochainTensorIso (K L : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K) ⊗
        ((F.mapHomologicalComplex (.up ℤ)).obj L) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) :=
  Hom.isoOfComponents (F.mapCochainTensorXIso K L) (fun i j hij ↦ by
    obtain rfl : j = i + 1 := ((ComplexShape.up_Rel _ _ _).mp hij).symm
    exact F.mapCochainTensorXIso_hom_comm K L i)

/-- The component of the forward cochain comparison is the coproduct comparison. -/
@[simp]
lemma mapCochainTensorIso_hom_f (K L : CochainComplex C ℤ) (n : ℤ) :
    (F.mapCochainTensorIso K L).hom.f n = (F.mapCochainTensorXIso K L n).hom :=
  (rfl)

/-- The component of the inverse cochain comparison is the inverse coproduct comparison. -/
@[simp]
lemma mapCochainTensorIso_inv_f (K L : CochainComplex C ℤ) (n : ℤ) :
    (F.mapCochainTensorIso K L).inv.f n = (F.mapCochainTensorXIso K L n).inv :=
  (rfl)

/-- The cochain tensor comparison is natural in both complexes. -/
@[reassoc]
lemma mapCochainTensorIso_hom_naturality {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) :
    ((F.mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
        (F.mapHomologicalComplex (.up ℤ)).map g) ≫ (F.mapCochainTensorIso K₂ L₂).hom =
      (F.mapCochainTensorIso K₁ L₁).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).map (f ⊗ₘ g) := by
  ext n
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [comp_f, mapCochainTensorIso_hom_f, tensorHom_eq_mapBifunctorMap,
    mapHomologicalComplex_map_f, ι_mapBifunctorMap_assoc,
    ι_mapCochainTensorXIso_hom, ι_mapCochainTensorXIso_hom_assoc,
    ← F.map_comp, ι_mapBifunctorMap]
  simp [Monoidal.μIso_hom, LaxMonoidal.μ_natural_left_assoc,
    LaxMonoidal.μ_natural_right_assoc]

/-- The tensor comparison as a natural isomorphism of bifunctors on unbounded cochain
complexes. Uncurrying uses the existing bifunctor on complexes and requires no extra
hypotheses about tensor products of four graded objects. -/
def mapCochainTensorNatIso :
    (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        uncurry.obj (curriedTensor D).map₂CochainComplex ≅
      uncurry.obj (curriedTensor C).map₂CochainComplex ⋙ F.mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun KL ↦ F.mapCochainTensorIso KL.1 KL.2) (fun {KL MN} fg ↦ by
    dsimp only [comp_map, prod_map, uncurry_obj_map, map₂HomologicalComplex_map_app,
      map₂HomologicalComplex_obj_map]
    dsimp only [comp_obj, prod_obj, uncurry_obj_obj, map₂HomologicalComplex_obj_obj]
    simp only [← tensorHom_eq_mapBifunctorMap]
    have hf := F.mapCochainTensorIso_hom_naturality fg.1 (𝟙 KL.2)
    have hg := F.mapCochainTensorIso_hom_naturality (𝟙 MN.1) fg.2
    simp only [Functor.map_id] at hf hg
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, ← Functor.map_comp])

/-- The forward natural comparison evaluated at a pair of complexes. -/
@[simp]
lemma mapCochainTensorNatIso_hom_app (K L : CochainComplex C ℤ) :
    F.mapCochainTensorNatIso.hom.app (K, L) = (F.mapCochainTensorIso K L).hom :=
  (rfl)

/-- The inverse natural comparison evaluated at a pair of complexes. -/
@[simp]
lemma mapCochainTensorNatIso_inv_app (K L : CochainComplex C ℤ) :
    F.mapCochainTensorNatIso.inv.app (K, L) = (F.mapCochainTensorIso K L).inv :=
  (rfl)

end

end CategoryTheory.Functor
