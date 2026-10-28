/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors and signed cube totalization

Applying an additive functor to the signed totalization of a finite commutative cube agrees
with totalizing the image cube. This comparison is needed when evaluating a cube of formal
cobordisms in modules, or extending coefficients of a cube of modules. Additivity suffices:
the sums at each height are finite, and the edge signs are integer scalars.

`CategoryTheory.Functor.cubeComplexMapIso` constructs this cochain isomorphism using Mathlib's
`CategoryTheory.Functor.mapBiproduct` in every degree. Its characteristic equations retain
the vertex inclusions and projections. The comparison is natural in both the cube and the
additive functor, and respects identity and composition of additive functors.

The signed cube convention follows M. Khovanov, *A categorification of the Jones polynomial*,
Duke Math. J. 101 (2000), §3.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

-- Unlike `PreservesFiniteBiproducts`, finite-product preservation supports every index universe.
attribute [local instance] preservesBiproduct_of_preservesProduct

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [HasFiniteBiproducts E]
  {ι : Type w} [Fintype ι] [LinearOrder ι]

variable (F : Finset ι ⥤ C) (G : C ⥤ D) [G.Additive]

private def cubeComplexMapXIso (r : ℤ) : (F ⋙ G).cubeComplex.X r ≅ G.obj (F.cubeComplex.X r) :=
  (F ⋙ G).cubeComplexXIsoBiproduct r ≪≫
    (G.mapBiproduct (fun S : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj S.1)).symm ≪≫
    G.mapIso (F.cubeComplexXIsoBiproduct r).symm

@[reassoc]
private lemma ι_cubeComplexMapXIso_hom {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F ⋙ G).cubeComplexι S ≫ (F.cubeComplexMapXIso G r).hom =
      G.map (F.cubeComplexι S) := by
  simp only [cubeComplexMapXIso, Iso.trans_hom, Iso.symm_hom, mapIso_hom,
    ι_cubeComplexXIsoBiproduct_hom_assoc, mapBiproduct_inv, biproduct.ι_desc_assoc,
    ← G.map_comp, ι_cubeComplexXIsoBiproduct_inv]

/-- Totalizing the image of a cube under an additive functor agrees with applying the functor
degreewise to its totalization. On each vertex the forward map is the image of its inclusion. -/
def cubeComplexMapIso : (F ⋙ G).cubeComplex ≅
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F.cubeComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (F.cubeComplexMapXIso G) <| by
    rintro r _ rfl
    refine (F ⋙ G).cubeComplex_hom_ext fun S ↦ ?_
    simp only [ι_cubeComplexMapXIso_hom_assoc,
      ι_cubeComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
      Functor.comp_map, Category.assoc, ι_cubeComplexMapXIso_hom,
      mapHomologicalComplex_obj_d, ← G.map_comp]
    rw [ι_cubeComplex_d, G.map_sum]
    congr 1
    funext a
    simp [G.map_zsmul]

/-- The forward comparison sends each vertex inclusion to its image under the functor. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexMapIso_hom_f {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F ⋙ G).cubeComplexι S ≫ (F.cubeComplexMapIso G).hom.f r = G.map (F.cubeComplexι S) := by
  exact ι_cubeComplexMapXIso_hom F G S

/-- The inverse comparison recovers each vertex inclusion. -/
@[reassoc (attr := simp)]
lemma map_ι_cubeComplexMapIso_inv_f {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    G.map (F.cubeComplexι S) ≫ (F.cubeComplexMapIso G).inv.f r =
      (F ⋙ G).cubeComplexι S := by
  rw [← ι_cubeComplexMapIso_hom_f F G S, Category.assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]

/-- The inverse comparison followed by a vertex projection is its image under the functor. -/
@[reassoc (attr := simp)]
lemma cubeComplexMapIso_inv_f_π {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.cubeComplexMapIso G).inv.f r ≫ (F ⋙ G).cubeComplexπ S = G.map (F.cubeComplexπ S) := by
  apply (cancel_epi ((F.cubeComplexMapIso G).hom.f r)).1
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.id_comp]
  apply (F ⋙ G).cubeComplex_hom_ext fun T ↦ ?_
  by_cases h : T = S
  · subst h
    simp [← G.map_comp]
  · simp [h, ← G.map_comp]

/-- The forward comparison recovers each mapped vertex projection. -/
@[reassoc (attr := simp)]
lemma cubeComplexMapIso_hom_f_map_π {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.cubeComplexMapIso G).hom.f r ≫ G.map (F.cubeComplexπ S) =
      (F ⋙ G).cubeComplexπ S := by
  rw [← cubeComplexMapIso_inv_f_π F G S, ← Category.assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.id_comp]

/-- The comparison commutes with maps of cubes. -/
@[reassoc]
lemma cubeComplexMapIso_hom_naturality {F' : Finset ι ⥤ C} (α : F ⟶ F') :
    NatTrans.cubeComplexMap (whiskerRight α G) ≫ (F'.cubeComplexMapIso G).hom =
      (F.cubeComplexMapIso G).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (NatTrans.cubeComplexMap α) := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply (F ⋙ G).cubeComplex_hom_ext
  intro S
  simp only [HomologicalComplex.comp_f, NatTrans.ι_cubeComplexMap_f_assoc,
    ι_cubeComplexMapIso_hom_f, whiskerRight_app, ι_cubeComplexMapIso_hom_f_assoc,
    mapHomologicalComplex_map_f, ← G.map_comp, NatTrans.ι_cubeComplexMap_f]

/-- Totalization commutes naturally with postcomposition by an additive functor. -/
def cubeComplexMapNatIso :
    (whiskeringRight (Finset ι) C D).obj G ⋙ cubeComplexFunctor D ι ≅
      cubeComplexFunctor C ι ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun F ↦ F.cubeComplexMapIso G)
    (fun α ↦ cubeComplexMapIso_hom_naturality _ _ α)

/-- The forward natural comparison at a cube is its totalization comparison. -/
@[simp]
lemma cubeComplexMapNatIso_hom_app :
    (G.cubeComplexMapNatIso (ι := ι)).hom.app F = (F.cubeComplexMapIso G).hom := (rfl)

/-- The inverse natural comparison at a cube is its inverse totalization comparison. -/
@[simp]
lemma cubeComplexMapNatIso_inv_app :
    (G.cubeComplexMapNatIso (ι := ι)).inv.app F = (F.cubeComplexMapIso G).inv := (rfl)

/-- The comparison also commutes with natural transformations of additive functors. -/
@[reassoc]
lemma cubeComplexMapIso_hom_naturality_functor (G' : C ⥤ D) [G'.Additive] (τ : G ⟶ G') :
    NatTrans.cubeComplexMap (whiskerLeft F τ) ≫ (F.cubeComplexMapIso G').hom =
      (F.cubeComplexMapIso G).hom ≫
        (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app F.cubeComplex := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply (F ⋙ G).cubeComplex_hom_ext
  intro S
  simp only [HomologicalComplex.comp_f, NatTrans.ι_cubeComplexMap_f_assoc,
    ι_cubeComplexMapIso_hom_f, whiskerLeft_app, ι_cubeComplexMapIso_hom_f_assoc,
    NatTrans.mapHomologicalComplex_app_f, τ.naturality]

/-- The comparison for the identity functor agrees with the native identity comparisons. -/
lemma cubeComplexMapIso_id :
    (F.cubeComplexMapIso (𝟭 C)).hom ≫
        (mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app F.cubeComplex =
      NatTrans.cubeComplexMap (rightUnitor F).hom := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply (F ⋙ 𝟭 C).cubeComplex_hom_ext
  intro S
  simp

/-- Applying two additive functors successively gives the comparison for their composite,
with the native associativity and degreewise-functor comparisons. -/
lemma cubeComplexMapIso_comp (H : D ⥤ E) [H.Additive] :
    (F.cubeComplexMapIso (G ⋙ H)).hom =
      NatTrans.cubeComplexMap (associator F G H).inv ≫
        ((F ⋙ G).cubeComplexMapIso H).hom ≫
          (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (F.cubeComplexMapIso G).hom ≫
            (mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).hom.app
              F.cubeComplex := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply (F ⋙ G ⋙ H).cubeComplex_hom_ext
  intro S
  simp [← H.map_comp]

end CategoryTheory.Functor
