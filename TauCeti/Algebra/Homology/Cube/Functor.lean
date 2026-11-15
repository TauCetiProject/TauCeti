/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.Algebra.Homology.Cube.Basic

/-!
# Additive functors and the signed totalization of a cube

An additive functor `G : C ⥤ D` between preadditive categories with finite biproducts commutes
with the signed totalization of finite commutative cubes
(`CategoryTheory.Functor.mapCubeComplexIso`): mapping the cochain complex `F.cubeComplex` termwise
by `G` is canonically isomorphic to the signed totalization `(F ⋙ G).cubeComplex` of the composed
cube, because `G` preserves the finite biproducts forming each height summand and the signed sums
of edge maps forming the differential.

The comparison is natural in cube morphisms (`NatTrans.mapHomologicalComplex_cubeComplexMap`) and
packages into a natural isomorphism of functors `CategoryTheory.cubeComplexCompIso`.

## Main definitions and results

* `CategoryTheory.Functor.mapCubeComplexIso`: the cochain isomorphism
  `(G.mapHomologicalComplex (.up ℤ)).obj F.cubeComplex ≅ (F ⋙ G).cubeComplex`.
* `CategoryTheory.Functor.map_cubeComplexι_comp_mapCubeComplexIso_hom`,
  `CategoryTheory.Functor.mapCubeComplexIso_hom_π`,
  `CategoryTheory.Functor.ι_mapCubeComplexIso_inv`, and
  `CategoryTheory.Functor.mapCubeComplexIso_inv_comp_map_cubeComplexπ`: its action on vertex
  inclusions and projections.
* `CategoryTheory.NatTrans.mapHomologicalComplex_cubeComplexMap`: naturality with respect to
  morphisms of cubes.
* `CategoryTheory.cubeComplexCompIso`: the natural isomorphism
  `cubeComplexFunctor C ι ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    (Functor.whiskeringRight (Finset ι) C D).obj G ⋙ cubeComplexFunctor D ι`.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]
  {ι : Type w} [Fintype ι] [LinearOrder ι]

namespace Functor

variable (F : Finset ι ⥤ C) (G : C ⥤ D) [G.Additive]

/-- The degree-`r` component of the comparison between `G` applied to `F.cubeComplex` and
`(F ⋙ G).cubeComplex`, assembled from the vertex projections and inclusions. -/
private def mapCubeComplexXIso (r : ℤ) :
    ((G.mapHomologicalComplex (.up ℤ)).obj F.cubeComplex).X r ≅ (F ⋙ G).cubeComplex.X r where
  hom := (F ⋙ G).cubeComplexLift fun S ↦ G.map (F.cubeComplexπ S)
  inv := (F ⋙ G).cubeComplexDesc fun S ↦ G.map (F.cubeComplexι S)
  hom_inv_id := by
    calc
      (F ⋙ G).cubeComplexLift (fun S ↦ G.map (F.cubeComplexπ S)) ≫
          (F ⋙ G).cubeComplexDesc (fun S ↦ G.map (F.cubeComplexι S)) =
        ∑ S : {S : Finset ι // (#S : ℤ) = r},
          G.map (F.cubeComplexπ S) ≫ G.map (F.cubeComplexι S) := by
        rw [← Category.id_comp ((F ⋙ G).cubeComplexDesc _), ← (F ⋙ G).cubeComplex_total r,
          Preadditive.sum_comp, Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        simp only [Category.assoc, cubeComplexLift_π_assoc, ι_cubeComplexDesc]
      _ = G.map (∑ S : {S : Finset ι // (#S : ℤ) = r}, F.cubeComplexπ S ≫ F.cubeComplexι S) := by
        simp only [← G.map_comp, map_sum]
      _ = 𝟙 _ := by rw [F.cubeComplex_total, G.map_id]
  inv_hom_id := by
    ext T S
    simp only [Category.assoc, cubeComplexLift_π, ι_cubeComplexDesc_assoc, Category.id_comp]
    by_cases h : S = T
    · subst h
      rw [← G.map_comp, F.cubeComplexι_π_self, G.map_id, (F ⋙ G).cubeComplexι_π_self]
      rfl
    · rw [← G.map_comp, F.cubeComplexι_π_of_ne h, G.map_zero, (F ⋙ G).cubeComplexι_π_of_ne h]

/-- **Additive functors commute with the signed cube totalization.** Mapping `F.cubeComplex`
termwise by an additive functor `G` gives `(F ⋙ G).cubeComplex`. -/
def mapCubeComplexIso :
    (G.mapHomologicalComplex (.up ℤ)).obj F.cubeComplex ≅ (F ⋙ G).cubeComplex :=
  HomologicalComplex.Hom.isoOfComponents (F.mapCubeComplexXIso G) <| by
    rintro r _ rfl
    refine (F ⋙ G).cubeComplex_hom_ext' fun T ↦ ?_
    simp only [mapCubeComplexXIso, Functor.mapHomologicalComplex_obj_d, Category.assoc,
      cubeComplexLift_π, (F ⋙ G).cubeComplex_d_π T, Preadditive.comp_sum]
    rw [← G.map_comp, F.cubeComplex_d_π T, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Functor.map_zsmul, G.map_comp, Preadditive.comp_zsmul, cubeComplexLift_π_assoc]
    rfl

/-- `Functor.mapCubeComplexIso` sends the image under `G` of the inclusion of vertex `S` to the
inclusion of `S` in `(F ⋙ G).cubeComplex`. -/
@[reassoc (attr := simp)]
lemma map_cubeComplexι_comp_mapCubeComplexIso_hom {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    G.map (F.cubeComplexι S) ≫ (F.mapCubeComplexIso G).hom.f r = (F ⋙ G).cubeComplexι S := by
  refine (F ⋙ G).cubeComplex_hom_ext' fun T ↦ ?_
  simp only [mapCubeComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f, mapCubeComplexXIso,
    Category.assoc, cubeComplexLift_π, ← G.map_comp]
  by_cases h : S = T
  · subst h
    rw [F.cubeComplexι_π_self, G.map_id, (F ⋙ G).cubeComplexι_π_self]
    rfl
  · rw [F.cubeComplexι_π_of_ne h, G.map_zero, (F ⋙ G).cubeComplexι_π_of_ne h]

/-- The forward map of `Functor.mapCubeComplexIso` projects onto vertex `S` via `G` applied to the
projection of `F.cubeComplex`. -/
@[reassoc (attr := simp)]
lemma mapCubeComplexIso_hom_π {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.mapCubeComplexIso G).hom.f r ≫ (F ⋙ G).cubeComplexπ S = G.map (F.cubeComplexπ S) := by
  simp [mapCubeComplexIso, mapCubeComplexXIso]

/-- The inverse of `Functor.mapCubeComplexIso` restricts on vertex `S` to `G` applied to the
inclusion of `S` in `F.cubeComplex`. -/
@[reassoc (attr := simp)]
lemma ι_mapCubeComplexIso_inv {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F ⋙ G).cubeComplexι S ≫ (F.mapCubeComplexIso G).inv.f r = G.map (F.cubeComplexι S) := by
  simp [mapCubeComplexIso, mapCubeComplexXIso]

/-- Projecting after the inverse of `Functor.mapCubeComplexIso` recovers the vertex projection of
`(F ⋙ G).cubeComplex`. -/
@[reassoc (attr := simp)]
lemma mapCubeComplexIso_inv_comp_map_cubeComplexπ {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.mapCubeComplexIso G).inv.f r ≫ G.map (F.cubeComplexπ S) = (F ⋙ G).cubeComplexπ S := by
  rw [← mapCubeComplexIso_hom_π, ← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.id_comp]

end Functor

namespace NatTrans

/-- `Functor.mapCubeComplexIso` is natural in morphisms of cubes. -/
@[reassoc]
lemma mapHomologicalComplex_cubeComplexMap {F₁ F₂ : Finset ι ⥤ C} (α : F₁ ⟶ F₂)
    (G : C ⥤ D) [G.Additive] :
    (G.mapHomologicalComplex (.up ℤ)).map (cubeComplexMap α) ≫ (F₂.mapCubeComplexIso G).hom =
      (F₁.mapCubeComplexIso G).hom ≫ cubeComplexMap (Functor.whiskerRight α G) := by
  ext r S
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
    Functor.mapCubeComplexIso_hom_π, Functor.mapCubeComplexIso_hom_π_assoc, cubeComplexMap_f_π,
    Functor.whiskerRight_app]
  rw [← G.map_comp, cubeComplexMap_f_π, G.map_comp]

end NatTrans

variable (C ι) in
/-- As a functor of the cube, `Functor.cubeComplex` commutes up to canonical isomorphism with any
additive functor `G : C ⥤ D`. -/
def cubeComplexCompIso (G : C ⥤ D) [G.Additive] :
    cubeComplexFunctor C ι ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight (Finset ι) C D).obj G ⋙ cubeComplexFunctor D ι :=
  NatIso.ofComponents (fun F ↦ F.mapCubeComplexIso G) fun α ↦
    NatTrans.mapHomologicalComplex_cubeComplexMap α G

end CategoryTheory
