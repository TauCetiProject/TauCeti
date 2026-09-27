/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift

/-!
# Naturality of Tate dimension shifting

The canonical connecting isomorphisms for the upward and downward dimension shifts commute
with morphisms of coefficient representations. After tensoring each short exact sequence
on the left, they are natural in both the tensoring and coefficient representations. These squares
transport coefficient maps through dimension shifting in the Tate cup product.

They follow from naturality of the connecting homomorphism and the morphisms of the canonical
dimension-shifting sequences. See Milne, *Class Field Theory*, Chapter II, §1.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

section TensoringVariable

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A M : Rep k G)

variable {M} in
/-- The tensored upward dimension shift is natural in the tensoring representation. -/
theorem tensorDimensionShiftUpIso_hom_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (f ▷ dimensionShiftUp A) ≫
        (tensorDimensionShiftUpIso A M' i j hij).hom =
      (tensorDimensionShiftUpIso A M i j hij).hom ≫ (tateCohomologyFunctor j).map (f ▷ A) := by
  rw [tensorDimensionShiftUpIso_hom, tensorDimensionShiftUpIso_hom]
  exact (HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor k G).mapShortComplex.map
      ((ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A)).mapNatTrans ((curriedTensor (Rep k G)).map f)))
    _ _ i j hij).symm

/-- The inverse tensored upward dimension shift is natural in the tensoring representation. -/
theorem tensorDimensionShiftUpIso_inv_naturality_left {M' : Rep k G} (f : M ⟶ M')
    (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (f ▷ A) ≫
        (tensorDimensionShiftUpIso A M' i j hij).inv =
      (tensorDimensionShiftUpIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map (f ▷ dimensionShiftUp A) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftUpIso_hom_naturality_left,
    Iso.inv_hom_id_assoc]

variable {M} in
/-- The tensored downward dimension shift is natural in the tensoring representation. -/
theorem tensorDimensionShiftDownIso_hom_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (f ▷ A) ≫ (tensorDimensionShiftDownIso A M' i j hij).hom =
      (tensorDimensionShiftDownIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map (f ▷ dimensionShiftDown A) := by
  rw [tensorDimensionShiftDownIso_hom, tensorDimensionShiftDownIso_hom]
  exact (HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor k G).mapShortComplex.map
      ((ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
        (dimensionShiftDownι_comp_indBotCounit A)).mapNatTrans ((curriedTensor (Rep k G)).map f)))
    _ _ i j hij).symm

variable {M} in
/-- The inverse of the tensored downward dimension shift is natural in the tensoring
representation. -/
theorem tensorDimensionShiftDownIso_inv_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (f ▷ dimensionShiftDown A) ≫
        (tensorDimensionShiftDownIso A M' i j hij).inv =
      (tensorDimensionShiftDownIso A M i j hij).inv ≫ (tateCohomologyFunctor i).map (f ▷ A) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftDownIso_hom_naturality_left,
    Iso.inv_hom_id_assoc]


end TensoringVariable

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A B : Rep k G} (f : A ⟶ B) (n : ℤ)

/-- The upward dimension-shifting connecting isomorphism is natural in the coefficient
representation. -/
theorem dimensionShiftUpIso_hom_naturality :
    (tateCohomologyFunctor n).map (Rep.dimensionShiftUpMap f) ≫
        (dimensionShiftUpIso B n).hom =
      (dimensionShiftUpIso A n).hom ≫ (tateCohomologyFunctor (n + 1)).map f := by
  rw [dimensionShiftUpIso_hom, dimensionShiftUpIso_hom]
  have hA : (ShortComplex.mk (Rep.coindBotUnit A) (Rep.dimensionShiftUpπ A)
      (Rep.coindBotUnit_comp_dimensionShiftUpπ A)).ShortExact := by
    simpa only [Rep.dimensionShiftUpSES_def] using Rep.dimensionShiftUpSES_shortExact A
  have hB : (ShortComplex.mk (Rep.coindBotUnit B) (Rep.dimensionShiftUpπ B)
      (Rep.coindBotUnit_comp_dimensionShiftUpπ B)).ShortExact := by
    simpa only [Rep.dimensionShiftUpSES_def] using Rep.dimensionShiftUpSES_shortExact B
  simpa only [Rep.dimensionShiftUpSESMap_τ₁, Rep.dimensionShiftUpSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality hA hB (Rep.dimensionShiftUpSESMap f) n).symm

/-- The inverse upward connecting isomorphism is natural in the coefficient representation. -/
theorem dimensionShiftUpIso_inv_naturality :
    (tateCohomologyFunctor (n + 1)).map f ≫ (dimensionShiftUpIso B n).inv =
      (dimensionShiftUpIso A n).inv ≫
        (tateCohomologyFunctor n).map (Rep.dimensionShiftUpMap f) := by
  rw [Iso.comp_inv_eq, Category.assoc, dimensionShiftUpIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- The downward dimension-shifting connecting isomorphism is natural in the coefficient
representation. -/
theorem dimensionShiftDownIso_hom_naturality :
    (tateCohomologyFunctor n).map f ≫ (dimensionShiftDownIso B n).hom =
      (dimensionShiftDownIso A n).hom ≫
        (tateCohomologyFunctor (n + 1)).map (Rep.dimensionShiftDownMap f) := by
  rw [dimensionShiftDownIso_hom, dimensionShiftDownIso_hom]
  have hA : (ShortComplex.mk (Rep.dimensionShiftDownι A) (Rep.indBotCounit A)
      (Rep.dimensionShiftDownι_comp_indBotCounit A)).ShortExact := by
    simpa only [Rep.dimensionShiftDownSES_def] using Rep.dimensionShiftDownSES_shortExact A
  have hB : (ShortComplex.mk (Rep.dimensionShiftDownι B) (Rep.indBotCounit B)
      (Rep.dimensionShiftDownι_comp_indBotCounit B)).ShortExact := by
    simpa only [Rep.dimensionShiftDownSES_def] using Rep.dimensionShiftDownSES_shortExact B
  simpa only [Rep.dimensionShiftDownSESMap_τ₁, Rep.dimensionShiftDownSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality hA hB (Rep.dimensionShiftDownSESMap f) n).symm

/-- The inverse downward connecting isomorphism is natural in the coefficient representation. -/
theorem dimensionShiftDownIso_inv_naturality :
    (tateCohomologyFunctor (n + 1)).map (Rep.dimensionShiftDownMap f) ≫
        (dimensionShiftDownIso B n).inv =
      (dimensionShiftDownIso A n).inv ≫ (tateCohomologyFunctor n).map f := by
  rw [Iso.comp_inv_eq, Category.assoc, dimensionShiftDownIso_hom_naturality,
    Iso.inv_hom_id_assoc]

variable (M : Rep k G)

/-- The connecting isomorphism for the upward shift remains natural after tensoring on the
left by a fixed representation. -/
theorem tensorDimensionShiftUpIso_hom_naturality_right (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map ((tensorLeft M).map (Rep.dimensionShiftUpMap f)) ≫
        (tensorDimensionShiftUpIso B M i j hij).hom =
      (tensorDimensionShiftUpIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map ((tensorLeft M).map f) := by
  subst j
  rw [tensorDimensionShiftUpIso_hom, tensorDimensionShiftUpIso_hom]
  have hA : ((ShortComplex.mk (Rep.coindBotUnit A) (Rep.dimensionShiftUpπ A)
      (Rep.coindBotUnit_comp_dimensionShiftUpπ A)).map (tensorLeft M)).ShortExact := by
    simpa only [Rep.dimensionShiftUpSES_def] using
      Rep.dimensionShiftUpSES_tensorLeft_shortExact A M
  have hB : ((ShortComplex.mk (Rep.coindBotUnit B) (Rep.dimensionShiftUpπ B)
      (Rep.coindBotUnit_comp_dimensionShiftUpπ B)).map (tensorLeft M)).ShortExact := by
    simpa only [Rep.dimensionShiftUpSES_def] using
      Rep.dimensionShiftUpSES_tensorLeft_shortExact B M
  simpa only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃,
    Rep.dimensionShiftUpSESMap_τ₁, Rep.dimensionShiftUpSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality hA hB
      ((tensorLeft M).mapShortComplex.map (Rep.dimensionShiftUpSESMap f)) i).symm

/-- The inverse tensored upward connecting isomorphism is natural in the coefficient
representation. -/
theorem tensorDimensionShiftUpIso_inv_naturality_right (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map ((tensorLeft M).map f) ≫
        (tensorDimensionShiftUpIso B M i j hij).inv =
      (tensorDimensionShiftUpIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map ((tensorLeft M).map (Rep.dimensionShiftUpMap f)) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftUpIso_hom_naturality_right,
    Iso.inv_hom_id_assoc]

/-- The connecting isomorphism for the downward shift remains natural after tensoring on the
left by a fixed representation. -/
theorem tensorDimensionShiftDownIso_hom_naturality_right (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map ((tensorLeft M).map f) ≫
        (tensorDimensionShiftDownIso B M i j hij).hom =
      (tensorDimensionShiftDownIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map ((tensorLeft M).map (Rep.dimensionShiftDownMap f)) := by
  subst j
  rw [tensorDimensionShiftDownIso_hom, tensorDimensionShiftDownIso_hom]
  have hA : ((ShortComplex.mk (Rep.dimensionShiftDownι A) (Rep.indBotCounit A)
      (Rep.dimensionShiftDownι_comp_indBotCounit A)).map (tensorLeft M)).ShortExact := by
    simpa only [Rep.dimensionShiftDownSES_def] using
      Rep.dimensionShiftDownSES_tensorLeft_shortExact A M
  have hB : ((ShortComplex.mk (Rep.dimensionShiftDownι B) (Rep.indBotCounit B)
      (Rep.dimensionShiftDownι_comp_indBotCounit B)).map (tensorLeft M)).ShortExact := by
    simpa only [Rep.dimensionShiftDownSES_def] using
      Rep.dimensionShiftDownSES_tensorLeft_shortExact B M
  simpa only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃,
    Rep.dimensionShiftDownSESMap_τ₁, Rep.dimensionShiftDownSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality hA hB
      ((tensorLeft M).mapShortComplex.map (Rep.dimensionShiftDownSESMap f)) i).symm

/-- The inverse tensored downward connecting isomorphism is natural in the shifted
coefficient representation. -/
theorem tensorDimensionShiftDownIso_inv_naturality_right (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map ((tensorLeft M).map (Rep.dimensionShiftDownMap f)) ≫
        (tensorDimensionShiftDownIso B M i j hij).inv =
      (tensorDimensionShiftDownIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map ((tensorLeft M).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftDownIso_hom_naturality_right,
    Iso.inv_hom_id_assoc]

end TauCeti.TateCohomology
