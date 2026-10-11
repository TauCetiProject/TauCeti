/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Endpoint terms of an inverse braid-complex product

The cochain tensor product of the braid complex `Bᵢ` with its inverse `Bᵢ'` has one term in
cohomological degree `-1` and one in degree `1`. The balanced tensor unitors identify them with
the vertex bimodule `Pᵢ ⊗ₖ eᵢ Z` and its internal shift by `-2`. These identifications give the
outer terms needed when the middle terms are cancelled to prove the inverse homotopy equivalence.

The calculation is valid for the public componentwise zigzag algebra, including isolated
vertices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- The integer-graded algebra structure used by the braid-complex tensor product. -/
local instance : GradedAlgebra (zigzagAlgebraInternalGrading k G).piece :=
  zigzagAlgebraIntegerGradedAlgebra k G

local notation "F" => zigzagBimoduleTensor k G
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "B" => zigzagBraidComplex k G
local notation "B'" => zigzagBraidInverseComplex k G
local notation "c" => ComplexShape.up ℤ

/-- The cochain tensor product of the braid complex and its inverse at one vertex. -/
noncomputable abbrev zigzagBraidInverseComplexTensor (i : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (B i) (B' i) F c

local notation "T" => zigzagBraidInverseComplexTensor k G

private def inverseTensorLeftIso (i : V) :
    ((F).obj ((B i).X (-1))).obj ((B' i).X 0) ≅ U i :=
  ((F).flip.obj ((B' i).X 0)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
    ((F).obj (U i)).mapIso (zigzagBraidInverseComplexXIso₀ k G i) ≪≫
      zigzagBimoduleRightUnitor k G (U i)

private def inverseTensorRightIso (i : V) :
    ((F).obj ((B i).X 0)).obj ((B' i).X 1) ≅
      (GradedModuleCat.shiftFunctor (-2)).obj (U i) :=
  ((F).flip.obj ((B' i).X 1)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
    ((F).obj Z).mapIso (zigzagBraidInverseComplexXIso₁ k G i) ≪≫
      zigzagBimoduleLeftUnitor k G ((GradedModuleCat.shiftFunctor (-2)).obj (U i))

private def inverseTensorLeftMap (i : V) (p q : ℤ) :
    ((F).obj ((B i).X p)).obj ((B' i).X q) ⟶ U i := by
  by_cases hp : p = -1
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (inverseTensorLeftIso k G i).hom
    · exact 0
  · exact 0

private def inverseTensorLeftHom (i : V) : (T i).X (-1) ⟶ U i :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ inverseTensorLeftMap k G i p q)

private theorem inverseTensorLeftMap_supported (i : V) :
    inverseTensorLeftMap k G i (-1) 0 = (inverseTensorLeftIso k G i).hom := by
  simp only [inverseTensorLeftMap, dite_true]

private def inverseTensorLeftInv (i : V) : U i ⟶ (T i).X (-1) :=
  (inverseTensorLeftIso k G i).inv ≫
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c (-1) 0 (-1) (by simp)

/-- The degree `-1` term of `Bᵢ ⊗ Bᵢ'` is the vertex bimodule. -/
def zigzagBraidInverseTensorXMinusOneIso (i : V) : (T i).X (-1) ≅ U i where
  hom := inverseTensorLeftHom k G i
  inv := inverseTensorLeftInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- `mapBifunctor.hom_ext` states the component index using the tensor complex's
    -- `ComplexShape` predicate; unfold that predicate to its degree-sum equation before
    -- solving for the supported bidegrees. Rewriting cannot use the sum until this reduction.
    change p + q = -1 at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [inverseTensorLeftHom, inverseTensorLeftInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, inverseTensorLeftMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · by_cases hp' : p = 0
      · subst p
        have hq : q = -1 := by omega
        subst q
        exact (((F).obj ((B i).X 0)).map_isZero
          (isZero_zigzagBraidInverseComplex_X i (by omega) (by omega))).eq_of_src _ _
      · exact (((F).flip.obj ((B' i).X q)).map_isZero
          (isZero_zigzagBraidComplex_X i hp hp')).eq_of_src _ _
  inv_hom_id := by
    simp only [inverseTensorLeftHom, inverseTensorLeftInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, inverseTensorLeftMap_supported,
      Iso.inv_hom_id]

private def inverseTensorRightMap (i : V) (p q : ℤ) :
    ((F).obj ((B i).X p)).obj ((B' i).X q) ⟶
      (GradedModuleCat.shiftFunctor (-2)).obj (U i) := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 1
    · subst q
      exact (inverseTensorRightIso k G i).hom
    · exact 0
  · exact 0

private def inverseTensorRightHom (i : V) : (T i).X 1 ⟶
    (GradedModuleCat.shiftFunctor (-2)).obj (U i) :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ inverseTensorRightMap k G i p q)

private theorem inverseTensorRightMap_supported (i : V) :
    inverseTensorRightMap k G i 0 1 = (inverseTensorRightIso k G i).hom := by
  simp only [inverseTensorRightMap, dite_true]

private def inverseTensorRightInv (i : V) :
    (GradedModuleCat.shiftFunctor (-2)).obj (U i) ⟶ (T i).X 1 :=
  (inverseTensorRightIso k G i).inv ≫
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c 0 1 1 (by simp)

/-- The degree `1` term of `Bᵢ ⊗ Bᵢ'` is the vertex bimodule shifted by `-2`. -/
def zigzagBraidInverseTensorXOneIso (i : V) : (T i).X 1 ≅
    (GradedModuleCat.shiftFunctor (-2)).obj (U i) where
  hom := inverseTensorRightHom k G i
  inv := inverseTensorRightInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- As above, reduce the tensor complex's `ComplexShape` predicate to its degree sum so
    -- arithmetic can identify the supported bidegrees.
    change p + q = 1 at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 1 := by omega
      subst q
      simp only [inverseTensorRightHom, inverseTensorRightInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, inverseTensorRightMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · by_cases hq : q = 0
      · subst q
        have hp' : p = 1 := by omega
        subst p
        exact (((F).flip.obj ((B' i).X 0)).map_isZero
          (isZero_zigzagBraidComplex_X i (by omega) (by omega))).eq_of_src _ _
      · have hq' : q ≠ 1 := by
          intro h
          subst q
          exact hp (by omega)
        exact (((F).obj ((B i).X p)).map_isZero
          (isZero_zigzagBraidInverseComplex_X i hq hq')).eq_of_src _ _
  inv_hom_id := by
    simp only [inverseTensorRightHom, inverseTensorRightInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, inverseTensorRightMap_supported,
      Iso.inv_hom_id]

/-- The degree `(-1, 0)` summand includes into degree `-1` as the right unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidInverseTensorXMinusOneIso_hom (i : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c (-1) 0 (-1) (by simp) ≫
        (zigzagBraidInverseTensorXMinusOneIso k G i).hom =
      ((((F).flip.obj ((B' i).X 0)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
        ((F).obj (U i)).mapIso (zigzagBraidInverseComplexXIso₀ k G i)) ≪≫
          zigzagBimoduleRightUnitor k G (U i)).hom := by
  -- The iso field in the conclusion is definitionally the descended map. Expose that field
  -- and the private hom abbreviation; a rewrite cannot match through these reducible wrappers.
  change HomologicalComplex.ιMapBifunctor (B i) (B' i) F c (-1) 0 (-1) (by simp) ≫
      inverseTensorLeftHom k G i = (inverseTensorLeftIso k G i).hom
  simp only [inverseTensorLeftHom, HomologicalComplex.ι_mapBifunctorDesc,
    inverseTensorLeftMap_supported]

/-- The degree `(0, 1)` summand includes into degree `1` as the left unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidInverseTensorXOneIso_hom (i : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c 0 1 1 (by simp) ≫
        (zigzagBraidInverseTensorXOneIso k G i).hom =
      ((((F).flip.obj ((B' i).X 1)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
        ((F).obj Z).mapIso (zigzagBraidInverseComplexXIso₁ k G i)) ≪≫
          zigzagBimoduleLeftUnitor k G ((GradedModuleCat.shiftFunctor (-2)).obj (U i))).hom := by
  -- Reduce the iso field and private hom abbreviation so the supported component equation
  -- can be discharged by the following simplification.
  change HomologicalComplex.ιMapBifunctor (B i) (B' i) F c 0 1 1 (by simp) ≫
      inverseTensorRightHom k G i = (inverseTensorRightIso k G i).hom
  simp only [inverseTensorRightHom, HomologicalComplex.ι_mapBifunctorDesc,
    inverseTensorRightMap_supported]

end TauCeti
