/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit

/-!
# Endpoint terms of an inverse braid-complex product

The cochain tensor product of the braid complex `Bᵢ` with its inverse `Bᵢ'` has one term in
cohomological degree `-1` and one in degree `1`. The balanced tensor unitors identify them with
the vertex bimodule `Pᵢ ⊗ₖ eᵢ Z` and its internal shift by `-2`. These identifications are the
outer terms of `TauCeti.zigzagBraidComplexTensorInverseHomotopyEquiv`, which cancels the middle
terms to show that `Bᵢ ⊗ Bᵢ'` is homotopy equivalent to the regular graded bimodule `Z` in
degree zero.

The calculation is valid for the public componentwise zigzag algebra, including isolated
vertices.

## References

* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, J. Amer. Math.
  Soc. 15 (2002) (the complexes `R_i` and `R_i'` of the zigzag algebra `A_m`).
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001) (zigzag algebras of arbitrary graphs and the same complexes).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "B" => zigzagBraidComplex k G
local notation "B'" => zigzagBraidInverseComplex k G
local notation "c" => ComplexShape.up ℤ

/-- The cochain tensor product of the braid complex and its inverse at one vertex. -/
abbrev zigzagBraidInverseComplexTensor (i : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (B i) (B' i) F c

local notation "T" => zigzagBraidInverseComplexTensor k G

/-- A summand of `Bᵢ ⊗ Bᵢ'` vanishes unless its degrees lie in `{-1, 0} × {0, 1}`. -/
theorem isZero_zigzagBraidInverseComplexTensor_pair (i : V) (p q : ℤ)
    (h : ¬ ((p = -1 ∨ p = 0) ∧ (q = 0 ∨ q = 1))) :
    Limits.IsZero (((F).obj ((B i).X p)).obj ((B' i).X q)) := by
  by_cases hp : p = -1 ∨ p = 0
  · exact ((F).obj ((B i).X p)).map_isZero
      (isZero_zigzagBraidInverseComplex_X i (by omega) (by omega))
  · exact ((F).flip.obj ((B' i).X q)).map_isZero
      (isZero_zigzagBraidComplex_X i (by omega) (by omega))

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

/-- The degree `-1` term of `Bᵢ ⊗ Bᵢ'` is the vertex bimodule. -/
def zigzagBraidInverseTensorXMinusOneIso (i : V) : (T i).X (-1) ≅ U i :=
  HomologicalComplex.mapBifunctorSingleSummandIso (B i) (B' i) F c (-1) 0 (-1) (by simp)
      (fun p q hpq _ ↦ isZero_zigzagBraidInverseComplexTensor_pair k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    inverseTensorLeftIso k G i

/-- The degree `1` term of `Bᵢ ⊗ Bᵢ'` is the vertex bimodule shifted by `-2`. -/
def zigzagBraidInverseTensorXOneIso (i : V) : (T i).X 1 ≅
    (GradedModuleCat.shiftFunctor (-2)).obj (U i) :=
  HomologicalComplex.mapBifunctorSingleSummandIso (B i) (B' i) F c 0 1 1 (by simp)
      (fun p q hpq _ ↦ isZero_zigzagBraidInverseComplexTensor_pair k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    inverseTensorRightIso k G i

/-- The degree `(-1, 0)` summand includes into degree `-1` as the right unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidInverseTensorXMinusOneIso_hom (i : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c (-1) 0 (-1) (by simp) ≫
        (zigzagBraidInverseTensorXMinusOneIso k G i).hom =
      ((((F).flip.obj ((B' i).X 0)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
        ((F).obj (U i)).mapIso (zigzagBraidInverseComplexXIso₀ k G i)) ≪≫
          zigzagBimoduleRightUnitor k G (U i)).hom := by
  simp only [zigzagBraidInverseTensorXMinusOneIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc, inverseTensorLeftIso,
    Category.assoc]

/-- The degree `(0, 1)` summand includes into degree `1` as the left unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidInverseTensorXOneIso_hom (i : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c 0 1 1 (by simp) ≫
        (zigzagBraidInverseTensorXOneIso k G i).hom =
      ((((F).flip.obj ((B' i).X 1)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
        ((F).obj Z).mapIso (zigzagBraidInverseComplexXIso₁ k G i)) ≪≫
          zigzagBimoduleLeftUnitor k G ((GradedModuleCat.shiftFunctor (-2)).obj (U i))).hom := by
  simp only [zigzagBraidInverseTensorXOneIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc, inverseTensorRightIso,
    Category.assoc]

end TauCeti
