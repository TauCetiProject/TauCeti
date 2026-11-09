/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic
public import TauCeti.Algebra.Module.GradedModule.Homology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The bigrading of simply blocked grid homology

The one-variable specialization of an odd-component grid has an internal
`(O-Maslov, Alexander)` grading on its homology. A homogeneous class is precisely a class
with a homogeneous cycle representative, measured after the actual `simplyBlockedChainEquiv`.
For knot grids this is the bigrading of `G-hat`. For a link with several components this is
only the one-variable specialization: simply blocked link homology blocks one marking on
each component.

The homogeneous pieces are modules over the coefficient ring. We use the explicit
`ModuleCat.restrictScalars` presentation of categorical homology to preserve its polynomial
module structure and coefficient action. The internal decomposition prepares the bigraded
Euler characteristic; no identification with the Alexander polynomial is asserted here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)
  [CommRing R] [CharP R 2] (i : Fin n)

local notation "Poly" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "C" => GridDiagram.simplyBlockedComplex G.val R i
local notation "d" => ModuleCat.Hom.hom (HomologicalComplex.d C () ())
local notation "Base" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* Poly)

-- These are precisely the coefficient actions selected by `ModuleCat.restrictScalars`.
/-- The coefficient action on the actual specialized complex carrier is restriction of its
polynomial action along `MvPolynomial.C`, as in `ModuleCat.restrictScalars`. -/
local instance hatComplexCoefficientModule : Module R ((C).X ()) :=
  Module.compHom _ (MvPolynomial.C : R →+* Poly)
local instance : IsScalarTower R Poly ((C).X ()) := IsScalarTower.of_compHom R Poly _
/-- The coefficient action on categorical specialization homology is restriction of its
polynomial action along `MvPolynomial.C`, as in the public restricted-scalar presentation. -/
local instance hatHomologyCoefficientModule : Module R ((C).homology ()) :=
  Module.compHom _ (MvPolynomial.C : R →+* Poly)
local instance : IsScalarTower R Poly ((C).homology ()) := IsScalarTower.of_compHom R Poly _

private noncomputable def hatComplexGrading : InternalGrading R ((C).X ()) (ℤ × ℤ) :=
  (InternalGrading.mk (G.bigradedChainHatPiece R i)
    (G.isInternal_bigradedChainHatPiece R i)).map
      ((G.1.simplyBlockedChainEquiv R i).symm.restrictScalars R)

private theorem mem_hatComplexGrading_piece {g : ℤ × ℤ} {c : (C).X ()} :
    c ∈ (hatComplexGrading G R i).piece g ↔
      G.1.simplyBlockedChainEquiv R i c ∈ G.bigradedChainHatPiece R i g := by
  rw [hatComplexGrading, InternalGrading.mem_map_piece_iff]
  simp only [LinearEquiv.restrictScalars_symm_apply, LinearEquiv.symm_symm]

private theorem hatDifferential_homogeneous :
    LinearMap.IsHomogeneous d (hatComplexGrading G R i).piece
      (hatComplexGrading G R i).piece (-(1, 0)) := by
  rw [LinearMap.isHomogeneous_def]
  intro g c hc
  rw [mem_hatComplexGrading_piece] at hc ⊢
  rw [G.1.simplyBlockedChainEquiv_d]
  simpa only [sub_eq_add_neg] using G.simplyBlockedDifferential_mem_bigradedChainHatPiece hc

private noncomputable def hatHomologyEquiv :
    (d).homology (C).hom_d_comp_hom_d ≃ₗ[R] (Base).obj ((C).homology ()) :=
  (C).moduleCatHomologyIso.symm.toLinearEquiv.restrictScalars R

/-- The internal `(O-Maslov, Alexander)` grading on the homology of a one-variable specialization.
The coefficient action is explicitly restriction of its polynomial action. -/
noncomputable def bigradedHatHomologyGrading :
    InternalGrading R ((Base).obj ((C).homology ())) (ℤ × ℤ) :=
  ((hatComplexGrading G R i).homology (hatDifferential_homogeneous G R i)
    (C).hom_d_comp_hom_d).map (hatHomologyEquiv G R i)

/-- The bidegree-`g` piece of the homology of the one-variable specialization. -/
noncomputable def bigradedHatHomologyPiece (g : ℤ × ℤ) :
    Submodule R ((Base).obj ((C).homology ())) :=
  (G.bigradedHatHomologyGrading R i).piece g

/-- The pieces of the bundled grading are the homogeneous specialization homology pieces. -/
@[simp]
theorem bigradedHatHomologyGrading_piece (g : ℤ × ℤ) :
    (G.bigradedHatHomologyGrading R i).piece g = G.bigradedHatHomologyPiece R i g := by
  rw [bigradedHatHomologyPiece]

/-- A class is homogeneous exactly when it has a cycle representative whose actual specialized
chain has the specified bidegree. -/
theorem mem_bigradedHatHomologyPiece_iff {g : ℤ × ℤ} {y : (Base).obj ((C).homology ())} :
    y ∈ G.bigradedHatHomologyPiece R i g ↔
      ∃ z : LinearMap.ker d,
        G.1.simplyBlockedChainEquiv R i z ∈ G.bigradedChainHatPiece R i g ∧
          G.1.oneVariableSpecializationHomologyClass R i z = y := by
  rw [bigradedHatHomologyPiece, bigradedHatHomologyGrading,
    InternalGrading.mem_map_piece_iff, InternalGrading.mem_homology_piece_iff]
  simp only [mem_hatComplexGrading_piece]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, ?_⟩
    apply (C).moduleCatHomologyIso.toLinearEquiv.injective
    exact ((C).moduleCatHomologyIso_hom_moduleCatKerHomologyClass z).trans hzy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, ((C).moduleCatHomologyIso_hom_moduleCatKerHomologyClass z).symm⟩

/-- A homogeneous cycle represents a class of the same bidegree. -/
theorem oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ} {z : LinearMap.ker d}
    (hz : G.1.simplyBlockedChainEquiv R i z ∈ G.bigradedChainHatPiece R i g) :
    G.1.oneVariableSpecializationHomologyClass R i z ∈ G.bigradedHatHomologyPiece R i g :=
  (G.mem_bigradedHatHomologyPiece_iff R i).mpr ⟨z, hz, rfl⟩

/-- The homogeneous pieces span the homology of the specialization. -/
theorem iSup_bigradedHatHomologyPiece_eq_top :
    ⨆ g, G.bigradedHatHomologyPiece R i g = ⊤ :=
  (G.bigradedHatHomologyGrading R i).isInternal.submodule_iSup_eq_top

/-- The homogeneous homology pieces are independent. -/
theorem iSupIndep_bigradedHatHomologyPiece :
    iSupIndep (G.bigradedHatHomologyPiece R i) :=
  (G.bigradedHatHomologyGrading R i).isInternal.submodule_iSupIndep

/-- The homology of the specialization is the internal direct sum of its bidegree pieces. -/
theorem isInternal_bigradedHatHomologyPiece :
    DirectSum.IsInternal (G.bigradedHatHomologyPiece R i) :=
  (G.bigradedHatHomologyGrading R i).isInternal

/-- Multiplication by a surviving polynomial variable lowers homology bidegree by `(2, 1)`.
This statement also applies to the one-variable specialization of a multi-component grid. -/
theorem X_smul_mem_bigradedHatHomologyPiece (j : {c : Fin n // c ≠ i})
    {g : ℤ × ℤ} {y : (Base).obj ((C).homology ())}
    (hy : y ∈ G.bigradedHatHomologyPiece R i g) :
    (MvPolynomial.X j : Poly) • y ∈ G.bigradedHatHomologyPiece R i (g - (2, 1)) := by
  rw [bigradedHatHomologyPiece, bigradedHatHomologyGrading,
    InternalGrading.mem_map_piece_iff] at hy ⊢
  have he : (hatHomologyEquiv G R i).symm ((MvPolynomial.X j : Poly) • y) =
      (MvPolynomial.X j : Poly) • (hatHomologyEquiv G R i).symm y :=
    (C).moduleCatHomologyIso.hom.hom.map_smul _ _
  rw [he, sub_eq_add_neg]
  refine (hatComplexGrading G R i).smul_mem_homology_piece
    (hatDifferential_homogeneous G R i) (C).hom_d_comp_hom_d (fun g c hc => ?_) hy
  rw [mem_hatComplexGrading_piece] at hc ⊢
  rw [map_smul]
  simpa only [sub_eq_add_neg] using G.X_smul_mem_bigradedChainHatPiece j hc

end TauCeti.OddComponentGridDiagram
