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

The comparison API restricts semilinear homology equivalences to coefficient scalars, descends
chain-level bigrading preservation, and restricts homogeneous equivalences to their pieces.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n m : ℕ} {G : GridDiagram n} {H : GridDiagram m}
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n) (j : Fin m)

/-- A semilinear specialization-homology equivalence fixing constant polynomials is linear over
its coefficient ring, with the actions selected by `ModuleCat.restrictScalars`. -/
noncomputable def oneVariableSpecializationHomologyCoefficientEquiv
    (σ : MvPolynomial {c : Fin n // c ≠ i} R →+*
      MvPolynomial {c : Fin m // c ≠ j} R)
    {σ' : MvPolynomial {c : Fin m // c ≠ j} R →+*
      MvPolynomial {c : Fin n // c ≠ i} R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : (G.simplyBlockedComplex R i).homology () ≃ₛₗ[σ]
      (H.simplyBlockedComplex R j).homology ())
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r) :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* _)).obj
        ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* _)).obj
        ((H.simplyBlockedComplex R j).homology ()) :=
  { e.toAddEquiv with
    map_smul' := fun r x => by
      rw [ModuleCat.restrictScalars.smul_def, RingHom.id_apply,
        ModuleCat.restrictScalars.smul_def']
      exact (e.map_smulₛₗ (MvPolynomial.C r) x).trans (by rw [hσ]; rfl) }

-- Keep these application equations as named rewrites: simplifying a forward application before
-- its enclosing inverse changes the bundled equivalence and prevents generic inverse laws matching.
/-- Restricting coefficient scalars preserves the chosen map. -/
theorem oneVariableSpecializationHomologyCoefficientEquiv_apply
    (σ : MvPolynomial {c : Fin n // c ≠ i} R →+*
      MvPolynomial {c : Fin m // c ≠ j} R)
    {σ' : MvPolynomial {c : Fin m // c ≠ j} R →+*
      MvPolynomial {c : Fin n // c ≠ i} R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : (G.simplyBlockedComplex R i).homology () ≃ₛₗ[σ]
      (H.simplyBlockedComplex R j).homology ())
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r) (x) :
    oneVariableSpecializationHomologyCoefficientEquiv R i j σ e hσ x = e x := (rfl)

/-- Restricting coefficient scalars preserves the chosen inverse. -/
theorem oneVariableSpecializationHomologyCoefficientEquiv_symm_apply
    (σ : MvPolynomial {c : Fin n // c ≠ i} R →+*
      MvPolynomial {c : Fin m // c ≠ j} R)
    {σ' : MvPolynomial {c : Fin m // c ≠ j} R →+*
      MvPolynomial {c : Fin n // c ≠ i} R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : (G.simplyBlockedComplex R i).homology () ≃ₛₗ[σ]
      (H.simplyBlockedComplex R j).homology ())
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r) (x) :
    (oneVariableSpecializationHomologyCoefficientEquiv R i j σ e hσ).symm x = e.symm x := (rfl)

end TauCeti.GridDiagram

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

section Comparison

variable {m : ℕ} (H : OddComponentGridDiagram m) (j : Fin m)

local notation "BaseH" => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
local notation "D" => GridDiagram.simplyBlockedComplex H.val R j

/-- Cycle-level preservation of the chain bigrading descends to a degree-zero homology map.
The class equation keeps this independent of how the homology comparison was constructed. -/
theorem isHomogeneous_oneVariableSpecializationHomologyMap
    (f : (Base).obj ((C).homology ()) →ₗ[R] (BaseH).obj ((D).homology ()))
    (cycles : LinearMap.ker d → LinearMap.ker ((D).d () ()).hom)
    (hclass : ∀ z, f (G.1.oneVariableSpecializationHomologyClass R i z) =
      H.1.oneVariableSpecializationHomologyClass R j (cycles z))
    (hdegree : ∀ (g : ℤ × ℤ) (z : LinearMap.ker d),
      G.1.simplyBlockedChainEquiv R i z ∈ G.bigradedChainHatPiece R i g →
      H.1.simplyBlockedChainEquiv R j (cycles z) ∈ H.bigradedChainHatPiece R j g) :
    LinearMap.IsHomogeneous f (G.bigradedHatHomologyGrading R i).piece
      (H.bigradedHatHomologyGrading R j).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  rw [add_zero, bigradedHatHomologyGrading_piece] at ⊢
  rw [bigradedHatHomologyGrading_piece] at hy
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedHatHomologyPiece_iff R i).mp hy
  rw [hclass]
  exact H.oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece R j
    (hdegree g z hz)

/-- A degree-zero homology equivalence preserves and reflects membership in each piece. -/
theorem homologyEquiv_mem_bigradedHatHomologyPiece_iff
    (e : (Base).obj ((C).homology ()) ≃ₗ[R] (BaseH).obj ((D).homology ()))
    (he : LinearMap.IsHomogeneous e.toLinearMap (G.bigradedHatHomologyGrading R i).piece
      (H.bigradedHatHomologyGrading R j).piece 0)
    (g : ℤ × ℤ) (y : (Base).obj ((C).homology ())) :
    e y ∈ H.bigradedHatHomologyPiece R j g ↔ y ∈ G.bigradedHatHomologyPiece R i g := by
  constructor
  · intro hy
    rw [← bigradedHatHomologyGrading_piece] at hy
    simpa only [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using he.linearEquiv_symm.map_mem hy
  · intro hy
    rw [← bigradedHatHomologyGrading_piece] at hy
    simpa only [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe] using
      he.map_mem hy

/-- Restrict a degree-zero specialization-homology equivalence to a specified bidegree. -/
noncomputable def oneVariableSpecializationHomologyPieceEquivOfHomogeneous
    (e : (Base).obj ((C).homology ()) ≃ₗ[R] (BaseH).obj ((D).homology ()))
    (he : LinearMap.IsHomogeneous e.toLinearMap (G.bigradedHatHomologyGrading R i).piece
      (H.bigradedHatHomologyGrading R j).piece 0) (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] H.bigradedHatHomologyPiece R j g :=
  e.ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv,
      ← G.homologyEquiv_mem_bigradedHatHomologyPiece_iff R i H j e he g,
      LinearEquiv.apply_symm_apply])

/-- The restricted piece equivalence is the chosen total equivalence on underlying classes. -/
@[simp]
theorem coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_apply
    (e : (Base).obj ((C).homology ()) ≃ₗ[R] (BaseH).obj ((D).homology ()))
    (he : LinearMap.IsHomogeneous e.toLinearMap (G.bigradedHatHomologyGrading R i).piece
      (H.bigradedHatHomologyGrading R j).piece 0) (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationHomologyPieceEquivOfHomogeneous R i H j e he g y :
      (BaseH).obj ((D).homology ())) = e y.1 := (rfl)

/-- The inverse restricted piece equivalence is the chosen total inverse on underlying classes. -/
@[simp]
theorem coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_symm_apply
    (e : (Base).obj ((C).homology ()) ≃ₗ[R] (BaseH).obj ((D).homology ()))
    (he : LinearMap.IsHomogeneous e.toLinearMap (G.bigradedHatHomologyGrading R i).piece
      (H.bigradedHatHomologyGrading R j).piece 0) (g : ℤ × ℤ)
    (y : H.bigradedHatHomologyPiece R j g) :
    ((G.oneVariableSpecializationHomologyPieceEquivOfHomogeneous R i H j e he g).symm y :
      (Base).obj ((C).homology ())) = e.symm y.1 := (rfl)

end Comparison

end TauCeti.OddComponentGridDiagram
