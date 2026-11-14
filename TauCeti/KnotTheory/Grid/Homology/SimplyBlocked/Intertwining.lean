/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked

/-!
# Simply blocked homology equivalences induced by intertwining chain equivalences

Several symmetries of grid diagrams act on the simply blocked chain modules by explicit
equivalences of free modules that commute with the differentials. Such an equivalence may move
the blocked `O`-marking from column `i` to another column `j`, and may be semilinear along a
renaming of the surviving polynomial variables. This file passes any such intertwining
equivalence to simply blocked knot-grid homology `G-hat`, characterized on cycle classes.

If the chain equivalence moreover fixes the coefficient scalars and preserves the
`(O-Maslov, Alexander)` bidegree of chains, the induced homology equivalence preserves and
reflects the bigrading of `G-hat`. It then restricts to coefficient-linear equivalences of
homogeneous homology pieces, so the bigraded Poincaré series and the Alexander-graded Euler
characteristic of the two diagrams agree.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.simplyBlockedCyclesEquivOfIntertwining`: the equivalence of cycle
  modules induced by an intertwining chain equivalence.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyEquivOfIntertwining`: the induced equivalence
  of simply blocked homologies.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyPieceEquivOfIntertwining`: its restriction to a
  homogeneous piece, when the chain equivalence preserves bidegrees.

## Main results

* `IsKnot.simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass`: the
  class of a cycle goes to the class of its image.
* `IsKnot.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff`: the induced
  equivalence preserves and reflects the bigrading.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining` and
  `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_of_intertwining`: the
  bigraded Poincaré series and the Euler characteristic agree.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1. The descent
to homology uses Mathlib's `LinearEquiv.ofSubmodules` and `Submodule.Quotient.equiv`, as in the
unblocked construction `TauCeti.GridDiagram.unblockedHomologyEquivOfIntertwining`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G G' : GridDiagram n} (hG : G.IsKnot) {i j : Fin n}

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (hG' : G'.IsKnot)
  {σ : MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ j} R}
  {σ' : MvPolynomial {c : Fin n // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (e : GridChainHat R n i ≃ₛₗ[σ] GridChainHat R n j)
  (he : ∀ c, G'.simplyBlockedDifferential R j (e c) = e (G.simplyBlockedDifferential R i c))

/-! ### The equivalence of homologies -/

/-- The intertwining equivalence between the categorical chain carriers. -/
private def simplyBlockedChainEquivOfIntertwining :
    (G.simplyBlockedComplex R i).X () ≃ₛₗ[σ] (G'.simplyBlockedComplex R j).X () :=
  (G.simplyBlockedChainEquiv R i).trans (e.trans (G'.simplyBlockedChainEquiv R j).symm)

include he in
private theorem simplyBlockedChainEquivOfIntertwining_d (z : (G.simplyBlockedComplex R i).X ()) :
    (G'.simplyBlockedComplex R j).d () () (simplyBlockedChainEquivOfIntertwining R e z) =
      simplyBlockedChainEquivOfIntertwining R e ((G.simplyBlockedComplex R i).d () () z) := by
  apply (G'.simplyBlockedChainEquiv R j).injective
  simp only [simplyBlockedChainEquivOfIntertwining, LinearEquiv.trans_apply,
    simplyBlockedChainEquiv_d, LinearEquiv.apply_symm_apply, he]

/-- The equivalence of simply blocked cycle modules induced by a chain equivalence intertwining
the simply blocked differentials. -/
def simplyBlockedCyclesEquivOfIntertwining :
    hG.simplyBlockedCycles R i ≃ₛₗ[σ] hG'.simplyBlockedCycles R j :=
  (simplyBlockedChainEquivOfIntertwining R e).ofSubmodules _ _
    ((simplyBlockedChainEquivOfIntertwining R e).map_ker_of_intertwine _ _
      (simplyBlockedChainEquivOfIntertwining_d R e he))

/-- On underlying explicit chains, the cycle equivalence is the chain equivalence. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedCyclesEquivOfIntertwining
    (z : hG.simplyBlockedCycles R i) :
    G'.simplyBlockedChainEquiv R j (hG.simplyBlockedCyclesEquivOfIntertwining R hG' e he z) =
      e (G.simplyBlockedChainEquiv R i z) := by
  simp only [simplyBlockedCyclesEquivOfIntertwining, LinearEquiv.ofSubmodules_apply,
    simplyBlockedChainEquivOfIntertwining, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

private theorem map_boundaries_simplyBlockedCyclesEquivOfIntertwining :
    (hG.simplyBlockedBoundaries R i).map
        (hG.simplyBlockedCyclesEquivOfIntertwining R hG' e he).toLinearMap =
      hG'.simplyBlockedBoundaries R j := by
  -- The boundary map is the differential with codomain restricted to cycles, and
  -- `ofSubmodules` restricts the chain equivalence, so after `Subtype.ext` both sides are the
  -- chain-level identity `simplyBlockedChainEquivOfIntertwining_d`.
  ext z
  constructor
  · rintro ⟨w, ⟨c, rfl⟩, rfl⟩
    refine ⟨simplyBlockedChainEquivOfIntertwining R e c, Subtype.ext ?_⟩
    exact simplyBlockedChainEquivOfIntertwining_d R e he c
  · rintro ⟨c, rfl⟩
    refine ⟨hG.simplyBlockedBoundaryMap R i
      ((simplyBlockedChainEquivOfIntertwining R e).symm c), ⟨_, rfl⟩, Subtype.ext ?_⟩
    exact (simplyBlockedChainEquivOfIntertwining_d R e he _).symm.trans
      (congrArg ((G'.simplyBlockedComplex R j).d () ())
        ((simplyBlockedChainEquivOfIntertwining R e).apply_symm_apply c))

/-- **The equivalence of simply blocked homologies induced by an intertwining map.** A
semilinear equivalence `e` of the specialized chain modules blocking `i` and `j`, with
`∂̂' ∘ e = e ∘ ∂̂`, induces a semilinear equivalence `G-hat(G) ≃ G-hat(G')`. -/
def simplyBlockedHomologyEquivOfIntertwining :
    hG.simplyBlockedHomology R i ≃ₛₗ[σ] hG'.simplyBlockedHomology R j :=
  (hG.simplyBlockedHomologyIsoQuotient R i).toLinearEquiv.trans <|
    (Submodule.Quotient.equiv _ _ (hG.simplyBlockedCyclesEquivOfIntertwining R hG' e he)
      (hG.map_boundaries_simplyBlockedCyclesEquivOfIntertwining R hG' e he)).trans
        (hG'.simplyBlockedHomologyIsoQuotient R j).toLinearEquiv.symm

/-- The induced equivalence sends the class of a cycle to the class of its image. -/
@[simp]
theorem simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he
        (G.oneVariableSpecializationHomologyClass R i z) =
      G'.oneVariableSpecializationHomologyClass R j
        (hG.simplyBlockedCyclesEquivOfIntertwining R hG' e he z) := by
  simp only [simplyBlockedHomologyEquivOfIntertwining, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-! ### The bigrading -/

section Bigraded

local notation "H" => hG.toOddComponentGridDiagram
local notation "H'" => GridDiagram.IsKnot.toOddComponentGridDiagram hG'
local notation "Base" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ i} R)
local notation "Base'" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ j} R)

/-- The coefficient action on source homology is the action selected by
`ModuleCat.restrictScalars` along the inclusion of constant polynomials. -/
local instance intertwiningSourceCoefficientModule : Module R (hG.simplyBlockedHomology R i) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
/-- The coefficient action on target homology is the same restricted-scalar action. -/
local instance intertwiningTargetCoefficientModule :
    Module R (hG'.simplyBlockedHomology R j) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)

variable (hσ : ∀ r : R, σ (MvPolynomial.C r) = MvPolynomial.C r)
  (hpiece : ∀ (g : ℤ × ℤ) (c : GridChainHat R n i),
    c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece R i g →
      e c ∈ hG'.toOddComponentGridDiagram.bigradedChainHatPiece R j g)

/-- The induced equivalence, restricted to coefficient scalars. -/
private def simplyBlockedHomologyCoefficientEquivOfIntertwining :
    (Base).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (Base').obj (hG'.simplyBlockedHomology R j) :=
  (hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he).toAddEquiv.toLinearEquiv fun r y => by
    have hy := (hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he).map_smulₛₗ
      (MvPolynomial.C r) y
    rw [hσ] at hy
    exact hy

private theorem simplyBlockedHomologyCoefficientEquivOfIntertwining_apply
    (y : (Base).obj (hG.simplyBlockedHomology R i)) :
    simplyBlockedHomologyCoefficientEquivOfIntertwining hG R hG' e he hσ y =
      hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he y :=
  (rfl)

include hpiece in
/-- If the chain equivalence preserves bidegrees, the induced equivalence sends a homogeneous
class to one of the same bidegree. -/
theorem simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)}
    (hy : y ∈ (H).bigradedHatHomologyPiece R i g) :
    hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he y ∈
      (H').bigradedHatHomologyPiece R j g := by
  obtain ⟨z, hz, rfl⟩ := ((H).mem_bigradedHatHomologyPiece_iff R i).mp hy
  rw [simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass]
  apply (H').oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece
  rw [simplyBlockedChainEquiv_simplyBlockedCyclesEquivOfIntertwining]
  exact hpiece g _ hz

include hpiece in
private theorem simplyBlockedHomologyCoefficientEquivOfIntertwining_homogeneous :
    LinearMap.IsHomogeneous
      (simplyBlockedHomologyCoefficientEquivOfIntertwining hG R hG' e he hσ).toLinearMap
      ((H).bigradedHatHomologyGrading R i).piece
      ((H').bigradedHatHomologyGrading R j).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  simp only [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
  rw [add_zero, LinearEquiv.coe_coe, simplyBlockedHomologyCoefficientEquivOfIntertwining_apply]
  exact hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece R hG' e he
    hpiece hy

include hσ hpiece in
/-- If the chain equivalence fixes the coefficient scalars and preserves bidegrees, the induced
equivalence preserves and reflects the bigrading of `G-hat`. -/
theorem simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he y ∈
        (H').bigradedHatHomologyPiece R j g ↔
      y ∈ (H).bigradedHatHomologyPiece R i g := by
  refine ⟨fun hy => ?_,
    hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece R hG' e he hpiece⟩
  -- The inverse of a degree-preserving equivalence of internally graded modules preserves
  -- degrees, because it preserves the unique homogeneous decompositions.
  have hinv := (simplyBlockedHomologyCoefficientEquivOfIntertwining_homogeneous hG R hG' e he
    hσ hpiece).linearEquiv_symm
  rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece,
    ← simplyBlockedHomologyCoefficientEquivOfIntertwining_apply hG R hG' e he hσ] at hy
  have hm := hinv.map_mem hy
  rwa [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at hm

/-- The restriction of the induced equivalence to a homogeneous piece, as a coefficient-linear
equivalence of homogeneous pieces. -/
def simplyBlockedHomologyPieceEquivOfIntertwining (g : ℤ × ℤ) :
    (H).bigradedHatHomologyPiece R i g ≃ₗ[R] (H').bigradedHatHomologyPiece R j g :=
  (simplyBlockedHomologyCoefficientEquivOfIntertwining hG R hG' e he hσ).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv,
      ← hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff R hG' e he
        hσ hpiece,
      ← simplyBlockedHomologyCoefficientEquivOfIntertwining_apply hG R hG' e he hσ,
      LinearEquiv.apply_symm_apply]
    -- The two sides differ only in which presentation of the coefficient action is used.
    rfl)

/-- On underlying classes, the equivalence of homogeneous pieces is the induced equivalence. -/
@[simp]
theorem coe_simplyBlockedHomologyPieceEquivOfIntertwining (g : ℤ × ℤ)
    (y : (H).bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyPieceEquivOfIntertwining R hG' e he hσ hpiece g y :
      (Base').obj (hG'.simplyBlockedHomology R j)) =
      hG.simplyBlockedHomologyEquivOfIntertwining R hG' e he
        (y : (Base).obj (hG.simplyBlockedHomology R i)) :=
  (rfl)

end Bigraded

end Ring

/-! ### Poincaré series and Euler characteristic -/

section Field

variable (K : Type*) [Field K] [CharP K 2] (hG' : G'.IsKnot)
  {σ : MvPolynomial {c : Fin n // c ≠ i} K →+* MvPolynomial {c : Fin n // c ≠ j} K}
  {σ' : MvPolynomial {c : Fin n // c ≠ j} K →+* MvPolynomial {c : Fin n // c ≠ i} K}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (e : GridChainHat K n i ≃ₛₗ[σ] GridChainHat K n j)
  (he : ∀ c, G'.simplyBlockedDifferential K j (e c) = e (G.simplyBlockedDifferential K i c))
  (hσ : ∀ r : K, σ (MvPolynomial.C r) = MvPolynomial.C r)
  (hpiece : ∀ (g : ℤ × ℤ) (c : GridChainHat K n i),
    c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece K i g →
      e c ∈ hG'.toOddComponentGridDiagram.bigradedChainHatPiece K j g)

include he hσ hpiece

/-- A chain equivalence that intertwines the simply blocked differentials, fixes the coefficient
scalars and preserves bidegrees identifies the bigraded Poincaré series of `G-hat`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining :
    hG'.bigradedSimplyBlockedHomologyPoincareSeries K j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyPieceEquivOfIntertwining K hG' e he hσ hpiece g).finrank_eq.symm

/-- A chain equivalence that intertwines the simply blocked differentials, fixes the coefficient
scalars and preserves bidegrees identifies the Alexander-graded Euler characteristic of
`G-hat`. -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_of_intertwining :
    hG'.gradedSimplyBlockedHomologyEulerChar K j = hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining K hG' e he hσ hpiece]

end Field

end TauCeti.GridDiagram.IsKnot
