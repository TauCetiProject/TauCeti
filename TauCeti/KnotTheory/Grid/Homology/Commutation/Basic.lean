/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.Assembly
public import TauCeti.KnotTheory.Grid.Commutation.Grading.Map
public import TauCeti.KnotTheory.Grid.Homology.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander

/-!
# The pentagon map on unblocked grid homology

The pentagon-counting map of a column turn (`GridDiagram.ColumnTurn`) intertwines the unblocked
differentials. It therefore induces a specified map on `GH⁻`, sending the class of a cycle
to the class of its pentagon image. The map is semilinear along the transposition of the
two coefficient variables. Over any commutative ring of characteristic two, for diagrams with an
odd number of link components it raises the Maslov--Alexander bigrading by the bidegree
`GridDiagram.commutationBidegree` of the turn, which vanishes for a column commutation. For knot
grids it is linear over `R[U]` and homogeneous for the Alexander grading
(`GridDiagram.IsKnot.isHomogeneous_unblockedHomologyCommutationLinearMap`).

The construction uses the concrete cycle quotient through `unblockedHomologyIso` and
Mathlib's `Submodule.mapQ`. It supplies the homology map itself; invertibility requires
the hexagon homotopy identities.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) (C : ColumnTurn n)

local notation "G'" => G.swapColumns C.column (finRotate n C.column)

section Cycles

variable [CommSemiring R] [CharP R 2]

/-- The pentagon map of a column turn sends cycles to cycles. -/
theorem commutationMap_mem_ker_unblockedDifferential {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    G.commutationMap R C z ∈ LinearMap.ker ((G').unblockedDifferential R) := by
  have h := LinearMap.congr_fun (G.commutationMap_comp_unblockedDifferential C R) z
  rw [LinearMap.mem_ker]
  simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp hz, map_zero] using h.symm

/-- Restriction of the pentagon map to cycles. -/
private noncomputable def commutationCyclesMap :
    LinearMap.ker (G.unblockedDifferential R) →ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)]
      LinearMap.ker ((G').unblockedDifferential R) :=
  (G.commutationMap R C).restrict fun _ hz =>
    G.commutationMap_mem_ker_unblockedDifferential R C hz

@[simp]
private theorem coe_commutationCyclesMap (z : LinearMap.ker (G.unblockedDifferential R)) :
    (G.commutationCyclesMap R C z : GridChainMinus R n) = G.commutationMap R C z :=
  LinearMap.coe_restrict_apply _ _

/-- The pentagon map on cycles takes boundaries to boundaries. -/
private theorem commutationCyclesMap_mem_boundariesInKer
    {z : LinearMap.ker (G.unblockedDifferential R)}
    (hz : z ∈ (G.unblockedDifferential R).boundariesInKer) :
    G.commutationCyclesMap R C z ∈ ((G').unblockedDifferential R).boundariesInKer := by
  obtain ⟨w, hw⟩ := (LinearMap.mem_boundariesInKer _).mp hz
  apply (LinearMap.mem_boundariesInKer _).mpr
  refine ⟨G.commutationMap R C w, ?_⟩
  have h := LinearMap.congr_fun (G.commutationMap_comp_unblockedDifferential C R) w
  simpa only [LinearMap.comp_apply, hw, coe_commutationCyclesMap] using h.symm

end Cycles

variable [CommRing R] [CharP R 2]

private noncomputable def commutationQuotientMap :
    (G.unblockedDifferential R).homology (G.unblockedDifferential_comp_self_eq_zero R)
      →ₛₗ[((renameEquiv R (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
        MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)]
      ((G').unblockedDifferential R).homology
        ((G').unblockedDifferential_comp_self_eq_zero R) := by
  apply Submodule.mapQ _ _ (G.commutationCyclesMap R C)
  intro z hz
  exact G.commutationCyclesMap_mem_boundariesInKer R C hz

/-- The specified map on unblocked grid homology induced by the pentagon map of a column turn,
for instance that of a column commutation. It is semilinear along the renaming that exchanges the
two variables of the exchanged columns. -/
noncomputable def unblockedHomologyCommutationMap :
    G.unblockedHomology R →ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] (G').unblockedHomology R :=
  ((G').unblockedHomologyIso R).toLinearEquiv.symm.toLinearMap.comp
    ((G.commutationQuotientMap R C).comp (G.unblockedHomologyIso R).toLinearEquiv.toLinearMap)

/-- The commutation map sends a cycle class to the class of its pentagon image. -/
@[simp]
theorem unblockedHomologyCommutationMap_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyCommutationMap R C (G.unblockedHomologyClass R z) =
      (G').unblockedHomologyClass R
        ⟨G.commutationMap R C z, G.commutationMap_mem_ker_unblockedDifferential R C z.2⟩ := by
  simp only [unblockedHomologyCommutationMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq]
  simp only [CategoryTheory.Iso.toLinearEquiv_apply (G.unblockedHomologyIso R),
    CategoryTheory.Iso.toLinearEquiv_apply ((G').unblockedHomologyIso R),
    G.unblockedHomologyIso_hom_unblockedHomologyClass R,
    (G').unblockedHomologyIso_hom_unblockedHomologyClass R, commutationQuotientMap,
    LinearMap.homologyπ_apply, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (G.coe_commutationCyclesMap R C z))

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

section Turn

variable (C : GridDiagram.ColumnTurn n)

/-- The commutation map of a column turn `C` on `GH⁻` raises the full Maslov--Alexander bidegree
by `G.commutationBidegree C`. -/
theorem unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece_add
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    G.1.unblockedHomologyCommutationMap R C y ∈
      (G.swapColumns C).bigradedUnblockedHomologyPiece R (g + G.1.commutationBidegree C) := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [GridDiagram.unblockedHomologyCommutationMap_unblockedHomologyClass]
  apply unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece
  exact G.commutationMap_mem_bigradedChainMinusPiece_add R C hz

/-- The commutation map of a column turn `C` on `GH⁻` raises the Alexander grading by the
Alexander component of `G.commutationBidegree C`. -/
theorem unblockedHomologyCommutationMap_mem_alexanderUnblockedHomologyGrading_piece_add
    {a : ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ (G.alexanderUnblockedHomologyGrading R).piece a) :
    G.1.unblockedHomologyCommutationMap R C y ∈
      ((G.swapColumns C).alexanderUnblockedHomologyGrading R).piece
        (a + (G.1.commutationBidegree C).2) := by
  rw [G.mem_alexanderUnblockedHomologyGrading_piece_iff R,
    G.mem_alexanderHomologyGrading_piece_iff] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain rfl : y = G.1.unblockedHomologyClass R z := by
    apply (ModuleCat.mono_iff_injective (G.1.unblockedHomologyIso R).hom).mp inferInstance
    rw [GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass, hzy]
  rw [GridDiagram.unblockedHomologyCommutationMap_unblockedHomologyClass,
    (G.swapColumns C).mem_alexanderUnblockedHomologyGrading_piece_iff R,
    (G.swapColumns C).mem_alexanderHomologyGrading_piece_iff]
  exact ⟨_, G.commutationMap_mem_alexanderChainMinusPiece_add R C hz,
    (GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass ..).symm⟩

end Turn

variable (C : GridDiagram.ColumnCommutationData G.1)

/-- The commutation map on `GH⁻` preserves the full Maslov--Alexander bigrading. -/
theorem unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    G.1.unblockedHomologyCommutationMap R C y ∈
      bigradedUnblockedHomologyPiece
        ⟨G.1.swapColumns C.column (finRotate n C.column),
          C.isColumnCommutation.componentCount_eq.symm ▸ G.2⟩ R g := by
  simpa using G.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece_add R C hy

/-- The commutation map on `GH⁻` preserves the Alexander grading. -/
theorem unblockedHomologyCommutationMap_mem_alexanderUnblockedHomologyGrading_piece
    {a : ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ (G.alexanderUnblockedHomologyGrading R).piece a) :
    G.1.unblockedHomologyCommutationMap R C y ∈
      (alexanderUnblockedHomologyGrading
        ⟨G.1.swapColumns C.column (finRotate n C.column),
          C.isColumnCommutation.componentCount_eq.symm ▸ G.2⟩ R).piece a := by
  simpa using
    G.unblockedHomologyCommutationMap_mem_alexanderUnblockedHomologyGrading_piece_add R C hy

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2]
  (C : ColumnTurn n)

/-- For a knot grid, the specified commutation map of a column turn is linear over `R[U]`, since
renaming the grid variables commutes with their common specialization to `U`. -/
noncomputable def unblockedHomologyCommutationLinearMap :
    letI := hG.unblockedHomologyModule R
    letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
    G.unblockedHomology R →ₗ[Polynomial R]
      (G.swapColumns C.column (finRotate n C.column)).unblockedHomology R := by
  letI := hG.unblockedHomologyModule R
  letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  exact
    { toFun := G.unblockedHomologyCommutationMap R C
      map_add' := map_add _
      map_smul' := fun q y => by
        obtain ⟨p, rfl⟩ := aeval_const_X_surjective (Fin n) R q
        rw [hG.aeval_smul_unblockedHomology, LinearMap.map_smulₛₗ,
          ← (hG.swapColumns C.column (finRotate n C.column)).aeval_smul_unblockedHomology]
        simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, renameEquiv_apply,
          aeval_rename, Function.comp_def, RingHom.id_apply] }

/-- The `R[U]`-linear map acts by the specified semilinear commutation map. -/
@[simp]
theorem unblockedHomologyCommutationLinearMap_apply (y : G.unblockedHomology R) :
    hG.unblockedHomologyCommutationLinearMap R C y =
      G.unblockedHomologyCommutationMap R C y := (rfl)

open OddComponentGridDiagram in
/-- For a knot grid, the `R[U]`-linear commutation map of a column turn `C` is homogeneous for the
Alexander gradings, of degree the Alexander component of `G.commutationBidegree C`. -/
theorem isHomogeneous_unblockedHomologyCommutationLinearMap :
    letI := hG.unblockedHomologyModule R
    letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
    LinearMap.IsHomogeneous (hG.unblockedHomologyCommutationLinearMap R C)
      (hG.alexanderUnblockedHomologyGrading R).piece
      ((hG.swapColumns C.column (finRotate n C.column)).alexanderUnblockedHomologyGrading R).piece
      (G.commutationBidegree C).2 := by
  let _ := hG.unblockedHomologyModule R
  let _ := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
  refine LinearMap.isHomogeneous_def.mpr fun a y hy => ?_
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
  exact unblockedHomologyCommutationMap_mem_alexanderUnblockedHomologyGrading_piece_add _ R C hy

end GridDiagram.IsKnot

end TauCeti
