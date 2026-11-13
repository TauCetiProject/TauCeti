/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SimplyBlocked.Map
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# North-east stabilization of one-variable-specialization homology

The north-east corner `X`-stabilization inserts a column after the split column `s` and a row
after its `X`-marking. The old `O`-marking of column `i` then lies in column
`s.succ.succAbove i`. Blocking that marking gives one-variable-specialization homology in the
same absolute `(O-Maslov, Alexander)` bidegrees as the original diagram whenever its component
count is odd. For knots this specialization is simply blocked homology.

This file specializes the existing unblocked north-east comparison to a semilinear map over
the surviving polynomial variables. It descends to a bijective semilinear homology map and,
after restricting scalars, a coefficient-linear equivalence on total homology and every
homogeneous piece. The cycle-class and chain-evaluation equations hide all carrier transport.
The underlying unblocked comparison conjugates the south-west comparison by half-turns,
retaining the grading normalization and blocked marking. For knots over a field of
characteristic two, the bigraded Poincaré series and Alexander-graded Euler characteristic
are unchanged.

The specialization construction and exact-sequence argument are shared with the south-west
comparison through `SimplyBlocked/Map.lean`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open CategoryTheory

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (s i : Fin n) (R : Type*)

section Semiring

variable [CommSemiring R]

local notation "j" => s.succ.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The coefficient homomorphism of stabilization after blocking the transported old marking.
Merge the stabilization columns using `s.predAbove`, then kill the variable of column `i`. -/
noncomputable def simplyBlockedStabilizeXSuccRingHom : S →+* A :=
  simplyBlockedRingHomAlong R s.predAbove i j

/-- A surviving source variable is merged and then specialized in the old grid. In particular,
when `i = s`, the other variable of the stabilization block also maps to zero. -/
@[simp]
theorem simplyBlockedStabilizeXSuccRingHom_X (c : {c : Fin (n + 1) // c ≠ j}) :
    simplyBlockedStabilizeXSuccRingHom s i R (MvPolynomial.X c) =
      simplyBlockedRingHom R i (MvPolynomial.X (s.predAbove c)) := by
  simp [simplyBlockedStabilizeXSuccRingHom]

/-- Stabilization leaves ground-ring coefficients unchanged after blocking. -/
@[simp]
theorem simplyBlockedStabilizeXSuccRingHom_C (r : R) :
    simplyBlockedStabilizeXSuccRingHom s i R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [simplyBlockedStabilizeXSuccRingHom]

/-- Merging columns commutes with blocking the transported old marking. -/
theorem simplyBlockedStabilizeXSuccRingHom_specialization (p : MvPolynomial (Fin (n + 1)) R) :
    simplyBlockedStabilizeXSuccRingHom s i R (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename s.predAbove p) :=
  simplyBlockedRingHomAlong_specialization R s.predAbove i j
    (by simp [Fin.predAbove_succ_succAbove]) p

end Semiring

variable (G : GridDiagram n) [CommRing R]

local notation "j" => s.succ.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The stabilization comparison with the transported old `O`-marking blocked. Its image on a
generator is the specialization of the unblocked stabilization comparison. -/
noncomputable def simplyBlockedStabilizeXSuccMap :
    GridChainHat R (n + 1) j →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      GridChainHat R n i :=
  simplyBlockedMapAlong R s.predAbove i j (G.stabilizeXSuccChainMap s R)

/-- The specialized stabilization map on a single supported coefficient. -/
theorem simplyBlockedStabilizeXSuccMap_single (x : GridState (n + 1)) (p : S) :
    G.simplyBlockedStabilizeXSuccMap s i R (Finsupp.single x p) =
      simplyBlockedStabilizeXSuccRingHom s i R p •
        simplyBlockedSpecialization R i (G.stabilizeXSuccChainMap s R (Finsupp.single x 1)) :=
  simplyBlockedMapAlong_single R s.predAbove i j (G.stabilizeXSuccChainMap s R) x p

/-- The matrix formula for the specialized stabilization comparison. -/
@[simp]
theorem simplyBlockedStabilizeXSuccMap_apply_apply (c : GridChainHat R (n + 1) j)
    (y : GridState n) :
    G.simplyBlockedStabilizeXSuccMap s i R c y = c.sum fun x p =>
      simplyBlockedStabilizeXSuccRingHom s i R p *
        simplyBlockedRingHom R i (G.stabilizeXSuccChainMap s R (Finsupp.single x 1) y) :=
  simplyBlockedMapAlong_apply_apply R s.predAbove i j (G.stabilizeXSuccChainMap s R) c y

/-- The simply blocked comparison is the descent of the unblocked stabilization map through
coefficient specialization. -/
@[simp↓]
theorem simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization (c : GridChainMinus R (n + 1)) :
    G.simplyBlockedStabilizeXSuccMap s i R (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (G.stabilizeXSuccChainMap s R c) :=
  simplyBlockedMapAlong_specialization R s.predAbove i j (G.stabilizeXSuccChainMap s R)
    (by simp [Fin.predAbove_succ_succAbove]) c

variable [CharP R 2]

/-- Stabilization commutes with the simply blocked differentials. -/
theorem simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential (c : GridChainHat R (n + 1) j) :
    G.simplyBlockedStabilizeXSuccMap s i R
        ((G.stabilizeX s.succ (G.X s).succ s).simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (G.simplyBlockedStabilizeXSuccMap s i R c) :=
  simplyBlockedMapAlong_differential R s.predAbove i j (G.stabilizeXSuccChainMap s R) G _
    (by simp [Fin.predAbove_succ_succAbove]) (G.stabilizeXSuccChainMap_unblockedDifferential s R) c

/-! ### Quasi-isomorphism after blocking -/

local notation "G'" => GridDiagram.stabilizeX G (Fin.succ s)
  (Fin.succ (GridDiagram.X G s)) s

/-- Every simply blocked cycle of `G` differs from the image of a simply blocked cycle of the
stabilized diagram by a boundary. -/
private theorem exists_sub_simplyBlockedStabilizeXSuccMap_mem_range {y : GridChainHat R n i}
    (hy : y ∈ LinearMap.ker (G.simplyBlockedDifferential R i)) :
    ∃ x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j),
      y - G.simplyBlockedStabilizeXSuccMap s i R x ∈
        LinearMap.range (G.simplyBlockedDifferential R i) :=
  exists_sub_simplyBlockedMapAlong_mem_range R s.predAbove i j
    (G.stabilizeXSuccChainMap s R) G _ (by simp [Fin.predAbove_succ_succAbove])
    (G.stabilizeXSuccChainMap_unblockedDifferential s R)
    (fun _ hc => G.exists_sub_stabilizeXSuccChainMap_mem_range s R hc)
    (fun _ hx h => G.mem_range_of_stabilizeXSuccChainMap_mem_range s R hx h) hy

/-- A simply blocked cycle of the stabilized diagram whose image in `G` is a boundary is itself a
boundary. -/
private theorem mem_range_of_simplyBlockedStabilizeXSuccMap_mem_range {x : GridChainHat R (n + 1) j}
    (hx : x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j))
    (h : G.simplyBlockedStabilizeXSuccMap s i R x ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    x ∈ LinearMap.range ((G').simplyBlockedDifferential R j) :=
  mem_range_of_simplyBlockedMapAlong_mem_range R s.predAbove i j
    (G.stabilizeXSuccChainMap s R) G _ (by simp [Fin.predAbove_succ_succAbove])
    (G.stabilizeXSuccChainMap_unblockedDifferential s R)
    (fun _ hc => G.exists_sub_stabilizeXSuccChainMap_mem_range s R hc)
    (fun _ hx h => G.mem_range_of_stabilizeXSuccChainMap_mem_range s R hx h) hx h

end TauCeti.GridDiagram

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "G'" => GridDiagram.stabilizeX G (Fin.succ s)
  (Fin.succ (GridDiagram.X G s)) s
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- Stabilization on cycles of the one-variable specialization, with the chosen old `O`-marking
blocked in each diagram. -/
noncomputable def oneVariableSpecializationStabilizeXSuccCyclesMap :
    LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom
      →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
  oneVariableSpecializationCyclesMapOfIntertwining R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R)

/-- Under the explicit chain identifications, the map on cycles of the one-variable specialization
is `simplyBlockedStabilizeXSuccMap`. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.simplyBlockedChainEquiv R i (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) =
      G.simplyBlockedStabilizeXSuccMap s i R ((G').simplyBlockedChainEquiv R j z) :=
  simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R) z

/-- The specified semilinear stabilization comparison on the homology of the one-variable
specialization, from the stabilized grid to the original grid. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyMap :
    ((G').simplyBlockedComplex R j).homology () →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      (G.simplyBlockedComplex R i).homology () :=
  oneVariableSpecializationHomologyMapOfIntertwining
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R)

/-- The stabilization comparison on the one-variable specialization sends a cycle class to the class
of its stabilization image. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R
        ((G').oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) :=
  oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R) z

/-- **Stabilization invariance for the one-variable specialization.** For any grid diagram `G`, the
stabilization map from the homology of the specialization `V_{s.succ.succAbove i} = 0` of `G'`
to the homology of the specialization `V_i = 0` of `G` is bijective. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R) := by
  apply oneVariableSpecializationHomologyMapOfIntertwining_bijective
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R)
  · intro x hx hfx
    exact G.mem_range_of_simplyBlockedStabilizeXSuccMap_mem_range s i R hx hfx
  · intro y hy
    exact G.exists_sub_simplyBlockedStabilizeXSuccMap_mem_range s i R hy

/-- The stabilization comparison on the homology of the one-variable specialization, packaged as an
`R`-linear equivalence by restricting scalars along `MvPolynomial.C`. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
        (((G').simplyBlockedComplex R j).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
        ((G.simplyBlockedComplex R i).homology ()) :=
  oneVariableSpecializationHomologyLinearEquivOfIntertwining
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R)
    (simplyBlockedStabilizeXSuccRingHom_C s i R)
    (G.oneVariableSpecializationStabilizeXSuccHomologyMap_bijective s i R)

/-- On elements, the coefficient-linear equivalence is the semilinear stabilization map. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_apply
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
      (((G').simplyBlockedComplex R j).homology ())) :
    G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y =
      G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R y :=
  oneVariableSpecializationHomologyLinearEquivOfIntertwining_apply
    R j i (simplyBlockedStabilizeXSuccRingHom s i R)
    (G.simplyBlockedStabilizeXSuccMap s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R)
    (simplyBlockedStabilizeXSuccRingHom_C s i R)
    (G.oneVariableSpecializationStabilizeXSuccHomologyMap_bijective s i R) y

/-- The total north-east comparison sends a cycle class to the class of its cycle image. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R
        ((G').oneVariableSpecializationHomologyClass R j z) :
          (G.simplyBlockedComplex R i).homology ()) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) :=
  (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv_apply s i R
    ((G').oneVariableSpecializationHomologyClass R j z)).trans
      (G.oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass
        s i R z)

/-- The inverse total comparison recovers a cycle class from the class of its north-east image. -/
theorem
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_homologyClass_cyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    ((G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm
        (G.oneVariableSpecializationHomologyClass R i
          (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z)) :
              ((G').simplyBlockedComplex R j).homology ()) =
      (G').oneVariableSpecializationHomologyClass R j z := by
  rw [←
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
      G s i R z]
  exact (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm_apply_apply _

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

omit [CharP R 2] in
/-- The specialized north-east chain comparison preserves absolute bidegrees. -/
theorem simplyBlockedStabilizeXSuccMap_mem_bigradedChainHatPiece {g : ℤ × ℤ}
    {c : GridChainHat R (n + 1) j}
    (hc : c ∈ (G.stabilizeXSucc s).bigradedChainHatPiece R j g) :
    G.1.simplyBlockedStabilizeXSuccMap s i R c ∈ G.bigradedChainHatPiece R i g := by
  obtain ⟨b, hb, rfl⟩ := (G.stabilizeXSucc s).mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [GridDiagram.simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.stabilizeXSuccChainMap_mem_bigradedChainMinusPiece s R hb)

/-- The north-east total homology comparison is homogeneous of bidegree zero. -/
theorem isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).toLinearMap
      ((G.stabilizeXSucc s).bigradedHatHomologyGrading R j).piece
      (G.bigradedHatHomologyGrading R i).piece 0 := by
  refine (G.stabilizeXSucc s).isHomogeneous_oneVariableSpecializationHomologyMap R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).toLinearMap
    (G.1.oneVariableSpecializationStabilizeXSuccCyclesMap s i R) ?_ ?_
  · intro z
    exact
      oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
        G.1 s i R z
  · intro g z hz
    rw [GridDiagram.simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap]
    exact G.simplyBlockedStabilizeXSuccMap_mem_bigradedChainHatPiece s i R hz

/-- The north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ)
    (y : (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) :
    G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g := by
  exact (G.stabilizeXSucc s).bigradedHatHomologyEquiv_mem_piece_iff R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- The inverse north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y ∈
        (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  exact (G.stabilizeXSucc s).bigradedHatHomologyEquiv_symm_mem_piece_iff R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- North-east `X`-stabilization identifies each homogeneous piece, blocking the transported old
`O`-marking and preserving absolute `O`-Maslov and Alexander bidegrees. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ≃ₗ[R]
      G.bigradedHatHomologyPiece R i g :=
  (G.stabilizeXSucc s).bigradedHatHomologyPieceEquiv R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g

/-- The piece comparison is the restriction of the total homology comparison. -/
@[simp↓]
theorem coe_oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) :
    (G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y := by
  exact (G.stabilizeXSucc s).coe_bigradedHatHomologyPieceEquiv_apply R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- The inverse piece comparison is the restriction of the inverse total comparison. -/
@[simp↓]
theorem coe_oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    ((G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g).symm y :
        (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) =
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y := by
  exact (G.stabilizeXSucc s).coe_bigradedHatHomologyPieceEquiv_symm_apply R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- North-east `X`-stabilization preserves the coefficient-ring rank in every bidegree. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeXSucc (g : ℤ × ℤ) :
    Module.finrank R ((G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) =
      Module.finrank R (G.bigradedHatHomologyPiece R i g) :=
  (G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g).finrank_eq

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (K : Type*) [Field K] [CharP K 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.succ s) (Fin.succ (GridDiagram.X G s)) s) hG

/-- North-east corner `X`-stabilization preserves the bigraded Poincaré series of simply
blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  have hstab : (hG').toOddComponentGridDiagram = hG.toOddComponentGridDiagram.stabilizeXSucc s :=
    Subtype.ext rfl
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries, hstab]
  exact hG.toOddComponentGridDiagram.finrank_bigradedHatHomologyPiece_stabilizeXSucc s i K g

/-- North-east corner `X`-stabilization preserves the Alexander-graded Euler characteristic of
simply blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeX_succ :
    (hG').gradedSimplyBlockedHomologyEulerChar K j =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ s i K]

end TauCeti.GridDiagram.IsKnot
