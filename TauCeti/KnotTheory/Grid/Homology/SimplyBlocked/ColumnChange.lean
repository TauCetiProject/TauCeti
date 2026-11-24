/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
public import TauCeti.KnotTheory.Grid.XHomotopy.Grading
import TauCeti.Algebra.Homology.SquareZero.Quotient

/-!
# Simply blocked grid homology does not depend on the blocked `O`-marking

Simply blocked grid homology `G-hat` is the homology of the unblocked grid complex `GC⁻` with one
variable `V_i` set to zero. For a knot grid it does not depend on the choice of the blocked column
`i`: this file constructs, for any two columns `i` and `j`, an isomorphism between the homologies
of the two specializations which preserves the (`O`-Maslov, Alexander) bigrading, so the bigraded
Poincaré series and the Alexander-graded Euler characteristic of `G-hat` are independent of `i`.

Write `π_i` for specialization at `V_i = 0`. It is surjective, it intertwines the differentials,
and it kills exactly the multiples of `V_i`, on which `V_i` acts injectively. So the specialization
at `V_i = 0` is the quotient of `GC⁻` by the injective chain map `V_i`. Given a map `H` on `GC⁻`
with `∂⁻ H + H ∂⁻ = V_i + V_j`, in characteristic two the chain maps `V_i` and `V_j` are
homotopic, and the comparison of quotients by homotopic injective chain maps
(`LinearMap.homologyEquivOfHomotopicInjective`), transported along the identifications of
`TauCeti.GridDiagram.oneVariableSpecializationHomologyEquivLinearMapHomology`, gives a
coefficient-linear equivalence of the homologies of the two specializations
(`GridDiagram.oneVariableSpecializationHomologyEquivOfHomotopy`). If `V_i • a + ∂⁻ b = 0`, it
sends the class of `π_i b` to the class of `π_j (H a + b)`; its inverse acts in the same way with
`i` and `j` exchanged. No knot hypothesis is needed for this part: two columns on the same
component of a link are related by such a homotopy as well.

On a knot grid the variables of all columns are homotopic through the `X`-marking homotopies
(`GridDiagram.IsKnot.XSmulHomotopy`), which have bidegree `(-1, -1)`. With this homotopy the
equivalence preserves bidegrees, giving the degree-zero equivalence
`GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv` of the bigraded simply blocked
homologies for the blocked columns `i` and `j`.

## Main definitions

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyEquivOfHomotopy`: the equivalence of the
  homologies of the specializations at `V_i = 0` and at `V_j = 0` induced by a homotopy between
  `V_i` and `V_j`.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv`: for a knot grid, the
  coefficient-linear equivalence of simply blocked homologies blocking the columns `i` and `j`.

## Main results

* `GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv_mem_bigradedHatHomologyPiece_iff`:
  for a knot grid it preserves and reflects both homology degrees.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_columnChange` and
  `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_columnChange`: over a field of
  characteristic two, the bigraded Poincaré series and the Alexander-graded Euler characteristic of
  `G-hat` do not depend on the blocked column.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6: simply blocked grid
  homology, defined by blocking one `O`-marking, and the `X`-marking homotopies of Lemma 4.6.9.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Geom. Topol. 11
  (2007), Section 2 (arXiv:math/0610559).
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### Changing the blocked column along a homotopy -/

section Homotopy

variable (R : Type*) [CommRing R]

local notation "Base" k => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ k} R)

/-- Multiplication by `V_k` commutes with `∂⁻`, over the ground ring. -/
private theorem X_smul_comp_unblockedDifferential (k : Fin n) :
    DistribSMul.toLinearMap R (GridChainMinus R n) (MvPolynomial.X k : MvPolynomial (Fin n) R)
        ∘ₗ (G.unblockedDifferential R).restrictScalars R =
      (G.unblockedDifferential R).restrictScalars R ∘ₗ
        DistribSMul.toLinearMap R (GridChainMinus R n)
          (MvPolynomial.X k : MvPolynomial (Fin n) R) :=
  LinearMap.ext fun c => (LinearMap.map_smul (G.unblockedDifferential R) _ c).symm

variable [CharP R 2] {i j : Fin n}
  {H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n}
  (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
    (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)

include hH in
/-- In characteristic two, a homotopy between `V_i` and `V_j` over the ground ring. -/
private theorem restrictScalars_homotopy :
    (G.unblockedDifferential R).restrictScalars R ∘ₗ H.restrictScalars R +
        H.restrictScalars R ∘ₗ (G.unblockedDifferential R).restrictScalars R =
      DistribSMul.toLinearMap R (GridChainMinus R n) (MvPolynomial.X i : MvPolynomial (Fin n) R) -
        DistribSMul.toLinearMap R (GridChainMinus R n)
          (MvPolynomial.X j : MvPolynomial (Fin n) R) := by
  refine LinearMap.ext fun c => ?_
  have h := LinearMap.congr_fun hH c
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [LinearMap.sub_apply, DistribSMul.toLinearMap_apply, DistribSMul.toLinearMap_apply,
    ← sub_smul, CharTwo.sub_eq_add, ← h]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]

include hH in
/-- **Changing the blocked column.** Given a map `H` on `GC⁻` with `∂⁻ H + H ∂⁻ = V_i + V_j` in
characteristic two, the coefficient-linear equivalence between the homologies of the
specializations at `V_i = 0` and at `V_j = 0` comparing the quotients of `GC⁻` by the homotopic
injective chain maps `V_i` and `V_j` (`LinearMap.homologyEquivOfHomotopicInjective`). -/
noncomputable def oneVariableSpecializationHomologyEquivOfHomotopy :
    (Base i).obj ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (Base j).obj ((G.simplyBlockedComplex R j).homology ()) :=
  (G.oneVariableSpecializationHomologyEquivLinearMapHomology R i).trans <|
    (LinearMap.homologyEquivOfHomotopicInjective
      (G.restrictScalars_unblockedDifferential_comp_self_eq_zero R)
      (G.restrictScalars_unblockedDifferential_comp_self_eq_zero R)
      (G.restrictScalars_simplyBlockedDifferential_comp_self_eq_zero R i)
      (G.restrictScalars_simplyBlockedDifferential_comp_self_eq_zero R j)
      (G.X_smul_comp_unblockedDifferential R i) (G.X_smul_comp_unblockedDifferential R j)
      (X_smul_gridChainMinus_injective R i) (X_smul_gridChainMinus_injective R j)
      (G.restrictScalars_homotopy R hH)
      (simplyBlockedSpecializationLinearMap_surjective R i)
      (simplyBlockedSpecializationLinearMap_surjective R j)
      (exact_X_smul_simplyBlockedSpecializationLinearMap R i)
      (exact_X_smul_simplyBlockedSpecializationLinearMap R j)
      (G.simplyBlockedSpecializationLinearMap_comp_unblockedDifferential R i)
      (G.simplyBlockedSpecializationLinearMap_comp_unblockedDifferential R j)).trans
      (G.oneVariableSpecializationHomologyEquivLinearMapHomology R j).symm

include hH in
/-- If `V_i • a + ∂⁻ b = 0` and `∂⁻ H + H ∂⁻ = V_i + V_j` in characteristic two, then
`π_j (H a + b)` is a cycle of the specialization at `V_j = 0`. -/
theorem simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero
    {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0) :
    G.simplyBlockedDifferential R j (simplyBlockedSpecialization R j (H a + b)) = 0 := by
  simpa only [LinearMap.mem_ker, LinearMap.restrictScalars_apply,
    simplyBlockedSpecializationLinearMap_apply] using
    LinearMap.map_add_mem_ker_of_homotopy
      (G.restrictScalars_unblockedDifferential_comp_self_eq_zero R)
      (G.X_smul_comp_unblockedDifferential R i) (X_smul_gridChainMinus_injective R i)
      (G.restrictScalars_homotopy R hH)
      (exact_X_smul_simplyBlockedSpecializationLinearMap R j)
      (G.simplyBlockedSpecializationLinearMap_comp_unblockedDifferential R j) hab

/-- If `V_i • a + ∂⁻ b = 0` and `π_i b` is the cycle `z`, the change of blocked column sends the
class of `z` to the class of `π_j (H a + b)`. -/
theorem oneVariableSpecializationHomologyEquivOfHomotopy_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0)
    (hb : simplyBlockedSpecialization R i b = G.simplyBlockedChainEquiv R i z) :
    G.oneVariableSpecializationHomologyEquivOfHomotopy R hH
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.oneVariableSpecializationHomologyClass R j
        ⟨(G.simplyBlockedChainEquiv R j).symm (simplyBlockedSpecialization R j (H a + b)), by
          rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
          exact G.simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero R hH hab⟩ := by
  refine (LinearEquiv.trans_apply ..).trans ?_
  rw [
    oneVariableSpecializationHomologyEquivLinearMapHomology_oneVariableSpecializationHomologyClass,
    LinearEquiv.trans_apply]
  rw [← simplyBlockedSpecializationLinearMap_apply] at hb
  have hz : simplyBlockedSpecializationLinearMap R i b ∈
      LinearMap.ker ((G.simplyBlockedDifferential R i).restrictScalars R) := by
    rw [hb, LinearMap.mem_ker, LinearMap.restrictScalars_apply]
    exact (G.mem_ker_simplyBlockedComplex_d_iff R i z).mp z.property
  -- `hab` with both maps written as the linear maps the general comparison is stated for.
  have hab' : DistribSMul.toLinearMap R (GridChainMinus R n)
      (MvPolynomial.X i : MvPolynomial (Fin n) R) a +
        (G.unblockedDifferential R).restrictScalars R b = 0 := hab
  rw [show (⟨G.simplyBlockedChainEquiv R i z, _⟩ :
      LinearMap.ker ((G.simplyBlockedDifferential R i).restrictScalars R)) = ⟨_, hz⟩ from
        Subtype.ext hb.symm,
    LinearMap.homologyEquivOfHomotopicInjective_mk _ _ _ _ _ _
      (X_smul_gridChainMinus_injective R i) (X_smul_gridChainMinus_injective R j) _ _ _ _ _ _ _
      hab' hz,
    oneVariableSpecializationHomologyEquivLinearMapHomology_symm_mk]
  exact congrArg (G.oneVariableSpecializationHomologyClass R j)
    (Subtype.ext (congrArg (G.simplyBlockedChainEquiv R j).symm
      (simplyBlockedSpecializationLinearMap_apply R j _)))

/-- If `V_j • a + ∂⁻ b = 0` and `π_j b` is the cycle `z`, the inverse of the change of blocked
column sends the class of `z` to the class of `π_i (H a + b)`. -/
theorem oneVariableSpecializationHomologyEquivOfHomotopy_symm_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.simplyBlockedComplex R j).d () ()).hom) {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X j : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0)
    (hb : simplyBlockedSpecialization R j b = G.simplyBlockedChainEquiv R j z) :
    (G.oneVariableSpecializationHomologyEquivOfHomotopy R hH).symm
        (G.oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        ⟨(G.simplyBlockedChainEquiv R i).symm (simplyBlockedSpecialization R i (H a + b)), by
          rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
          exact G.simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero R
            (hH.trans (by rw [add_comm])) hab⟩ := by
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  -- `V_j a` is a boundary, so `a` is a cycle and `∂⁻ (H a + b) = V_i a`.
  have ha : G.unblockedDifferential R a = 0 :=
    G.unblockedDifferential_eq_zero_of_eq_X_smul R (c := -b)
      ((map_neg _ b).trans (eq_neg_of_add_eq_zero_left hab).symm)
  have hab' : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a +
      G.unblockedDifferential R (H a + b) = 0 := by
    have h := LinearMap.congr_fun hH a
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, ha, map_zero, add_zero] at h
    rw [map_add, h, ← add_assoc, ← add_smul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add, hab]
  rw [G.oneVariableSpecializationHomologyEquivOfHomotopy_oneVariableSpecializationHomologyClass R hH
    _ hab' (LinearEquiv.apply_symm_apply _ _).symm]
  refine congrArg (G.oneVariableSpecializationHomologyClass R j) (Subtype.ext ?_)
  -- Reduce the subtype projection, then cancel `H a + H a` in characteristic two.
  dsimp only
  rw [← add_assoc, ← two_smul (MvPolynomial (Fin n) R), CharTwo.two_eq_zero, zero_smul, zero_add,
    hb, LinearEquiv.symm_apply_apply]

end Homotopy

/-! ### Knot grids -/

namespace IsKnot

variable {G} (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2] (i j : Fin n)

local notation "Base" i => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

/-- **Simply blocked knot grid homology does not depend on the blocked column.** The change of
blocked column, with the homotopy `hG.XSmulHomotopy R i j` between `V_i` and `V_j`, as a
coefficient-linear equivalence between the simply blocked homologies blocking the columns `i` and
`j`. -/
noncomputable def simplyBlockedHomologyColumnChangeEquiv :
    (Base i).obj (hG.simplyBlockedHomology R i) ≃ₗ[R] (Base j).obj (hG.simplyBlockedHomology R j) :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy R
    (hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j)

/-- If `V_i • a + ∂⁻ b = 0` and `π_i b` is the cycle `z`, the change of blocked column sends the
class of `z` to the class of `π_j (H a + b)`, for the `X`-marking homotopy `H`. -/
theorem simplyBlockedHomologyColumnChangeEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0)
    (hb : simplyBlockedSpecialization R i b = G.simplyBlockedChainEquiv R i z) :
    hG.simplyBlockedHomologyColumnChangeEquiv R i j
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.oneVariableSpecializationHomologyClass R j
        ⟨(G.simplyBlockedChainEquiv R j).symm
          (simplyBlockedSpecialization R j (hG.XSmulHomotopy R i j a + b)), by
          rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
          exact G.simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero R
            (hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j) hab⟩ :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy_oneVariableSpecializationHomologyClass R _ z
    hab hb

/-- If `V_j • a + ∂⁻ b = 0` and `π_j b` is the cycle `z`, the inverse change of blocked column
sends the class of `z` to the class of `π_i (H a + b)`, for the `X`-marking homotopy `H`. -/
theorem simplyBlockedHomologyColumnChangeEquiv_symm_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R j) {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X j : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0)
    (hb : simplyBlockedSpecialization R j b = G.simplyBlockedChainEquiv R j z) :
    (hG.simplyBlockedHomologyColumnChangeEquiv R i j).symm
        (G.oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        ⟨(G.simplyBlockedChainEquiv R i).symm
          (simplyBlockedSpecialization R i (hG.XSmulHomotopy R i j a + b)), by
          rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
          exact G.simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero R
            ((hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j).trans
              (by rw [add_comm])) hab⟩ :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy_symm_oneVariableSpecializationHomologyClass R
    _ z hab hb

/-- The change of blocked column on knot grid homology has bidegree zero. -/
theorem isHomogeneous_simplyBlockedHomologyColumnChangeEquiv :
    LinearMap.IsHomogeneous (hG.simplyBlockedHomologyColumnChangeEquiv R i j).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  rw [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := (hG.toOddComponentGridDiagram.mem_bigradedHatHomologyPiece_iff R i).mp hy
  -- The lift `b` of the cycle has bidegree `g`, and its boundary is `-V_i • a` for some `a`.
  have hb := (OddComponentGridDiagram.simplyBlockedLift_mem_bigradedChainMinusPiece_iff
    hG.toOddComponentGridDiagram).mpr hz
  obtain ⟨a, ha⟩ := (exact_X_smul_simplyBlockedSpecialization R i
    (-G.unblockedDifferential R (simplyBlockedLift R i (G.simplyBlockedChainEquiv R i z)))).mp (by
      rw [map_neg, simplyBlockedSpecialization_unblockedDifferential,
        simplyBlockedSpecialization_simplyBlockedLift,
        (G.mem_ker_simplyBlockedComplex_d_iff R i z).mp z.property, neg_zero])
  dsimp only at ha
  -- `V_i • a` has bidegree `g - (1, 0)`, so `a` has bidegree `g + (1, 1)`.
  have hadeg : a ∈ hG.toOddComponentGridDiagram.bigradedChainMinusPiece R (g + (1, 1)) := by
    have hg : g + (1, 1) - (2, 1) = g - (1, 0) := by
      ext <;> simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add] <;> omega
    rw [← hG.toOddComponentGridDiagram.X_smul_mem_bigradedChainMinusPiece_iff i, hg, ha]
    exact neg_mem (OddComponentGridDiagram.unblockedDifferential_mem_bigradedChainMinusPiece _ hb)
  rw [LinearEquiv.coe_toLinearMap,
    hG.simplyBlockedHomologyColumnChangeEquiv_oneVariableSpecializationHomologyClass R i j z
      (by rw [ha, neg_add_cancel]) (simplyBlockedSpecialization_simplyBlockedLift R i _), add_zero]
  refine OddComponentGridDiagram.oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece
    _ R j ?_
  rw [LinearEquiv.apply_symm_apply]
  refine hG.toOddComponentGridDiagram.simplyBlockedSpecialization_mem_bigradedChainHatPiece j
    (add_mem ?_ hb)
  simpa only [add_sub_cancel_right] using hG.XSmulHomotopy_mem_bigradedChainMinusPiece i j hadeg

/-- The change of blocked column preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyColumnChangeEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base i).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyColumnChangeEquiv R i j y ∈
        hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.toOddComponentGridDiagram.linearEquiv_mem_bigradedHatHomologyPiece_iff R i
    hG.toOddComponentGridDiagram j _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j)
    g y

/-- The change of blocked column restricted to the homology pieces of bidegree `g`. -/
noncomputable def simplyBlockedHomologyColumnChangePieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g :=
  hG.toOddComponentGridDiagram.bigradedHatHomologyPieceEquiv R i hG.toOddComponentGridDiagram j
    _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j) g

/-- On underlying classes, the piece equivalence is the total change of blocked column. -/
@[simp↓]
theorem coe_simplyBlockedHomologyColumnChangePieceEquiv (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyColumnChangePieceEquiv R i j g y :
        (Base j).obj (hG.simplyBlockedHomology R j)) =
      hG.simplyBlockedHomologyColumnChangeEquiv R i j
        (y : (Base i).obj (hG.simplyBlockedHomology R i)) :=
  hG.toOddComponentGridDiagram.coe_bigradedHatHomologyPieceEquiv_apply R i
    hG.toOddComponentGridDiagram j _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j)
    g y

/-- The inverse piece equivalence is the inverse of the total change of blocked column. -/
@[simp↓]
theorem coe_simplyBlockedHomologyColumnChangePieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :
    ((hG.simplyBlockedHomologyColumnChangePieceEquiv R i j g).symm y :
        (Base i).obj (hG.simplyBlockedHomology R i)) =
      (hG.simplyBlockedHomologyColumnChangeEquiv R i j).symm
        (y : (Base j).obj (hG.simplyBlockedHomology R j)) :=
  hG.toOddComponentGridDiagram.coe_bigradedHatHomologyPieceEquiv_symm_apply R i
    hG.toOddComponentGridDiagram j _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j)
    g y

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- **Independence of the blocked column.** Over a field of characteristic two, the bigraded
Poincaré series of the simply blocked homology `G-hat` of a knot grid is the same for every choice
of the blocked column. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_columnChange :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K j := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyColumnChangePieceEquiv K i j g).finrank_eq

/-- Over a field of characteristic two, the Alexander-graded Euler characteristic of the simply
blocked homology `G-hat` of a knot grid is the same for every choice of the blocked column. -/
theorem gradedSimplyBlockedHomologyEulerChar_columnChange :
    hG.gradedSimplyBlockedHomologyEulerChar K i = hG.gradedSimplyBlockedHomologyEulerChar K j := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_columnChange i j K]

end Field

end IsKnot

end TauCeti.GridDiagram
