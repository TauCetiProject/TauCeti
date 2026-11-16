/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basepoint
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Transpose
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Bigraded

/-!
# Invariance of bigraded simply blocked grid homology under grid moves

For knot grid diagrams over a commutative ring `R` of characteristic two,
`GridDiagram.IsKnot.SimplyBlockedHomologyIsomorphic` states that their simply blocked grid
homologies `G-hat` are isomorphic as `(O-Maslov, Alexander)`-bigraded `R`-modules via an `R`-linear
equivalence of bidegree `(0, 0)`.

We prove invariance under basepoint changes (`simplyBlockedHomologyIsomorphic_self`), cyclic
permutations, `transpose`, `rotate`, column and row commutations, corner and general stabilizations
and destabilizations (`simplyBlockedHomologyIsomorphic_of_isMove`), and arbitrary move sequences
(`simplyBlockedHomologyIsomorphic_of_movesTo`). Over a field of characteristic two, the bigraded
Poincaré series (`bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo`) and Alexander-graded
Euler characteristic (`gradedSimplyBlockedHomologyEulerChar_eq_of_movesTo`) are grid-move
invariants; naturality across distinct move sequences is not addressed here.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6, 5.1, and 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Geom. Topol. 11
  (2007), Section 3 (arXiv:math/0610559).
-/

public section

noncomputable section

open CategoryTheory

local notation "Base(" R ", " n ", " i ")" =>
  ModuleCat.restrictScalars (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

namespace TauCeti.GridDiagram.IsKnot

section Relation

variable {n m k : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram k}
  (hG : G.IsKnot) (hG' : G'.IsKnot) (hG'' : G''.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2]

/-- Two knot grid diagrams `G` (blocking column `i`) and `G'` (blocking column `j`) have isomorphic
bigraded simply blocked grid homology over `R` if there is an `R`-linear equivalence between their
restricted-scalar homologies that is homogeneous of `(O-Maslov, Alexander)` bidegree `(0, 0)`. -/
def SimplyBlockedHomologyIsomorphic (i : Fin n) (j : Fin m) : Prop :=
  ∃ e : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (Base(R, m, j)).obj (hG'.simplyBlockedHomology R j),
    LinearMap.IsHomogeneous e.toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG'.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0

/-- Every knot grid with a chosen blocked column has `G-hat` isomorphic to itself. -/
theorem SimplyBlockedHomologyIsomorphic.refl (i : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic hG R i i :=
  ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG hG' hG'' R}

/-- Unfold `SimplyBlockedHomologyIsomorphic` to a bidegree-`(0, 0)` `R`-linear equivalence. -/
theorem simplyBlockedHomologyIsomorphic_def {i : Fin n} {j : Fin m} :
    hG.SimplyBlockedHomologyIsomorphic hG' R i j ↔
      ∃ e : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
          (Base(R, m, j)).obj (hG'.simplyBlockedHomology R j),
        LinearMap.IsHomogeneous e.toLinearMap
          (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
          (hG'.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0 := Iff.rfl

/-- Isomorphism of bigraded `G-hat` is symmetric. -/
theorem SimplyBlockedHomologyIsomorphic.symm {i : Fin n} {j : Fin m}
    (h : hG.SimplyBlockedHomologyIsomorphic hG' R i j) :
    hG'.SimplyBlockedHomologyIsomorphic hG R j i :=
  let ⟨e, he⟩ := h; ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of bigraded `G-hat` is transitive. -/
theorem SimplyBlockedHomologyIsomorphic.trans {i : Fin n} {j : Fin m} {l : Fin k}
    (h : hG.SimplyBlockedHomologyIsomorphic hG' R i j)
    (h' : hG'.SimplyBlockedHomologyIsomorphic hG'' R j l) :
    hG.SimplyBlockedHomologyIsomorphic hG'' R i l :=
  let ⟨e, he⟩ := h; let ⟨e', he'⟩ := h'
  ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Symmetry of `SimplyBlockedHomologyIsomorphic` as an equivalence. -/
theorem simplyBlockedHomologyIsomorphic_comm {i : Fin n} {j : Fin m} :
    hG.SimplyBlockedHomologyIsomorphic hG' R i j ↔
      hG'.SimplyBlockedHomologyIsomorphic hG R j i := ⟨.symm, .symm⟩

/-- Isomorphic bigraded simply blocked homologies have `R`-linearly equivalent homogeneous pieces in
every bidegree `g`. -/
theorem SimplyBlockedHomologyIsomorphic.nonempty_piece_linearEquiv {i : Fin n} {j : Fin m}
    (h : hG.SimplyBlockedHomologyIsomorphic hG' R i j) (g : ℤ × ℤ) :
    Nonempty (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      hG'.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :=
  let ⟨e, he⟩ := h
  ⟨e.ofSubmodules _ _ (Submodule.ext fun _ => (Submodule.mem_map_equiv _).trans
    ⟨fun hy => by
      rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
      simpa only [add_zero, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he.map_mem hy,
     fun hy => by
      rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
      simpa only [add_zero, LinearEquiv.coe_coe] using he.linearEquiv_symm.map_mem hy⟩)⟩

/-- Isomorphic bigraded simply blocked homologies have equal `R`-finrank in every bidegree `g`. -/
theorem SimplyBlockedHomologyIsomorphic.finrank_bigradedHatHomologyPiece_eq {i : Fin n} {j : Fin m}
    (h : hG.SimplyBlockedHomologyIsomorphic hG' R i j) (g : ℤ × ℤ) :
    Module.finrank R (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) =
      Module.finrank R (hG'.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :=
  let ⟨e⟩ := h.nonempty_piece_linearEquiv g; e.finrank_eq

/-- A semilinear equivalence fixing constant polynomials and preserving homogeneous pieces witnesses
`SimplyBlockedHomologyIsomorphic`. -/
theorem SimplyBlockedHomologyIsomorphic.of_semilinearEquiv {i : Fin n} {j : Fin m}
    {σ : MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin m // c ≠ j} R}
    {σ' : MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (hσ : ∀ r : R, σ (MvPolynomial.C r) = MvPolynomial.C r)
    (e : hG.simplyBlockedHomology R i ≃ₛₗ[σ] hG'.simplyBlockedHomology R j)
    (hdeg : ∀ ⦃g : ℤ × ℤ⦄ ⦃y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)⦄,
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g →
        e y ∈ hG'.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :
    hG.SimplyBlockedHomologyIsomorphic hG' R i j := by
  let _ : Module R (hG.simplyBlockedHomology R i) :=
    Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
  let _ : Module R (hG'.simplyBlockedHomology R j) :=
    Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
  refine ⟨e.toAddEquiv.toLinearEquiv fun r y => by
      have hy := e.map_smulₛₗ (MvPolynomial.C r) y; rwa [hσ] at hy,
    LinearMap.isHomogeneous_def.mpr fun _ _ hy => by
      simp only [OddComponentGridDiagram.bigradedHatHomologyGrading_piece, add_zero] at hy ⊢
      exact hdeg hy⟩

end Relation

section FieldConsequences

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  {hG : G.IsKnot} {hG' : G'.IsKnot} {K : Type*} [Field K] [CharP K 2] {i : Fin n} {j : Fin m}

/-- Over a field of characteristic two, isomorphic bigraded simply blocked homologies have equal
bigraded Poincaré series. -/
theorem SimplyBlockedHomologyIsomorphic.bigradedSimplyBlockedHomologyPoincareSeries_eq
    (h : hG.SimplyBlockedHomologyIsomorphic hG' K i j) :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG'.bigradedSimplyBlockedHomologyPoincareSeries K j := by
  ext g; simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact h.finrank_bigradedHatHomologyPiece_eq g

/-- Over a field of characteristic two, isomorphic bigraded simply blocked homologies have equal
Alexander-graded Euler characteristics. -/
theorem SimplyBlockedHomologyIsomorphic.gradedSimplyBlockedHomologyEulerChar_eq
    (h : hG.SimplyBlockedHomologyIsomorphic hG' K i j) :
    hG.gradedSimplyBlockedHomologyEulerChar K i =
      hG'.gradedSimplyBlockedHomologyEulerChar K j := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    h.bigradedSimplyBlockedHomologyPoincareSeries_eq]

end FieldConsequences

section Moves

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

private def firstColumn {k : ℕ} {H : GridDiagram k} (hH : H.IsKnot) : Fin k :=
  ⟨0, Nat.pos_of_ne_zero hH.ne_zero⟩

/-- **Basepoint independence of bigraded `G-hat`.** On a knot grid, any two choices of blocked
column produce isomorphic bigraded simply blocked homologies. -/
theorem simplyBlockedHomologyIsomorphic_self (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic hG R i j :=
  ⟨hG.simplyBlockedHomologyBasepointEquiv R i j,
    hG.isHomogeneous_simplyBlockedHomologyBasepointEquiv R i j⟩

variable {hG R} in
/-- If bigraded `G-hat` is isomorphic for some pair of blocked columns, it is isomorphic for any
pair. -/
theorem SimplyBlockedHomologyIsomorphic.change_basepoints {hG' : G'.IsKnot}
    {i₀ : Fin n} {j₀ : Fin m}
    (h : hG.SimplyBlockedHomologyIsomorphic hG' R i₀ j₀) (i : Fin n) (j : Fin m) :
    hG.SimplyBlockedHomologyIsomorphic hG' R i j :=
  (hG.simplyBlockedHomologyIsomorphic_self R i i₀).trans
    (h.trans (hG'.simplyBlockedHomologyIsomorphic_self R j₀ j))

variable {hG} in
/-- Equal knot grids have isomorphic bigraded `G-hat` for any choices of blocked columns. -/
theorem simplyBlockedHomologyIsomorphic_of_eq {G₁ : GridDiagram n} {hG₁ : G₁.IsKnot}
    (h : G = G₁) (i j : Fin n) : hG.SimplyBlockedHomologyIsomorphic hG₁ R i j := by
  subst h; exact hG.simplyBlockedHomologyIsomorphic_self R i j

/-- Cyclic permutation of the rows preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_relabelRows_finRotate (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) R i j :=
  (SimplyBlockedHomologyIsomorphic.of_semilinearEquiv (fun _ => rfl)
    (hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv R i) fun {_ _} =>
      (hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff
        R i).mpr).change_basepoints i j

/-- Cyclic permutation of the columns preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_relabelColumns_finRotate (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) R i j :=
  (SimplyBlockedHomologyIsomorphic.of_semilinearEquiv
    (simplyBlockedRenameEquiv R (finRotate n) i).commutes
    (hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv R i) fun {_ _} =>
      (hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff
        R i).mpr).change_basepoints i j

/-- Diagonal reflection (`transpose`) preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_transpose (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic (G.isKnot_transpose.mpr hG) R i j :=
  (SimplyBlockedHomologyIsomorphic.of_semilinearEquiv
    (simplyBlockedRenameEquiv R G.O.toPerm i).commutes
    (hG.simplyBlockedHomologyTransposeEquiv R i) fun {_ _} =>
      (hG.simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece_iff
        R i).mpr).change_basepoints i j

/-- The toroidal half-turn (`rotate`) preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_rotate (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic (G.isKnot_rotate.mpr hG) R i j :=
  (SimplyBlockedHomologyIsomorphic.of_semilinearEquiv
    (simplyBlockedRenameEquiv R Fin.revPerm i).commutes
    (hG.simplyBlockedHomologyRotateEquiv R i) fun {_ _} =>
      (hG.simplyBlockedHomologyRotateEquiv_mem_bigradedHatHomologyPiece_iff
        R i).mpr).change_basepoints i j

/-- Validated column commutation preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G) (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic (C.isColumnCommutation.isKnot_iff.mpr hG) R i j :=
  (SimplyBlockedHomologyIsomorphic.of_semilinearEquiv
    (simplyBlockedRenameEquiv R (Equiv.swap C.column (finRotate n C.column)) i).commutes
    (hG.simplyBlockedHomologyCommutationEquiv R C i) fun {_ _} hy =>
      (congrFun (hG.coe_simplyBlockedHomologyCommutationEquiv R C i) _).symm ▸
        hG.simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece R C i hy
  ).change_basepoints i j

/-- Elementary column commutation preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_of_isColumnCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : IsColumnCommutation G H) (i j : Fin n) :
    hG.SimplyBlockedHomologyIsomorphic hH R i j := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact hG.simplyBlockedHomologyIsomorphic_swapColumns R C i j

/-- Every elementary row or column commutation preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_of_isCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : IsCommutation G H) (i j : Fin n) : hG.SimplyBlockedHomologyIsomorphic hH R i j := by
  rcases (isCommutation_iff G H).mp h with h | h
  · exact (hG.simplyBlockedHomologyIsomorphic_transpose R i i).trans
      (((G.isKnot_transpose.mpr hG).simplyBlockedHomologyIsomorphic_of_isColumnCommutation R
        (H.isKnot_transpose.mpr hH) ((isColumnCommutation_transpose G H).mpr h) i j).trans
        (hH.simplyBlockedHomologyIsomorphic_transpose R j j).symm)
  · exact hG.simplyBlockedHomologyIsomorphic_of_isColumnCommutation R hH h i j

/-- Any sequence of cyclic permutations and commutations preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.CommutationMovesTo H) (i j : Fin n) : hG.SimplyBlockedHomologyIsomorphic hH R i j :=
  h.induction_on
    (motive := fun A B => ∀ (hA : A.IsKnot) (hB : B.IsKnot) (a b : Fin n),
      hA.SimplyBlockedHomologyIsomorphic hB R a b)
    (fun _ hA _ a b => hA.simplyBlockedHomologyIsomorphic_relabelRows_finRotate R a b)
    (fun _ hA _ a b => hA.simplyBlockedHomologyIsomorphic_relabelColumns_finRotate R a b)
    (fun h hA hB a b => hA.simplyBlockedHomologyIsomorphic_of_isCommutation R hB h a b)
    (fun _ hA _ a b => hA.simplyBlockedHomologyIsomorphic_self R a b)
    (fun _ ih hA hB a b => (ih hB hA b a).symm)
    (fun h _ ih ih' hA hC a c =>
      let hB := h.movesTo.isKnot_iff.mpr hA
      (ih hA hB a (firstColumn hB)).trans (ih' hB hC (firstColumn hB) c)) hG hH i j

/-- South-west corner `X`-stabilization preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_stabilizeX (s : Fin n) (i : Fin n) (j : Fin (n + 1)) :
    hG.SimplyBlockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) R i j := by
  let hG' := (G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG
  refine (?_ : hG'.SimplyBlockedHomologyIsomorphic hG R
    (s.castSucc.succAbove i) i).symm.change_basepoints i j
  have hhom :=
    hG.toOddComponentGridDiagram.isHomogeneous_oneVariableSpecializationStabilizeXHomologyEquiv
      s i R
  -- Unfold semireducible `OddComponentGridDiagram.stabilizeX` so the source grading matches.
  dsimp only [OddComponentGridDiagram.stabilizeX] at hhom
  exact ⟨G.oneVariableSpecializationStabilizeXHomologyEquiv s i R, hhom⟩

/-- North-east corner `X`-stabilization preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_stabilizeX_succ (s : Fin n) (i : Fin n) (j : Fin (n + 1)) :
    hG.SimplyBlockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) R i j :=
  let hrot := G.isKnot_rotate.mpr hG
  let hstab := (G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG
  (hG.simplyBlockedHomologyIsomorphic_rotate R i s).trans
    ((hrot.simplyBlockedHomologyIsomorphic_stabilizeX R s.rev s 0).trans
      ((simplyBlockedHomologyIsomorphic_of_eq R (G.rotate_stabilizeX_succ s).symm 0 0).trans
        (hstab.simplyBlockedHomologyIsomorphic_rotate R j 0).symm))

/-- Every elementary stabilization of either marking and in any corner preserves bigraded
`G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)} (hH : H.IsKnot)
    (h : G.IsStabilization H) (i : Fin n) (j : Fin (n + 1)) :
    hG.SimplyBlockedHomologyIsomorphic hH R i j := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.simplyBlockedHomologyIsomorphic_stabilizeX R s i 0).trans
      (simplyBlockedHomologyIsomorphic_of_commutationMovesTo _ R hH hs.symm 0 j)
  · exact (hG.simplyBlockedHomologyIsomorphic_stabilizeX_succ R s i 0).trans
      (simplyBlockedHomologyIsomorphic_of_commutationMovesTo _ R hH hs.symm 0 j)

/-- Every elementary grid move — cyclic permutation, commutation, stabilization, or
destabilization — preserves bigraded `G-hat`. -/
theorem simplyBlockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) (i : Fin n) (j : Fin m) :
    hG.SimplyBlockedHomologyIsomorphic hG' R i j := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact hG.simplyBlockedHomologyIsomorphic_relabelRows_finRotate R i j
    · exact (hG'.simplyBlockedHomologyIsomorphic_relabelRows_finRotate R j i).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact hG.simplyBlockedHomologyIsomorphic_relabelColumns_finRotate R i j
    · exact (hG'.simplyBlockedHomologyIsomorphic_relabelColumns_finRotate R j i).symm
  | commutation h => exact hG.simplyBlockedHomologyIsomorphic_of_isCommutation R hG' h i j
  | stabilization h => exact hG.simplyBlockedHomologyIsomorphic_of_isStabilization R hG' h i j
  | destabilization h =>
    exact (hG'.simplyBlockedHomologyIsomorphic_of_isStabilization R hG
      ((isDestabilization_iff_isStabilization _ _).mp h) j i).symm

/-- **Invariance of bigraded `G-hat` under grid moves.** Knot grid diagrams connected by arbitrary
sequences of grid moves have isomorphic bigraded simply blocked grid homologies over `R`, for any
choices of blocked columns `i` and `j`. -/
theorem simplyBlockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G')
    (i : Fin n) (j : Fin m) : hG.SimplyBlockedHomologyIsomorphic hG' R i j :=
  h.induction_on
    (motive := fun A B => ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot) (a : Fin A.1) (b : Fin B.1),
      hA.SimplyBlockedHomologyIsomorphic hB R a b)
    (fun h hA hB a b => hA.simplyBlockedHomologyIsomorphic_of_isMove R hB h a b)
    (fun _ hA _ a b => hA.simplyBlockedHomologyIsomorphic_self R a b)
    (fun _ ih hA hB a b => (ih hB hA b a).symm)
    (fun h _ ih ih' hA hC a c =>
      let hB := h.isKnot_iff.mpr hA
      (ih hA hB a (firstColumn hB)).trans (ih' hB hC (firstColumn hB) c)) hG hG' i j

end Moves

section FieldMoves

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  (hG : G.IsKnot) (K : Type*) [Field K] [CharP K 2]

/-- **Grid-move invariance of the bigraded Poincaré series of `G-hat`.** -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo (hG' : G'.IsKnot)
    (h : G.MovesTo G') (i : Fin n) (j : Fin m) :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG'.bigradedSimplyBlockedHomologyPoincareSeries K j :=
  (hG.simplyBlockedHomologyIsomorphic_of_movesTo K hG' h i j
    ).bigradedSimplyBlockedHomologyPoincareSeries_eq

/-- **Grid-move invariance of the Alexander-graded Euler characteristic of `G-hat`.** -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_of_movesTo (hG' : G'.IsKnot)
    (h : G.MovesTo G') (i : Fin n) (j : Fin m) :
    hG.gradedSimplyBlockedHomologyEulerChar K i =
      hG'.gradedSimplyBlockedHomologyEulerChar K j :=
  (hG.simplyBlockedHomologyIsomorphic_of_movesTo K hG' h i j
    ).gradedSimplyBlockedHomologyEulerChar_eq

end FieldMoves

end TauCeti.GridDiagram.IsKnot
