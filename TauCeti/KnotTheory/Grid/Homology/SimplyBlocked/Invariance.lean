/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.ColumnChange
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Transpose
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Bigraded

import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Invariance of the bigraded simply blocked grid homology `G-hat` under grid moves

The simply blocked grid homology `G-hat` of a knot grid `G`, blocking the `O`-marking of column `i`,
is the homology of the specialization of the unblocked complex at `V_i = 0`. Viewed as a module
over the coefficient ring `R` (restricting scalars along the constant polynomials), it carries the
internal `(O-Maslov, Alexander)` bigrading `OddComponentGridDiagram.bigradedHatHomologyGrading`.
Two knot grids, with chosen blocked columns, have isomorphic `G-hat` as bigraded `R`-modules
(`GridDiagram.IsKnot.BigradedSimplyBlockedHomologyIsomorphic`) when some `R`-linear equivalence
between the two homologies maps each bigraded piece into the piece of the same bidegree. This
relation is reflexive, symmetric and transitive.

On a single knot grid the blocked column does not matter
(`GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv`), so the relation for one choice of
blocked columns gives it for every choice
(`GridDiagram.IsKnot.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked`). The cyclic
permutations, the column commutations (through the pentagon map), the diagonal reflection and the
south-west and north-east corner `X`-stabilizations have specified comparison equivalences on
`G-hat` that preserve the bigrading. Row commutations reduce to column commutations through the
diagonal reflection, and every stabilization reduces to the two corner `X`-stabilizations up to
cyclic permutations and commutations (`GridDiagram.IsStabilization.exists_commutationMovesTo`).
Hence knot grids connected by grid moves have isomorphic `G-hat` as bigraded `R`-modules, for every
choice of the blocked columns and every commutative ring `R` of characteristic two
(`GridDiagram.IsKnot.bigradedSimplyBlockedHomologyIsomorphic_of_movesTo`). Over a field this
makes the bigraded Poincaré series and the Alexander-graded Euler characteristic of `G-hat`
grid-move invariants.

The statement concerns the isomorphism class of the bigraded module: the maps attached to
different move sequences are not compared.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.BigradedSimplyBlockedHomologyIsomorphic`: `G-hat` of two knot grids,
  with chosen blocked columns, are isomorphic as `(O-Maslov, Alexander)`-bigraded modules over the
  coefficient ring.

## Main results

* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyIsomorphic_of_isMove`: each elementary
  grid move, including a destabilization, preserves the bigraded `G-hat`.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyIsomorphic_of_movesTo`: **invariance of
  the bigraded `G-hat`**, knot grids connected by grid moves have isomorphic `G-hat` as bigraded
  modules, for any choice of the blocked `O`-markings.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo`: over a
  field of characteristic two, the bigraded Poincaré series of `G-hat` is a grid-move invariant.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Theorem 5.3.1 (invariance of the
bigraded `G-hat` of a knot) with Corollary 4.6.17 (independence of the blocked marking), and the
commutation and stabilization comparisons of Sections 5.1 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3
(arXiv:math/0610559). The unblocked counterpart is
`TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`.
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram.IsKnot

/-! ### The relation -/

section Relation

variable {n m l : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram l}
  (hG : G.IsKnot) (i : Fin n) (hG' : G'.IsKnot) (i' : Fin m) (hG'' : G''.IsKnot) (i'' : Fin l)
  (R : Type*) [CommRing R] [CharP R 2]

/-- The simply blocked grid homologies `G-hat` of two knot grids, blocking the columns `i` and `i'`,
are **isomorphic as bigraded `R`-modules**: some `R`-linear equivalence between them maps each
`(O-Maslov, Alexander)` piece into the piece of the same bidegree. The two grids may have
different sizes, and the coefficient action is restriction of the polynomial action along the
constant polynomials. -/
def BigradedSimplyBlockedHomologyIsomorphic : Prop :=
  ∃ e : (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ i'} R)).obj
        (hG'.simplyBlockedHomology R i'),
    LinearMap.IsHomogeneous e.toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG'.toOddComponentGridDiagram.bigradedHatHomologyGrading R i').piece 0

/-- Every knot grid has `G-hat` isomorphic to itself as a bigraded module. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.refl :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG i R :=
  ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG i hG' i' hG'' i'' R}

/-- Unfold `BigradedSimplyBlockedHomologyIsomorphic` to the existence of a bigraded
equivalence. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_def :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R ↔
      ∃ e : (ModuleCat.restrictScalars
            (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
            (hG.simplyBlockedHomology R i) ≃ₗ[R]
          (ModuleCat.restrictScalars
            (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ i'} R)).obj
            (hG'.simplyBlockedHomology R i'),
        LinearMap.IsHomogeneous e.toLinearMap
          (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
          (hG'.toOddComponentGridDiagram.bigradedHatHomologyGrading R i').piece 0 :=
  Iff.rfl

/-- Isomorphism of bigraded `G-hat` is symmetric: since both bigradings are internal direct sum
decompositions, the inverse of a bigraded equivalence is bigraded. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.symm
    (h : hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R) :
    hG'.BigradedSimplyBlockedHomologyIsomorphic i' hG i R := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of bigraded `G-hat` is transitive: bigraded equivalences compose. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.trans
    (h : hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R)
    (h' : hG'.BigradedSimplyBlockedHomologyIsomorphic i' hG'' i'' R) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG'' i'' R := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Isomorphism of bigraded `G-hat` holds in one direction exactly when it holds in the other. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_comm :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R ↔
      hG'.BigradedSimplyBlockedHomologyIsomorphic i' hG i R :=
  ⟨.symm, .symm⟩

/-- A bijection between the simply blocked homologies of two knot grids makes them isomorphic as
bigraded modules if it maps each `(O-Maslov, Alexander)` piece into the piece of the same
bidegree and is semilinear along a ring homomorphism `σ` of the surviving polynomial rings that
fixes the constants, such as a renaming of the surviving variables. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.of_semilinearMap
    {σ : MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin m // c ≠ i'} R}
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r)
    (f : hG.simplyBlockedHomology R i →ₛₗ[σ] hG'.simplyBlockedHomology R i')
    (hf : Function.Bijective f)
    (hg : ∀ g y, y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g →
      f y ∈ hG'.toOddComponentGridDiagram.bigradedHatHomologyPiece R i' g) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R := by
  refine ⟨ModuleCat.restrictScalarsLinearEquivOfBijective _ _ f hσ hf,
    LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_⟩
  rw [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
  rw [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
    ModuleCat.restrictScalarsLinearEquivOfBijective_apply]
  exact hg g y hy

end Relation

/-! ### The elementary moves -/

section Moves

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- **`G-hat` does not depend on the blocked column.** For a knot grid, the simply blocked
homologies blocking any two columns are isomorphic as bigraded modules. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_columnChange (i j : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG j R :=
  ⟨hG.simplyBlockedHomologyColumnChangeEquiv R i j,
    hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j⟩

/-- The relation between the bigraded `G-hat` of two knot grids does not depend on the blocked
columns. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_congr_blocked {m : ℕ} {G' : GridDiagram m}
    {hG' : G'.IsKnot} (i j : Fin n) (i' j' : Fin m) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R ↔
      hG.BigradedSimplyBlockedHomologyIsomorphic j hG' j' R :=
  ⟨fun h ↦ (hG.bigradedSimplyBlockedHomologyIsomorphic_columnChange R j i).trans
      (h.trans (hG'.bigradedSimplyBlockedHomologyIsomorphic_columnChange R i' j')),
    fun h ↦ (hG.bigradedSimplyBlockedHomologyIsomorphic_columnChange R i j).trans
      (h.trans (hG'.bigradedSimplyBlockedHomologyIsomorphic_columnChange R j' i'))⟩

/-- **Cyclic permutation of the rows preserves the bigraded `G-hat`** of a knot grid, keeping the
blocked column. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_relabelRows_finRotate (i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i
      ((G.isKnot_relabelRows (finRotate n)).mpr hG) i R :=
  .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv R i).toLinearMap
    (hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv R i).bijective fun _ _ hy ↦
      (hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff R i).mpr
        hy

/-- **Cyclic permutation of the columns preserves the bigraded `G-hat`** of a knot grid, moving the
blocked column `i` to `finRotate n i`. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_relabelColumns_finRotate (i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i
      ((G.isKnot_relabelColumns (finRotate n)).mpr hG) (finRotate n i) R :=
  .of_semilinearMap (simplyBlockedRenameEquiv R (finRotate n) i).commutes
    (hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv R i).toLinearMap
    (hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv R i).bijective fun _ _ hy ↦
      (hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff R
        i).mpr hy

/-- **Diagonal reflection preserves the bigraded `G-hat`** of a knot grid, moving the blocked column
`i` to `G.O i`. The reflection is not a grid move; it reduces row commutations to column
commutations. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_transpose (i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i (G.isKnot_transpose.mpr hG) (G.O i) R :=
  .of_semilinearMap (simplyBlockedRenameEquiv R G.O.toPerm i).commutes
    (hG.simplyBlockedHomologyTransposeEquiv R i).toLinearMap
    (hG.simplyBlockedHomologyTransposeEquiv R i).bijective fun _ _ hy ↦
      (hG.simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece_iff R i).mpr hy

/-- **The bigraded `G-hat` is invariant under column commutation.** The commuted diagram of a knot
grid along validated column-commutation data, with the blocked column transported by the column
transposition, has `G-hat` isomorphic to that of the original as a bigraded module. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G)
    (i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i (C.isColumnCommutation.isKnot_iff.mpr hG)
      (Equiv.swap C.column (finRotate n C.column) i) R :=
  ⟨hG.simplyBlockedHomologyCommutationCoefficientEquiv R C i,
    hG.isHomogeneous_simplyBlockedHomologyCommutationCoefficientEquiv R C i⟩

/-- **The bigraded `G-hat` is invariant under the south-west corner `X`-stabilization**, the
stabilization of a knot grid splitting the `X`-marking of column `s` with its new `O`-marking in
the south-west corner of the new block; the blocked column `i` is transported to
`s.castSucc.succAbove i`. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_stabilizeX (s i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) (s.castSucc.succAbove i) R :=
  .symm ⟨G.oneVariableSpecializationStabilizeXHomologyEquiv s i R,
    hG.toOddComponentGridDiagram.isHomogeneous_oneVariableSpecializationStabilizeXHomologyEquiv
      s i R⟩

/-- **The bigraded `G-hat` is invariant under the north-east corner `X`-stabilization**, whose new
`O`-marking is the north-east corner of the new block; the blocked column `i` is transported to
`s.succ.succAbove i`. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_stabilizeX_succ (s i : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) (s.succ.succAbove i) R :=
  .symm ⟨G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R,
    hG.toOddComponentGridDiagram.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv
      s i R⟩

/-- **The bigraded `G-hat` is invariant under elementary column commutations**, for any choice of
the blocked columns. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_isColumnCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsColumnCommutation G G') (i i' : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact (hG.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R _ i _ i').mp
    (hG.bigradedSimplyBlockedHomologyIsomorphic_swapColumns R C i)

/-- **The bigraded `G-hat` is invariant under elementary commutations**, for any choice of the
blocked columns. A row commutation is a column commutation of the diagonal reflections. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_isCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsCommutation G G') (i i' : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (hG.bigradedSimplyBlockedHomologyIsomorphic_transpose R i).trans
      ((bigradedSimplyBlockedHomologyIsomorphic_of_isColumnCommutation _ R _
        ((isColumnCommutation_transpose G G').mpr h) _ _).trans
        (hG'.bigradedSimplyBlockedHomologyIsomorphic_transpose R i').symm)
  · exact hG.bigradedSimplyBlockedHomologyIsomorphic_of_isColumnCommutation R hG' h i i'

end Moves

/-! ### Move sequences -/

section MovesTo

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- Cyclic permutations and commutations preserve the bigraded `G-hat` along every size-preserving
sequence, for any choice of the blocked columns. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n}
    (hH : H.IsKnot) (h : G.CommutationMovesTo H) (i i' : Fin n) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hH i' R := by
  refine (hG.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R i i i i').mp ?_
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot) (j : Fin n),
      hA.BigradedSimplyBlockedHomologyIsomorphic j hB j R)
    (fun _ hA _ j ↦ hA.bigradedSimplyBlockedHomologyIsomorphic_relabelRows_finRotate R j)
    (fun _ hA _ j ↦ (hA.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R j j _ j).mp
      (hA.bigradedSimplyBlockedHomologyIsomorphic_relabelColumns_finRotate R j))
    (fun h hA hB j ↦ hA.bigradedSimplyBlockedHomologyIsomorphic_of_isCommutation R hB h j j)
    (fun _ hA _ j ↦ .refl hA j R)
    (fun _ ih hA hB j ↦ (ih hB hA j).symm)
    (fun h _ ih ih' hA hB j ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA) j).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB j)) hG hH i

/-- Every elementary stabilization, of either marking and in any corner, preserves the bigraded
`G-hat`, for any choice of the blocked columns. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)}
    (hH : H.IsKnot) (h : G.IsStabilization H) (i : Fin n) (i' : Fin (n + 1)) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hH i' R := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.bigradedSimplyBlockedHomologyIsomorphic_stabilizeX R s i).trans
      (bigradedSimplyBlockedHomologyIsomorphic_of_commutationMovesTo _ R hH hs.symm _ i')
  · exact (hG.bigradedSimplyBlockedHomologyIsomorphic_stabilizeX_succ R s i).trans
      (bigradedSimplyBlockedHomologyIsomorphic_of_commutationMovesTo _ R hH hs.symm _ i')

/-- Each elementary grid move, including a destabilization, preserves `G-hat` as a bigraded module,
for any choice of the blocked columns. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) (i : Fin n) (i' : Fin m) :
    hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact (hG.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R i i i i').mp
        (hG.bigradedSimplyBlockedHomologyIsomorphic_relabelRows_finRotate R i)
    · exact (hG'.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R i' i' i' i).mp
        (hG'.bigradedSimplyBlockedHomologyIsomorphic_relabelRows_finRotate R i') |>.symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact (hG.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R i i _ i').mp
        (hG.bigradedSimplyBlockedHomologyIsomorphic_relabelColumns_finRotate R i)
    · exact (hG'.bigradedSimplyBlockedHomologyIsomorphic_congr_blocked R i' i' _ i).mp
        (hG'.bigradedSimplyBlockedHomologyIsomorphic_relabelColumns_finRotate R i') |>.symm
  | commutation h => exact hG.bigradedSimplyBlockedHomologyIsomorphic_of_isCommutation R hG' h i i'
  | stabilization h =>
    exact hG.bigradedSimplyBlockedHomologyIsomorphic_of_isStabilization R hG' h i i'
  | destabilization h =>
    exact (hG'.bigradedSimplyBlockedHomologyIsomorphic_of_isStabilization R hG
      ((isDestabilization_iff_isStabilization _ _).mp h) i' i).symm

/-- **Invariance of the bigraded `G-hat` under grid moves.** Knot grid diagrams connected by
arbitrary grid moves have isomorphic simply blocked grid homologies as
`(O-Maslov, Alexander)`-bigraded `R`-modules, for any choice of the blocked `O`-markings. -/
theorem bigradedSimplyBlockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G')
    (i : Fin n) (i' : Fin m) : hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' R := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot) (j : Fin A.1) (j' : Fin B.1),
      hA.BigradedSimplyBlockedHomologyIsomorphic j hB j' R)
    (fun h hA hB j j' ↦ hA.bigradedSimplyBlockedHomologyIsomorphic_of_isMove R hB h j j')
    (fun _ hA _ j j' ↦ (hA.bigradedSimplyBlockedHomologyIsomorphic_columnChange R j j'))
    (fun _ ih hA hB j j' ↦ (ih hB hA j' j).symm)
    (fun h _ ih ih' hA hB j j' ↦
      -- A knot grid has positive size, so the intermediate grid has a column to block.
      have hM := h.isKnot_iff.mpr hA
      (ih hA hM j ⟨0, Nat.pos_of_ne_zero hM.ne_zero⟩).trans (ih' hM hB _ j'))
    hG hG' i i'

end MovesTo

/-! ### Poincaré series and Euler characteristic -/

section Field

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {hG : G.IsKnot} {hG' : G'.IsKnot}
  {i : Fin n} {i' : Fin m} {K : Type*} [Field K] [CharP K 2]

/-- Knot grids with isomorphic bigraded `G-hat` have the same bigraded Poincaré series. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.bigradedSimplyBlockedHomologyPoincareSeries_eq
    (h : hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' K) :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG'.bigradedSimplyBlockedHomologyPoincareSeries K i' := by
  obtain ⟨e, he⟩ := h
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.toOddComponentGridDiagram.bigradedHatHomologyPieceEquiv K i
    hG'.toOddComponentGridDiagram i' e he g).finrank_eq

/-- Knot grids with isomorphic bigraded `G-hat` have the same Alexander-graded Euler
characteristic. -/
theorem BigradedSimplyBlockedHomologyIsomorphic.gradedSimplyBlockedHomologyEulerChar_eq
    (h : hG.BigradedSimplyBlockedHomologyIsomorphic i hG' i' K) :
    hG.gradedSimplyBlockedHomologyEulerChar K i =
      hG'.gradedSimplyBlockedHomologyEulerChar K i' := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    h.bigradedSimplyBlockedHomologyPoincareSeries_eq]

variable (hG i i' K)

/-- **The bigraded Poincaré series of `G-hat` is a grid-move invariant**: over a field of
characteristic two, knot grids connected by grid moves have the same bigraded Poincaré series of
`G-hat`, for any choice of the blocked columns. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo (h : G.MovesTo G') :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      (h.isKnot_iff.mpr hG).bigradedSimplyBlockedHomologyPoincareSeries K i' :=
  (hG.bigradedSimplyBlockedHomologyIsomorphic_of_movesTo K _ h i
    i').bigradedSimplyBlockedHomologyPoincareSeries_eq

/-- **The Alexander-graded Euler characteristic of `G-hat` is a grid-move invariant**: over a field
of characteristic two, knot grids connected by grid moves have the same graded Euler
characteristic of `G-hat`, for any choice of the blocked columns. -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_of_movesTo (h : G.MovesTo G') :
    hG.gradedSimplyBlockedHomologyEulerChar K i =
      (h.isKnot_iff.mpr hG).gradedSimplyBlockedHomologyEulerChar K i' :=
  (hG.bigradedSimplyBlockedHomologyIsomorphic_of_movesTo K _ h i
    i').gradedSimplyBlockedHomologyEulerChar_eq

end Field

end TauCeti.GridDiagram.IsKnot
