/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.Bigraded
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading

/-!
# Invariance of the bigraded `K[U]`-module `GH⁻` under grid moves

The unblocked grid homology `GH⁻` of a knot grid carries two gradings, the `O`-Maslov grading and
the Alexander grading (`OddComponentGridDiagram.bigradedUnblockedHomologyGrading`), and the action
of `U` lowers them by `(2, 1)`. Two knot grids, possibly of different sizes, have isomorphic `GH⁻`
as bigraded `K[U]`-modules when some `K[U]`-linear equivalence between their homologies maps each
bigraded piece into the piece of the same bidegree
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`). This relation is reflexive,
symmetric and transitive; its inverse direction uses that both bigradings are internal direct sum
decompositions.

Each elementary move has a specified comparison map on `GH⁻` that preserves both gradings: the
cyclic permutations, the diagonal reflection, the pentagon map of a column commutation, and the
comparisons of the south-west and the north-east corner `X`-stabilizations. Since every
stabilization type reduces to these two corners up to cyclic permutations and commutations
(`GridDiagram.IsStabilization.exists_commutationMovesTo`), knot grids connected by grid moves
have isomorphic `GH⁻` as bigraded `K[U]`-modules
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`), over every commutative ring
`K` of characteristic two. It concerns the isomorphism class of the bigraded module: the maps
attached to different move sequences are not compared.

Forgetting the Maslov grading gives the Alexander-graded relation
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`), because the
Alexander grading of `GH⁻` is the coarsening of the bigrading
(`OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd`). This is how the
invariance of the Alexander-graded `GH⁻` and of `τ` is derived in `Homology/Invariance.lean`.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`: `GH⁻` of two knot grids are
  isomorphic as `(O-Maslov, Alexander)`-bigraded `K[U]`-modules.

## Main results

* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.of_semilinearMap`: a bijective
  bigrading-preserving map, semilinear along a ring homomorphism commuting with the evaluation of
  every variable at `U`, witnesses the relation.
* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`:
  the relation implies isomorphism as Alexander-graded `K[U]`-modules.
* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_isMove`: each elementary grid
  move, including a destabilization, preserves `GH⁻` as a bigraded `K[U]`-module.
* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`: **invariance of the
  bigraded `GH⁻`**, knot grids connected by grid moves have isomorphic `GH⁻` as bigraded
  `K[U]`-modules.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Theorem 5.3.1 (invariance of the
bigraded `GH⁻` of a knot), with the commutation and stabilization comparisons of Sections 5.1 and
5.2; Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3
(arXiv:math/0610559).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram.IsKnot

/-! ### Isomorphism of bigraded homologies -/

section Relation

variable {n m l : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram l}
  (hG : G.IsKnot) (hG' : G'.IsKnot) (hG'' : G''.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homologies of two knot grids are **isomorphic as bigraded
`R[U]`-modules**: some `R[U]`-linear equivalence `GH⁻(G) ≃ GH⁻(G')` maps each
`(O-Maslov, Alexander)` piece into the piece of the same bidegree. The two grids may have
different sizes. -/
def BigradedUnblockedHomologyIsomorphic : Prop :=
  letI := hG.unblockedHomologyModule R
  letI := hG'.unblockedHomologyModule R
  ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
    LinearMap.IsHomogeneous e.toLinearMap
      (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
      (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0

/-- Every knot grid has `GH⁻` isomorphic to itself as a bigraded `R[U]`-module. -/
theorem BigradedUnblockedHomologyIsomorphic.refl : hG.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  exact ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG hG' hG'' R}

/-- Unfold `BigradedUnblockedHomologyIsomorphic` to the existence of a bigraded equivalence. -/
theorem bigradedUnblockedHomologyIsomorphic_def :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔
      letI := hG.unblockedHomologyModule R
      letI := hG'.unblockedHomologyModule R
      ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
        LinearMap.IsHomogeneous e.toLinearMap
          (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
          (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0 :=
  Iff.rfl

/-- Equal knot grids have isomorphic bigraded `GH⁻`. This transports the relation along a
propositional equation of diagrams, such as one between two descriptions of a moved diagram. -/
theorem bigradedUnblockedHomologyIsomorphic_of_eq {G₁ : GridDiagram n} {hG₁ : G₁.IsKnot}
    (h : G = G₁) : hG.BigradedUnblockedHomologyIsomorphic hG₁ R := by
  subst h
  exact .refl hG R

/-- Isomorphism of bigraded homologies is symmetric: since both bigradings are internal direct sum
decompositions, the inverse of a bigraded equivalence is bigraded. -/
theorem BigradedUnblockedHomologyIsomorphic.symm
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG'.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of bigraded homologies is transitive: bigraded equivalences compose. -/
theorem BigradedUnblockedHomologyIsomorphic.trans
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R)
    (h' : hG'.BigradedUnblockedHomologyIsomorphic hG'' R) :
    hG.BigradedUnblockedHomologyIsomorphic hG'' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  let _ := hG''.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Isomorphism of bigraded homologies holds in one direction exactly when it holds in the
other. -/
theorem bigradedUnblockedHomologyIsomorphic_comm :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔ hG'.BigradedUnblockedHomologyIsomorphic hG R :=
  ⟨.symm, .symm⟩

/-- A bijection between the unblocked homologies of two knot grids makes them isomorphic as
bigraded `R[U]`-modules if it preserves the `(O-Maslov, Alexander)` bigrading and is semilinear
along a ring homomorphism `σ` of the polynomial rings that commutes with the evaluation
`V_j ↦ U`, such as a renaming of the variables. -/
theorem BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    {σ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin m) R}
    (hσ : ∀ p, aeval (fun _ ↦ (Polynomial.X : Polynomial R)) (σ p) =
      aeval (fun _ ↦ (Polynomial.X : Polynomial R)) p)
    (f : G.unblockedHomology R →ₛₗ[σ] G'.unblockedHomology R) (hf : Function.Bijective f)
    (hg : ∀ g y, y ∈ hG.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g →
      f y ∈ hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g) :
    hG.BigradedUnblockedHomologyIsomorphic hG' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  refine ⟨LinearEquiv.ofBijective (hG.unblockedHomologyLinearMapOfSemilinear hG' R hσ f)
    (by rwa [coe_unblockedHomologyLinearMapOfSemilinear]),
    LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_⟩
  rw [OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece] at hy
  rw [add_zero, OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece,
    LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply, coe_unblockedHomologyLinearMapOfSemilinear]
  exact hg g y hy

/-- Knot grids whose `GH⁻` are isomorphic as bigraded `R[U]`-modules have isomorphic `GH⁻` as
Alexander-graded `R[U]`-modules, since the Alexander grading is the coarsening of the bigrading
along the Alexander degree. -/
theorem BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) : hG.UnblockedHomologyIsomorphic hG' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have := hG.isScalarTower_unblockedHomology (R := R)
  have := hG'.isScalarTower_unblockedHomology (R := R)
  obtain ⟨e, he⟩ := h
  have he' : LinearMap.IsHomogeneous (e.toLinearMap.restrictScalars R)
      (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
      (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦ he.map_mem hy
  have hc := he'.coarsen_zero Prod.snd
  rw [OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd,
    OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd] at hc
  refine unblockedHomologyIsomorphic_def.mpr ⟨e, LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦ ?_⟩
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
  exact hc.map_mem hy

end Relation

/-! ### The elementary moves -/

section Moves

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **Cyclic permutation of the rows preserves the bigraded `GH⁻`** of a knot grid. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) K :=
  .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).bijective fun _ _ hy ↦
      (OddComponentGridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff
        hG.toOddComponentGridDiagram K).mpr hy

/-- **Cyclic permutation of the columns preserves the bigraded `GH⁻`** of a knot grid. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) K :=
  .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).bijective fun _ _ hy ↦
      (OddComponentGridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff
        hG.toOddComponentGridDiagram K).mpr hy

/-- The diagonal reflection of a knot grid preserves the bigraded `GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_transpose :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_transpose).mpr hG) K :=
  .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyTransposeEquiv K).toLinearMap
    (G.unblockedHomologyTransposeEquiv K).bijective fun _ _ hy ↦
      OddComponentGridDiagram.unblockedHomologyTransposeEquiv_mem_bigradedUnblockedHomologyPiece
        hG.toOddComponentGridDiagram K hy

/-- **The bigraded `GH⁻` is invariant under column commutation.** The commuted diagram of a knot
grid along validated column-commutation data has `GH⁻` isomorphic to that of the original as a
bigraded `K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G) :
    hG.BigradedUnblockedHomologyIsomorphic (hG.swapColumns C.column (finRotate n C.column)) K :=
  .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyCommutationMap K C) (G.unblockedHomologyCommutationMap_bijective C K)
    fun _ _ hy ↦
      OddComponentGridDiagram.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece
        hG.toOddComponentGridDiagram K C hy

/-- **The bigraded `GH⁻` is invariant under elementary column commutations.** -/
theorem bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsColumnCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact hG.bigradedUnblockedHomologyIsomorphic_swapColumns K C

/-- **The bigraded `GH⁻` is invariant under elementary commutations.** A row commutation is a
column commutation of the diagonal reflections. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (hG.bigradedUnblockedHomologyIsomorphic_transpose K).trans
      ((bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation _ K _
        ((isColumnCommutation_transpose G G').mpr h)).trans
        (hG'.bigradedUnblockedHomologyIsomorphic_transpose K).symm)
  · exact hG.bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation K hG' h

/-- **The bigraded `GH⁻` is invariant under the south-west corner `X`-stabilization**, the
stabilization of a knot grid splitting the `X`-marking of column `s` with its new `O`-marking in
the south-west corner of the new block. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) K :=
  (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun _ ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXHomologyMap s K) (G.stabilizeXHomologyMap_bijective s K) fun _ _ hy ↦
      hG.toOddComponentGridDiagram.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s K
        hy).symm

/-- **The bigraded `GH⁻` is invariant under the north-east corner `X`-stabilization**, whose new
`O`-marking is the north-east corner of the new block. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX_succ (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) K :=
  (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun _ ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXSuccHomologyMap s K) (G.stabilizeXSuccHomologyMap_bijective s K) fun _ _ hy ↦
      OddComponentGridDiagram.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece
        hG.toOddComponentGridDiagram s K hy).symm

end Moves

/-! ### Move sequences -/

section MovesTo

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- Cyclic permutations and commutations preserve the bigraded `GH⁻` along every size-preserving
sequence. -/
theorem bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n}
    (hH : H.IsKnot) (h : G.CommutationMovesTo H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA)).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB)) hG hH

/-- Every elementary stabilization, of either marking and in any corner, preserves the bigraded
`GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)}
    (hH : H.IsKnot) (h : G.IsStabilization H) : hG.BigradedUnblockedHomologyIsomorphic hH K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX_succ K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move, including a destabilization, preserves `GH⁻` as a bigraded
`K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) : hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K).symm
  | commutation h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hG' h
  | stabilization h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG' h
  | destabilization h =>
    exact (hG'.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- **Invariance of the bigraded `GH⁻` under grid moves.** Knot grid diagrams connected by
arbitrary grid moves have isomorphic unblocked grid homologies as `(O-Maslov, Alexander)`-bigraded
`K[U]`-modules. -/
theorem bigradedUnblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isMove K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

end MovesTo

end TauCeti.GridDiagram.IsKnot
